theory Wire_Code_Admission
  imports Wire_Code_Prechecks
begin

definition code_profile_allows :: "negotiated_wire_profile \<Rightarrow> wire_family \<Rightarrow> nat \<Rightarrow> bool" where
  "code_profile_allows profile family operation \<longleftrightarrow>
    family \<in> negotiated_families profile \<and>
    (negotiated_version profile \<noteq> 5 \<or>
      (family \<in> {Wire_Query,Wire_Heartbeat} \<and> operation \<in> {1,2}))"

definition code_wire_expiry :: "wire_core \<Rightarrow> wire_boundary \<Rightarrow> nat option" where
  "code_wire_expiry core authority =
    (let expiry = wire_sent_seconds core + max (wire_ttl_seconds core) (boundary_asset_ttl_floor authority)
     in if expiry < 2^64 then Some expiry else None)"

lemma source_checked_expiry_is_exactly_the_model_sum_when_representable:
  "code_wire_expiry core authority =
    (if wire_expiry authority core < 2^64 then Some (wire_expiry authority core) else None)"
  by (simp add: code_wire_expiry_def wire_expiry_def effective_wire_ttl_def Let_def)

definition code_check_versioned_scope :: "wire_core \<Rightarrow> wire_boundary \<Rightarrow> nat \<Rightarrow> wire_refusal option" where
  "code_check_versioned_scope core authority version =
    (let profile = boundary_profile authority in
     if negotiated_version profile \<noteq> version \<or> wire_version core \<noteq> version \<or>
        boundary_version_floor authority > version \<or>
        \<not> code_profile_allows profile (wire_message_family core) (wire_opcode (wire_operation_body core)) \<or>
        wire_atomicity core \<notin> negotiated_atomicities profile
     then Some Unsupported_Wire_Version
     else if \<not> current_wire_scope authority core then Some Invalid_Wire_Source
     else case code_wire_expiry core authority of None \<Rightarrow> Some Wire_TTL_Invalid | Some expiry \<Rightarrow>
       if boundary_now authority + boundary_future_skew authority \<ge> 2^64 \<or>
          wire_sent_seconds core > boundary_now authority + boundary_future_skew authority
       then Some Wire_TTL_Invalid
       else if expiry < boundary_now authority then Some Wire_TTL_Expired else None)"

definition code_admit_packet ::
  "(wire_core \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> bool) \<Rightarrow>
    wire_packet \<Rightarrow> wire_boundary \<Rightarrow> wire_refusal option" where
  "code_admit_packet verify packet authority =
    (case code_check_versioned_scope (packet_core packet) authority 6 of Some reason \<Rightarrow> Some reason
     | None \<Rightarrow> let core = packet_core packet in
       if wire_signature_scheme core = 2 then Some Invalid_Wire_Threshold
       else if wire_signature_scheme core \<notin> negotiated_schemes (boundary_profile authority) \<or>
         \<not> verify core (envelope_signing_bytes core) (packet_signature packet)
       then Some Invalid_Wire_Signature else None)"

definition code_decoded_gate ::
  "(wire_core \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> bool) \<Rightarrow>
    (wire_core \<Rightarrow> bool) \<Rightarrow> (negotiated_wire_profile \<Rightarrow> wire_core \<Rightarrow> bool) \<Rightarrow>
    wire_boundary \<Rightarrow> wire_bytes \<Rightarrow> wire_gate_result" where
  "code_decoded_gate verify attest body_allowed authority bytes =
    (if length bytes > boundary_max_frame authority then Gate_Refused Invalid_Wire_Format
     else case decode_wire_packet bytes of None \<Rightarrow> Gate_Refused Invalid_Wire_Format | Some packet \<Rightarrow>
       (case code_admit_packet verify packet authority of Some reason \<Rightarrow> Gate_Refused reason
        | None \<Rightarrow> if \<not> attest (packet_core packet) then Gate_Refused Invalid_Wire_Source
          else if \<not> body_allowed (boundary_profile authority) (packet_core packet)
          then Gate_Refused Invalid_Wire_Format else Gate_Admitted packet))"

theorem the_source_admission_order_matches_the_model_with_threshold_disabled:
  assumes "\<not> boundary_threshold_supported authority"
  shows "code_decoded_gate verify attest body_allowed authority bytes =
    wire_gate verify attest body_allowed authority bytes"
  using assms
  by (auto simp: code_decoded_gate_def code_admit_packet_def code_check_versioned_scope_def
    code_profile_allows_def source_checked_expiry_is_exactly_the_model_sum_when_representable
    wire_gate_def Let_def split: option.splits if_splits)

lemma threshold_two_is_always_a_source_refusal:
  assumes "code_check_versioned_scope (packet_core packet) authority 6 = None"
    "wire_signature_scheme (packet_core packet) = 2"
  shows "code_admit_packet verify packet authority = Some Invalid_Wire_Threshold"
  using assms by (simp add: code_admit_packet_def Let_def)

definition code_library_gate ::
  "(wire_core \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> bool) \<Rightarrow>
    (wire_core \<Rightarrow> bool) \<Rightarrow> (negotiated_wire_profile \<Rightarrow> wire_core \<Rightarrow> bool) \<Rightarrow>
    wire_boundary \<Rightarrow> wire_bytes \<Rightarrow> wire_gate_result" where
  "code_library_gate verify attest body_allowed authority bytes =
    (if negotiated_version (boundary_profile authority) \<noteq> 6 then Gate_Refused Unsupported_Wire_Version
     else case code_check_declared_version bytes (boundary_max_frame authority) of
       Some reason \<Rightarrow> Gate_Refused reason
     | None \<Rightarrow> code_decoded_gate verify attest body_allowed authority bytes)"

lemma prechecked_current_input_reuses_the_model_admission:
  fixes authority :: wire_boundary
  assumes "negotiated_version (boundary_profile authority) = 6"
    "code_check_declared_version bytes (boundary_max_frame authority) = None"
    "\<not> boundary_threshold_supported authority"
  shows "code_library_gate verify attest body_allowed authority bytes =
    wire_gate verify attest body_allowed authority bytes"
proof -
  have same: "code_decoded_gate verify attest body_allowed authority bytes =
      wire_gate verify attest body_allowed authority bytes"
    by (rule the_source_admission_order_matches_the_model_with_threshold_disabled[where authority = authority])
      (rule assms(3))
  show ?thesis using assms(1,2) same by (simp add: code_library_gate_def)
qed

lemma a_noncurrent_library_profile_has_a_documented_error_priority_difference:
  assumes "negotiated_version (boundary_profile authority) \<noteq> 6"
    "length bytes \<le> boundary_max_frame authority" "decode_wire_packet bytes = None"
  shows "code_library_gate verify attest body_allowed authority bytes = Gate_Refused Unsupported_Wire_Version"
    "wire_gate verify attest body_allowed authority bytes = Gate_Refused Invalid_Wire_Format"
  using assms by (simp_all add: code_library_gate_def wire_gate_def)

lemma a_new_declared_version_has_a_documented_predecode_difference:
  assumes "negotiated_version (boundary_profile authority) = 6"
    "length bytes \<le> boundary_max_frame authority"
    "code_declared_version bytes = Some version" "version \<noteq> 6"
    "decode_wire_packet bytes = None"
  shows "code_library_gate verify attest body_allowed authority bytes = Gate_Refused Unsupported_Wire_Version"
    "wire_gate verify attest body_allowed authority bytes = Gate_Refused Invalid_Wire_Format"
  using assms by (simp_all add: code_library_gate_def code_check_declared_version_def wire_gate_def)

definition code_check_delivery_ttl :: "nat option \<Rightarrow> wire_core \<Rightarrow> wire_refusal option" where
  "code_check_delivery_ttl maximum core =
    (case maximum of None \<Rightarrow> None | Some limit \<Rightarrow>
      if wire_ttl_seconds core > limit then Some Wire_TTL_Invalid else None)"

lemma the_default_delivery_ttl_configuration_adds_no_check:
  "code_check_delivery_ttl None core = None"
  by (simp add: code_check_delivery_ttl_def)

lemma an_above_limit_signed_delivery_ttl_is_a_refusal:
  "wire_ttl_seconds core > limit \<Longrightarrow>
    code_check_delivery_ttl (Some limit) core = Some Wire_TTL_Invalid"
  by (simp add: code_check_delivery_ttl_def)

definition code_transport_key :: "wire_core \<Rightarrow> authenticated_message_id" where
  "code_transport_key core =
    (wire_deployment core,wire_source_domain core,wire_principal core,wire_uuid core)"

lemma the_source_transport_key_has_the_exact_authenticated_model_components:
  "code_transport_key core = authenticated_wire_message_id core"
  by (simp add: code_transport_key_def authenticated_wire_message_id_def)

datatype code_arrival = Code_First | Code_Identical | Code_Replay_Conflict

definition code_compare_binding where
  "code_compare_binding retained exact =
    (case retained of None \<Rightarrow> Code_First | Some bytes \<Rightarrow>
      if bytes = exact then Code_Identical else Code_Replay_Conflict)"

lemma a_conflicting_source_binding_cannot_replace_an_earlier_body:
  "prior \<noteq> exact \<Longrightarrow> code_compare_binding (Some prior) exact = Code_Replay_Conflict"
  by (simp add: code_compare_binding_def)

end
