theory Wire_Code_Reference_Admission
  imports Wire_Code_Debit_Recovery "OIP_Reference_Profile.Reference_Wire_Admission"
begin

type_synonym code_checked_reference_input = "wire_packet \<times> wire_boundary \<times> wire_bytes"


type_synonym code_source_selected_boundary = "wire_boundary \<times> wire_bytes \<times> nat"

definition code_source_selected_pair :: "code_source_selected_boundary option \<Rightarrow> (wire_boundary \<times> wire_bytes) option" where
  "code_source_selected_pair selected = map_option (\<lambda>(scope,key,max_nesting). (scope,key)) selected"

definition code_source_selected_nesting :: "code_source_selected_boundary option \<Rightarrow> nat" where
  "code_source_selected_nesting selected =
    (case selected of None \<Rightarrow> 0 | Some (scope,key,max_nesting) \<Rightarrow> max_nesting)"

lemma the_source_boundary_pair_and_depth_are_the_same_selected_record:
  "code_source_selected_pair (Some (scope,key,max_nesting)) = Some (scope,key)"
  "code_source_selected_nesting (Some (scope,key,max_nesting)) = max_nesting"
  by (simp_all add: code_source_selected_pair_def code_source_selected_nesting_def)

lemma a_projected_source_selection_retains_its_exact_depth:
  assumes "code_source_selected_pair selected = Some (scope,key)"
  obtains max_nesting
  where "selected = Some (scope,key,max_nesting)" "code_source_selected_nesting selected = max_nesting"
  using assms by (auto simp: code_source_selected_pair_def code_source_selected_nesting_def
    split: option.splits prod.splits)

definition code_attach_channel_profile :: "negotiated_wire_profile \<Rightarrow> (wire_boundary \<times> wire_bytes) option \<Rightarrow> (wire_boundary \<times> wire_bytes) option" where
  "code_attach_channel_profile profile selected =
    map_option (\<lambda>(scope,key).
      (scope\<lparr>boundary_profile := profile,boundary_threshold_supported := False\<rparr>,key)) selected"

text \<open>
  Source: wire.rs consume, modern branch through check_delivery_ttl.
  Boundary has no profile field in Rust: code_attach_channel_profile is the
  value projection of passing channel.profile beside the selected Boundary.
  selected is the external wire_boundary result; cancelled is the configured
  cancellation provider. Neither parameter decides a codec or scope guard.
  This prefix does not model the later identity, proof, current-scope,
  ordered-observation, product execution or publication checks.
\<close>

definition code_reference_modern_prefix ::
  "nat \<Rightarrow> negotiated_wire_profile \<Rightarrow> code_source_selected_boundary option \<Rightarrow>
    code_channel_guard \<Rightarrow> nat \<Rightarrow> product_cut \<Rightarrow> wire_bytes \<Rightarrow> delivery_window \<Rightarrow>
    bool \<Rightarrow> (wire_core \<Rightarrow> bool) \<Rightarrow>
    (wire_bytes \<Rightarrow> wire_core \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> bool) \<Rightarrow>
    nat option \<Rightarrow> wire_bytes \<Rightarrow> (code_path_refusal + code_checked_reference_input)" where
  "code_reference_modern_prefix frame_limit profile selected channel deployment current_cut
      credential_packet window ordered cancelled verify_key maximum_ttl bytes =
    (if length bytes > frame_limit then Inl (Code_Path_Validation Invalid_Wire_Format)
     else if negotiated_version profile \<noteq> 6 then Inl (Code_Path_Validation Unsupported_Wire_Version)
     else case code_check_declared_version bytes frame_limit of Some reason \<Rightarrow> Inl (Code_Path_Validation reason)
      | None \<Rightarrow> (case decode_wire_packet bytes of None \<Rightarrow> Inl (Code_Path_Validation Invalid_Wire_Format)
       | Some packet \<Rightarrow> let core = packet_core packet in
         case code_check_operation code_reference_accepts core of Some reason \<Rightarrow> Inl (Code_Path_Validation reason)
          | None \<Rightarrow> if \<not> code_matches_signed_packet bytes credential_packet
            then Inl (Code_Path_Validation Invalid_Wire_Signature)
            else case code_boundary_at (code_attach_channel_profile profile (code_source_selected_pair selected)) channel deployment current_cut None False of
              Inl reason \<Rightarrow> Inl reason
            | Inr (scope,key) \<Rightarrow>
               if length bytes > boundary_max_frame scope then Inl (Code_Path_Validation Invalid_Wire_Format)
               else case code_gate_delivery window (boundary_now scope) (\<not> ordered) of Some reason \<Rightarrow> Inl reason
                | None \<Rightarrow> if \<not> ordered \<and> cancelled core then Inl Code_Path_Cancelled
                  else case code_admit_packet (verify_key key) packet scope of Some reason \<Rightarrow> Inl (Code_Path_Validation reason)
                   | None \<Rightarrow> (case code_check_delivery_ttl maximum_ttl core of
                       Some reason \<Rightarrow> Inl (Code_Path_Validation reason)
                     | None \<Rightarrow> Inr (packet,scope,key))))"

lemma a_modern_reference_prefix_keeps_the_exact_packet_and_selected_boundary:
  assumes "code_reference_modern_prefix frame_limit profile selected channel deployment current_cut
      credential_packet window ordered cancelled verify_key maximum_ttl bytes = Inr (packet,scope,key)"
  shows "decode_wire_packet bytes = Some packet"
    "code_boundary_at (code_attach_channel_profile profile (code_source_selected_pair selected)) channel deployment current_cut None False = Inr (scope,key)"
    "code_admit_packet (verify_key key) packet scope = None"
    "code_check_delivery_ttl maximum_ttl (packet_core packet) = None"
    "code_gate_delivery window (boundary_now scope) (\<not> ordered) = None"
  using assms by (auto simp: code_reference_modern_prefix_def Let_def
    split: option.splits sum.splits prod.splits if_splits)

theorem an_accepted_modern_prefix_uses_the_exact_channel_peer_key:
  assumes accepted: "code_reference_modern_prefix frame_limit profile selected channel deployment current_cut
      credential_packet window ordered cancelled verify_key maximum_ttl bytes = Inr (packet,scope,key)"
  shows "key = guard_channel_peer_key channel"
proof -
  have boundary: "code_boundary_at (code_attach_channel_profile profile (code_source_selected_pair selected)) channel deployment current_cut None False = Inr (scope,key)"
    by (rule a_modern_reference_prefix_keeps_the_exact_packet_and_selected_boundary(2)[OF accepted])
  show ?thesis by (rule every_source_boundary_uses_the_channel_peer_key_and_exact_live_cut(1)[OF boundary])
qed

lemma the_modern_prefix_refuses_an_overlimit_signed_ttl_before_any_consumer:
  assumes "wire_ttl_seconds (packet_core packet) > limit"
  shows "code_reference_modern_prefix frame_limit profile selected channel deployment current_cut
      credential_packet window ordered cancelled verify_key (Some limit) bytes \<noteq> Inr (packet,scope,key)"
proof
  assume accepted: "code_reference_modern_prefix frame_limit profile selected channel deployment current_cut
      credential_packet window ordered cancelled verify_key (Some limit) bytes = Inr (packet,scope,key)"
  have "code_check_delivery_ttl (Some limit) (packet_core packet) = None"
    by (rule a_modern_reference_prefix_keeps_the_exact_packet_and_selected_boundary(4)[OF accepted])
  then show False using an_above_limit_signed_delivery_ttl_is_a_refusal[OF assms] by simp
qed

definition code_decode_original_debit :: "wire_bytes \<Rightarrow> wire_core \<Rightarrow> reference_original_debit option" where
  "code_decode_original_debit bytes core =
    (case code_decode_ordinary core of
      Code_Ordinary_Ready native credential versions (Wire_Debit generation) \<Rightarrow>
        Some (code_original_debit bytes core native generation)
     | _ \<Rightarrow> None)"

lemma a_decoded_original_debit_keeps_the_native_id_origin_and_generation:
  assumes "code_decode_original_debit bytes core = Some request"
  obtains native credential versions generation
  where
    "code_decode_ordinary core = Code_Ordinary_Ready native credential versions (Wire_Debit generation)"
    "original_call request = native_id native"
    "original_origin request = native_origin native"
    "original_generation request = generation"
    "original_transport request = authenticated_wire_message_id core"
    "original_packet request = bytes"
  using assms by (auto simp: code_decode_original_debit_def code_original_debit_def
    split: code_ordinary_result.splits ordinary_wire_command.splits)

definition code_source_debit_body_allowed where
  "code_source_debit_body_allowed max_nesting profile core \<longleftrightarrow>
    max_nesting > 0 \<and> code_debit_body_allowed profile core"

definition code_reference_admit_debit where
  "code_reference_admit_debit frame_limit profile selected channel deployment current_cut credential_packet
      window ordered cancelled verify_key maximum_ttl attest may_prepare bytes control =
    (case code_reference_modern_prefix frame_limit profile selected channel deployment current_cut
       credential_packet window ordered cancelled verify_key maximum_ttl bytes of
       Inl reason \<Rightarrow> control
     | Inr (packet,scope,key) \<Rightarrow>
       select_reference_wire_admission (verify_key key) attest (code_source_debit_body_allowed (code_source_selected_nesting selected)) scope
         (code_decode_original_debit bytes) may_prepare bytes control)"

lemma a_failed_modern_prefix_has_no_ordered_admission_effect:
  assumes "code_reference_modern_prefix frame_limit profile selected channel deployment current_cut
      credential_packet window ordered cancelled verify_key maximum_ttl bytes = Inl reason"
  shows "code_reference_admit_debit frame_limit profile selected channel deployment current_cut credential_packet
      window ordered cancelled verify_key maximum_ttl attest may_prepare bytes control = control"
  using assms by (simp add: code_reference_admit_debit_def)

theorem every_changed_source_debit_admission_reuses_the_actual_ordered_consumer:
  fixes control :: "'head reference_control"
    and selected :: "code_source_selected_boundary option"
    and profile :: negotiated_wire_profile and channel :: code_channel_guard
    and current_cut :: product_cut
  assumes changed: "code_reference_admit_debit frame_limit profile selected channel deployment current_cut credential_packet
      window ordered cancelled verify_key maximum_ttl attest may_prepare bytes control \<noteq> control"
  obtains packet :: wire_packet and scope :: wire_boundary
    and key :: wire_bytes and request :: reference_original_debit
  where
    "decode_wire_packet bytes = Some packet" "encode_wire_packet packet = bytes"
    "key = guard_channel_peer_key channel"
    "current_wire_scope scope (packet_core packet)"
    "code_decode_original_debit bytes (packet_core packet) = Some request"
    "original_packet request = bytes"
    "original_transport request = authenticated_wire_message_id (packet_core packet)"
    "may_prepare request" "reference_can_deliver request control" "reference_work_can_start request control"
    "control_decisions (code_reference_admit_debit frame_limit profile selected channel deployment current_cut credential_packet
      window ordered cancelled verify_key maximum_ttl attest may_prepare bytes control)
      (original_call request) = Some (request,Ref_Pending)"
proof -
  obtain initial scope key where prefix: "code_reference_modern_prefix frame_limit profile selected channel deployment current_cut
      credential_packet window ordered cancelled verify_key maximum_ttl bytes = Inr (initial,scope,key)"
    using changed by (auto simp: code_reference_admit_debit_def split: sum.splits prod.splits)
  have admitted: "code_reference_admit_debit frame_limit profile selected channel deployment current_cut credential_packet
      window ordered cancelled verify_key maximum_ttl attest may_prepare bytes control =
    select_reference_wire_admission (verify_key key) attest (code_source_debit_body_allowed (code_source_selected_nesting selected)) scope
      (code_decode_original_debit bytes) may_prepare bytes control"
    by (simp add: code_reference_admit_debit_def prefix)
  have effect: "select_reference_wire_admission (verify_key key) attest (code_source_debit_body_allowed (code_source_selected_nesting selected)) scope
      (code_decode_original_debit bytes) may_prepare bytes control \<noteq> control"
    using changed admitted by simp
  obtain packet request where actual:
    "decode_wire_packet bytes = Some packet" "encode_wire_packet packet = bytes"
    "current_wire_scope scope (packet_core packet)"
    "code_decode_original_debit bytes (packet_core packet) = Some request"
    "original_packet request = bytes"
    "original_transport request = authenticated_wire_message_id (packet_core packet)"
    "fst (original_call request) = wire_principal (packet_core packet)"
    "may_prepare request" "reference_can_deliver request control" "reference_work_can_start request control"
    "control_decisions (select_reference_wire_admission (verify_key key) attest (code_source_debit_body_allowed (code_source_selected_nesting selected)) scope
      (code_decode_original_debit bytes) may_prepare bytes control) (original_call request) = Some (request,Ref_Pending)"
    by (rule a_new_pending_request_has_the_exact_verified_wire_input[OF effect])
  have peer: "key = guard_channel_peer_key channel"
    by (rule an_accepted_modern_prefix_uses_the_exact_channel_peer_key[OF prefix])
  have saved: "control_decisions
      (code_reference_admit_debit frame_limit profile selected channel deployment current_cut credential_packet
        window ordered cancelled verify_key maximum_ttl attest may_prepare bytes control)
      (original_call request) = Some (request,Ref_Pending)"
    using actual(11) admitted by simp
  show thesis
  proof (rule that[where packet=packet and scope=scope and key=key and request=request])
    show "decode_wire_packet bytes = Some packet" by (rule actual(1))
    show "encode_wire_packet packet = bytes" by (rule actual(2))
    show "key = guard_channel_peer_key channel" by (rule peer)
    show "current_wire_scope scope (packet_core packet)" by (rule actual(3))
    show "code_decode_original_debit bytes (packet_core packet) = Some request" by (rule actual(4))
    show "original_packet request = bytes" by (rule actual(5))
    show "original_transport request = authenticated_wire_message_id (packet_core packet)" by (rule actual(6))
    show "may_prepare request" by (rule actual(8))
    show "reference_can_deliver request control" by (rule actual(9))
    show "reference_work_can_start request control" by (rule actual(10))
    show "control_decisions
        (code_reference_admit_debit frame_limit profile selected channel deployment current_cut credential_packet
          window ordered cancelled verify_key maximum_ttl attest may_prepare bytes control)
        (original_call request) = Some (request,Ref_Pending)" by (rule saved)
  qed
qed

lemma a_zero_depth_source_selection_cannot_admit_a_pending_debit:
  assumes "code_source_selected_nesting selected = 0"
  shows "code_reference_admit_debit frame_limit profile selected channel deployment current_cut credential_packet
      window ordered cancelled verify_key maximum_ttl attest may_prepare bytes control = control"
  using assms
  by (auto simp: code_reference_admit_debit_def select_reference_wire_admission_def
    wire_gate_def code_source_debit_body_allowed_def Let_def
    split: sum.splits option.splits prod.splits if_splits)

text \<open>
  Source Boundary selection retains max_nesting beside the old model scope/key
  pair. The original wire_boundary has no depth field. Its pair projection and
  the decoder depth come from this one selected value; None depth0 is never
  used after successful boundary admission. This connects a concrete source prefix and native Debit projection to the
  existing ordered-admission consumer. It is not the full consume mirror.
  The outstanding post-prefix stages must be composed before publication;
  may_prepare is the existing current product authorization boundary, and
  attest is the named external proof boundary, not an arbitrary path verdict.
\<close>

end
