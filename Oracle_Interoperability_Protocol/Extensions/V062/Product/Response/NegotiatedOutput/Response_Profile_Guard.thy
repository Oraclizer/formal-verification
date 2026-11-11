theory Response_Profile_Guard
  imports "OIP_Message_Code.Wire_Code_Response_Preflight"
    "OIP_Message_Code.Wire_Code_Oracle_Transport"
begin

definition response_profile_eligible :: "negotiated_wire_profile \<Rightarrow> bool" where
  "response_profile_eligible profile \<longleftrightarrow>
    negotiated_version profile = 6 \<and> code_profile_allows profile Wire_Ack 2 \<and>
    1 \<in> negotiated_schemes profile"

definition response_profile_gate ::
  "negotiated_wire_profile \<Rightarrow> (wire_bytes \<Rightarrow> wire_refusal + 'a) \<Rightarrow>
   wire_bytes \<Rightarrow> wire_refusal + 'a" where
  "response_profile_gate profile later bytes =
    (if response_profile_eligible profile then later bytes else Inl Unsupported_Wire_Version)"

lemma response_profile_gate_refuses_before_later:
  "negotiated_version profile \<noteq> 6 \<or> \<not> code_profile_allows profile Wire_Ack 2 \<or>
    1 \<notin> negotiated_schemes profile \<Longrightarrow>
    response_profile_gate profile later bytes = Inl Unsupported_Wire_Version"
  by (auto simp: response_profile_gate_def response_profile_eligible_def)

lemma response_profile_gate_continues_when_eligible:
  "response_profile_eligible profile \<Longrightarrow> response_profile_gate profile later bytes = later bytes"
  by (simp add: response_profile_gate_def)

lemma response_profile_refusal_preserves_the_model_state:
  assumes "\<not> response_profile_eligible profile"
  shows "code_receive_signed_response (response_profile_gate profile later)
      signer_available run encode bytes state =
    (state, Inl (Code_Path_Validation Unsupported_Wire_Version))"
  by (rule a_failed_original_preflight_has_no_product_effect_or_signed_response)
    (simp add: response_profile_gate_def assms)

lemma response_profile_empty_declared_version:
  "code_check_declared_version [] frame_limit = None"
  by (simp add: code_check_declared_version_def code_declared_version_def code_take_varint_def numeral_eq_Suc)

lemma response_profile_empty_packet:
  "decode_wire_packet [] = None"
  by (simp add: decode_wire_packet_def read_canonical_proto_fields_def put_proto_fields_def)

text \<open>
  The established preflight supplies the empty-original boundary under its
  attachment and channel checks. The continuation for nonempty input is left
  abstract.
\<close>

lemma response_profile_gate_empty_original:
  assumes "ordered_available" "revocation_matches" "guard_channel_current channel"
    "guard_channel_deployment channel = registered_deployment"
  shows "response_profile_gate profile
      (code_original_response_preflight profile channel ordered_available revocation_matches
        registered_deployment frame_limit selected_atomicity verify_peer) [] =
    (if response_profile_eligible profile then Inl Invalid_Wire_Format else Inl Unsupported_Wire_Version)"
  using assms
  by (auto simp: response_profile_gate_def response_profile_eligible_def
      code_original_response_preflight_def response_profile_empty_declared_version
      response_profile_empty_packet)

text \<open>
  The ABI receives the selected version, the ACK/2 permission as 0 or 1,
  the selected scheme identifiers, and the exact original octets. The
  continuation sentinel -1 marks eligible nonempty input for later checks.
\<close>

definition response_profile_guard_integer ::
  "integer \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer" where
  "response_profile_guard_integer version ack schemes bytes =
    (if version = 6 \<and> ack = 1 \<and> List.member schemes 1
     then if bytes = [] then 70 else -1
     else 71)"

lemma response_profile_guard_empty_cases:
  "response_profile_guard_integer 6 1 [2] [] = 71"
  "response_profile_guard_integer 6 1 [1, 2] [] = 70"
  by (simp_all add: response_profile_guard_integer_def List.member_iff)

lemma response_profile_guard_continue_scope:
  "response_profile_guard_integer version ack schemes bytes = -1 \<longleftrightarrow>
    version = 6 \<and> ack = 1 \<and> List.member schemes 1 \<and> bytes \<noteq> []"
  by (auto simp: response_profile_guard_integer_def split: if_splits)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      response_profile_gate_refuses_before_later
      response_profile_gate_continues_when_eligible
      response_profile_refusal_preserves_the_model_state
      response_profile_empty_declared_version response_profile_empty_packet
      response_profile_gate_empty_original
      response_profile_guard_empty_cases response_profile_guard_continue_scope})
  then () else error "Unexpected oracle in the response profile guard"
\<close>

export_code response_profile_guard_integer
  in SML module_name OIP_Response_Profile_Guard file_prefix "oip_response_profile_guard"

end
