theory Wire_Code_Debit_Canary
  imports Wire_Code_Operands_Native "OIP_Reference_Profile.Reference_Exact_Guard_Packets"
begin

definition code_guard_native :: wire_native_call where
  "code_guard_native =
    \<lparr>native_reference = 33,native_id = (7,33),native_session = 2,
      native_cut = \<lparr>cut_authority_epoch = 9,cut_revision = 2\<rparr>,
      native_origin_epoch = 9,native_origin = (0,17),native_asset = 17,native_funding_owner = 7,
      native_destination = 2,native_recipient = 3,native_amount = 5,
      native_tail_words = [1,17,0,17,7,0,9,1,17,0,1],native_proof_bytes = []\<rparr>"

definition code_guard_credential :: product_lock_credential where
  "code_guard_credential =
    \<lparr>credential_token = \<lparr>token_asset = 17,token_owner = 7,token_generation = 0\<rparr>,
      credential_epoch = 9,credential_origin = (0,17)\<rparr>"

lemma the_runtime_guard_debit_has_the_source_decoded_operands:
  "code_decode_ordinary guard_debit_core =
    Code_Ordinary_Ready code_guard_native (Some code_guard_credential) [(17,0)] (Wire_Debit 1)"
  by (simp add: code_decode_ordinary_def code_native_call_prefix_def code_product_amount_def
    guard_debit_core_def guard_debit_body_def code_guard_native_def code_guard_credential_def
    decode_ordinary_operands_def decode_wire_credential_prefix_def decode_ordinary_tail_def
    code_ordinary_proofs_allowed_def wire_octets_def source_twenty_four_zero_octets Let_def)

lemma the_runtime_guard_debit_reaches_the_existing_product_selector_header:
  "native_debit_header_allowed guard_debit_core code_guard_native"
  by (rule every_source_debit_meets_the_existing_debit_selector_header[OF
    the_runtime_guard_debit_has_the_source_decoded_operands])

lemma the_runtime_guard_debit_keeps_the_exact_source_encoder_anchor:
  "code_typed_encode_core guard_debit_core = Some guard_debit_core_bytes"
proof -
  have packet: "wire_packet_wellformed guard_debit_packet"
    using every_accepted_wire_message_has_exactly_the_received_bytes[OF
      guard_debit_decodes_from_the_full_native_envelope] by blast
  have core: "wire_core_wellformed guard_debit_core"
    using packet by (simp add: wire_packet_wellformed_def)
  show ?thesis
    by (simp add: the_typed_source_encoder_is_the_checked_canonical_encoder
      core guard_debit_exact_core_encoding)
qed

definition code_guard_wrong_target where
  "code_guard_wrong_target = guard_debit_core\<lparr>wire_target_domain := 2\<rparr>"

lemma the_same_debit_with_only_its_target_changed_is_a_source_refusal:
  "code_decode_ordinary code_guard_wrong_target = Code_Ordinary_Refused Invalid_Wire_Source"
  by (simp add: code_decode_ordinary_def code_guard_wrong_target_def code_native_call_prefix_def code_product_amount_def
    guard_debit_core_def guard_debit_body_def decode_ordinary_operands_def decode_wire_credential_prefix_def
    decode_ordinary_tail_def code_ordinary_proofs_allowed_def wire_octets_def source_twenty_four_zero_octets Let_def)

definition code_ordinary_without_endpoint_check where
  "code_ordinary_without_endpoint_check core =
    (if wire_deadline (wire_operation_body core) \<noteq> Deadline_Absent
     then Code_Ordinary_Refused Invalid_Wire_Format
     else case code_native_call_prefix core of None \<Rightarrow> Code_Ordinary_Refused Invalid_Wire_Format | Some native \<Rightarrow>
       (case decode_ordinary_operands core native of None \<Rightarrow> Code_Ordinary_Refused Invalid_Wire_Format
        | Some (credential,versions,command) \<Rightarrow>
          if \<not> code_ordinary_proofs_allowed native command
          then Code_Ordinary_Refused Invalid_Wire_Format
          else Code_Ordinary_Ready native credential versions command))"

lemma deleting_only_the_endpoint_check_reaches_a_semantically_wrong_debit:
  "code_ordinary_without_endpoint_check code_guard_wrong_target =
    Code_Ordinary_Ready code_guard_native (Some code_guard_credential) [(17,0)] (Wire_Debit 1)"
  "\<not> native_debit_header_allowed code_guard_wrong_target code_guard_native"
  by (simp_all add: code_ordinary_without_endpoint_check_def code_guard_wrong_target_def
    code_native_call_prefix_def code_product_amount_def guard_debit_core_def guard_debit_body_def
    code_guard_native_def code_guard_credential_def decode_ordinary_operands_def
    decode_wire_credential_prefix_def decode_ordinary_tail_def code_ordinary_proofs_allowed_def
    native_debit_header_allowed_def wire_octets_def source_twenty_four_zero_octets Let_def)

lemma the_existing_product_selector_also_rejects_the_changed_target:
  "select_wire_debit route token endorsement attach code_guard_wrong_target = None"
  by (simp add: select_wire_debit_def native_debit_header_allowed_def code_guard_wrong_target_def
    decode_native_call_prefix_def guard_debit_core_def guard_debit_body_def
    wire_octets_def Let_def)

end
