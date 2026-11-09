theory Reference_Write_Profile
  imports "OIP_Message_Code.Wire_Code_Operands_Native"
begin

definition reference_accepts_write where
  "reference_accepts_write family opcode \<longleftrightarrow>
    code_reference_accepts family opcode \<or> (family = Wire_Lock \<and> opcode = 7)"

lemma reference_write_is_the_only_admission_change:
  "(reference_accepts_write family opcode \<noteq> code_reference_accepts family opcode) \<longleftrightarrow>
    family = Wire_Lock \<and> opcode = 7"
  by (cases family) (auto simp: reference_accepts_write_def)

lemma reference_write_admission_preserves_the_protocol_opcode_table:
  "reference_accepts_write family opcode \<Longrightarrow> valid_family_opcode family opcode"
  by (auto simp: reference_accepts_write_def intro: every_accepted_reference_operation_is_a_protocol_operation)

lemma every_other_decoded_operation_keeps_its_admission_and_exact_bytes:
  assumes "decode_wire_packet bytes = Some packet"
    "(wire_message_family (packet_core packet), wire_opcode (wire_operation_body (packet_core packet))) \<noteq> (Wire_Lock,7)"
  shows "code_check_operation reference_accepts_write (packet_core packet) =
      code_check_operation code_reference_accepts (packet_core packet)"
    "encode_wire_packet packet = bytes"
proof -
  show "code_check_operation reference_accepts_write (packet_core packet) =
      code_check_operation code_reference_accepts (packet_core packet)"
    using assms(2) by (auto simp: code_check_operation_def reference_accepts_write_def)
  show "encode_wire_packet packet = bytes"
    by (rule every_accepted_wire_message_has_exactly_the_received_bytes[THEN conjunct1, OF assms(1)])
qed

lemma the_new_profile_accepts_the_existing_write_layout:
  assumes "wire_message_family core = Wire_Lock" "wire_opcode (wire_operation_body core) = 7"
  shows "code_check_operation code_reference_accepts core = Some Unsupported_Wire_Version"
    "code_check_operation reference_accepts_write core = None"
    "decode_ordinary_tail Wire_Lock 7 [generation,value] = Some (Wire_Write generation value)"
  using assms by (simp_all add: code_check_operation_def reference_accepts_write_def decode_ordinary_tail_def)

definition reference_write_payload where
  "reference_write_payload core native credential versions generation value request =
    \<lparr>payload_envelope = \<lparr>envelope_message = native_reference native, envelope_origin = native_origin native,
       envelope_asset = native_asset native, envelope_caller = fst (native_id native),
       envelope_session = native_session native, envelope_cut = native_cut native,
       envelope_command = Client_Protocol (wire_target_domain core) 0 (Write_Intent request generation versions value)\<rparr>,
      payload_credential = credential, payload_origin_epoch = native_origin_epoch native\<rparr>"

definition select_reference_write where
  "select_reference_write attach core =
    (if wire_message_family core = Wire_Lock \<and> wire_opcode (wire_operation_body core) = 7 then
      case code_decode_ordinary core of
        Code_Ordinary_Ready native credential versions (Wire_Write generation value) \<Rightarrow>
          (case attach native of None \<Rightarrow> None | Some request \<Rightarrow>
            if signed_debit_request_matches native request \<and>
              request_authority_epoch request = cut_authority_epoch (native_cut native)
            then Some (native_id native, reference_write_payload core native credential versions generation value request)
            else None)
      | _ \<Rightarrow> None
    else None)"

lemma a_selected_write_consumes_the_exact_typed_operands:
  assumes "select_reference_write attach core = Some (call_id,payload)"
  obtains native credential versions generation write_value request where
    "code_decode_ordinary core = Code_Ordinary_Ready native credential versions (Wire_Write generation write_value)"
    "attach native = Some request"
    "signed_debit_request_matches native request"
    "request_authority_epoch request = cut_authority_epoch (native_cut native)"
    "native_envelope_matches core native call_id payload"
    "payload_credential payload = credential"
    "envelope_command (payload_envelope payload) =
      Client_Protocol (wire_target_domain core) 0 (Write_Intent request generation versions write_value)"
proof -
  obtain native credential versions generation write_value request where fields:
    "code_decode_ordinary core = Code_Ordinary_Ready native credential versions (Wire_Write generation write_value)"
    "attach native = Some request" "signed_debit_request_matches native request"
    "request_authority_epoch request = cut_authority_epoch (native_cut native)"
    "call_id = native_id native"
    "payload = reference_write_payload core native credential versions generation write_value request"
    using assms by (auto simp: select_reference_write_def
      split: code_ordinary_result.splits ordinary_wire_command.splits option.splits if_splits)
  have prefix: "code_native_call_prefix core = Some native"
    using every_source_ordinary_result_retains_the_existing_decoded_operands(1,2)[OF fields(1)]
    by (simp add: source_native_prefix_is_the_existing_prefix_with_its_actual_amount_limit)
  have caller: "fst (native_id native) = wire_principal core"
    by (rule a_source_native_prefix_has_the_exact_product_header(3)[OF prefix])
  show thesis
    by (rule that[OF fields(1-4)])
      (simp_all add: fields(5,6) caller reference_write_payload_def native_envelope_matches_def Let_def)
qed

end
