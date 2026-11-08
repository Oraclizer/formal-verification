theory Wire_Code_Debit_Selection
  imports Wire_Code_Operands_Native
begin

definition code_debit_body_allowed :: "negotiated_wire_profile \<Rightarrow> wire_core \<Rightarrow> bool" where
  "code_debit_body_allowed profile core =
    (case code_decode_ordinary core of Code_Ordinary_Ready native credential versions (Wire_Debit generation) \<Rightarrow> True
     | _ \<Rightarrow> False)"

definition code_select_debit_action where
  "code_select_debit_action verify attest authority route token endorsement attach bytes =
    (case code_library_gate verify attest code_debit_body_allowed authority bytes of
       Gate_Admitted packet \<Rightarrow>
         map_option snd (select_wire_debit route token endorsement attach (packet_core packet))
     | Gate_Refused reason \<Rightarrow> None)"

context source_attestation
begin

theorem the_prechecked_source_debit_selector_is_the_existing_service_selector:
  fixes authority :: wire_boundary
  assumes profile: "negotiated_version (boundary_profile authority) = 6"
    and precheck: "code_check_declared_version bytes (boundary_max_frame authority) = None"
    and threshold: "\<not> boundary_threshold_supported authority"
  shows "code_select_debit_action verify attest authority route token endorsement attach bytes =
    service_action_from_wire verify attest code_debit_body_allowed authority
      (map_option snd \<circ> select_wire_debit route token endorsement attach) bytes"
proof -
  have same: "code_library_gate verify attest code_debit_body_allowed authority bytes =
      wire_gate verify attest code_debit_body_allowed authority bytes"
    by (rule prechecked_current_input_reuses_the_model_admission[where authority = authority])
      (rule profile, rule precheck, rule threshold)
  show ?thesis using same
    by (cases "wire_gate verify attest code_debit_body_allowed authority bytes")
      (simp_all add: code_select_debit_action_def service_action_from_wire_def comp_def)
qed

theorem the_source_selected_debit_keeps_the_received_amount_recipient_generation_and_funding_owner:
  fixes authority :: wire_boundary
  assumes profile: "negotiated_version (boundary_profile authority) = 6"
    and precheck: "code_check_declared_version bytes (boundary_max_frame authority) = None"
    and threshold: "\<not> boundary_threshold_supported authority"
    and accepted: "code_select_debit_action verify attest authority route token endorsement attach bytes = Some action"
  obtains packet native credential versions generation request owner
  where
    "decode_wire_packet bytes = Some packet" "encode_wire_packet packet = bytes"
    "code_decode_ordinary (packet_core packet) =
      Code_Ordinary_Ready native credential versions (Wire_Debit generation)"
    "decode_native_call_prefix (packet_core packet) = Some native"
    "decode_ordinary_operands (packet_core packet) native = Some (credential,versions,Wire_Debit generation)"
    "attach native = Some request"
    "native_amount native < 2^64"
    "binding_amount (request_binding request) = native_amount native"
    "binding_recipient (request_binding request) = native_recipient native"
    "owner = native_funding_owner native"
    "action = debit_action_from_exact_operands route token endorsement (packet_core packet)
      native credential versions generation request"
proof -
  have gate: "code_library_gate verify attest code_debit_body_allowed authority bytes =
      wire_gate verify attest code_debit_body_allowed authority bytes"
    by (rule prechecked_current_input_reuses_the_model_admission[OF profile precheck threshold])
  have actual: "service_action_from_wire verify attest code_debit_body_allowed authority
      (map_option snd \<circ> select_wire_debit route token endorsement attach) bytes = Some action"
  proof -
    have link: "code_select_debit_action verify attest authority route token endorsement attach bytes =
      service_action_from_wire verify attest code_debit_body_allowed authority
        (map_option snd \<circ> select_wire_debit route token endorsement attach) bytes"
      by (rule the_prechecked_source_debit_selector_is_the_existing_service_selector[where authority = authority])
        (rule profile, rule precheck, rule threshold)
    show ?thesis using accepted by (simp only: link)
  qed
  obtain packet native credential versions generation request owner where old:
      "decode_wire_packet bytes = Some packet" "encode_wire_packet packet = bytes"
      "decode_native_call_prefix (packet_core packet) = Some native"
      "decode_ordinary_operands (packet_core packet) native = Some (credential,versions,Wire_Debit generation)"
      "attach native = Some request"
      "binding_amount (request_binding request) = native_amount native"
      "binding_recipient (request_binding request) = native_recipient native"
      "owner = native_funding_owner native"
      "action = debit_action_from_exact_operands route token endorsement (packet_core packet)
        native credential versions generation request"
    by (rule actual_debit_selection_uses_the_received_signed_core[OF actual])
  have admitted: "wire_gate verify attest code_debit_body_allowed authority bytes = Gate_Admitted packet"
    using accepted old(1) gate
    by (auto simp: code_select_debit_action_def wire_gate_def Let_def split: option.splits if_splits)
  have allowed: "code_debit_body_allowed (boundary_profile authority) (packet_core packet)"
    using a_wire_admission_uses_the_exact_current_domain_key_epoch_and_signature[OF admitted] by blast
  obtain source_native source_credential source_versions source_generation where source:
      "code_decode_ordinary (packet_core packet) =
        Code_Ordinary_Ready source_native source_credential source_versions (Wire_Debit source_generation)"
    using allowed
    by (auto simp: code_debit_body_allowed_def
      split: code_ordinary_result.splits ordinary_wire_command.splits)
  note exact = every_source_ordinary_result_retains_the_existing_decoded_operands[OF source]
  have same: "source_native = native" "source_credential = credential"
      "source_versions = versions" "source_generation = generation"
    using exact(1,3) old(3,4) by auto
  have ready: "code_decode_ordinary (packet_core packet) =
      Code_Ordinary_Ready native credential versions (Wire_Debit generation)"
    using source same by simp
  have limit: "native_amount native < 2^64" using exact(2) same(1) by simp
  show thesis by (rule that[OF old(1,2) ready old(3,4,5) limit old(6,7,8,9)])
qed

end

end
