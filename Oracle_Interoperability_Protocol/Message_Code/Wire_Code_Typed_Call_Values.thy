theory Wire_Code_Typed_Call_Values
  imports Wire_Code_Typed_IR
begin

fun code_ir_command :: "ordinary_wire_command \<Rightarrow> nat list" where
  "code_ir_command (Wire_Reserve oip_binder_value) = code_ir_node 110 [code_ir_scalar oip_binder_value]"
| "code_ir_command (Wire_Dispatch oip_binder_value) = code_ir_node 111 [code_ir_scalar oip_binder_value]"
| "code_ir_command (Wire_Debit oip_binder_value) = code_ir_node 112 [code_ir_scalar oip_binder_value]"
| "code_ir_command (Wire_Cancel oip_binder_value) = code_ir_node 113 [code_ir_scalar oip_binder_value]"
| "code_ir_command (Wire_Fence oip_binder_value) = code_ir_node 114 [code_ir_scalar oip_binder_value]"
| "code_ir_command (Wire_Preempt oip_binder_value) = code_ir_node 115 [code_ir_scalar oip_binder_value]"
| "code_ir_command (Wire_Timeout oip_binder_value) = code_ir_node 116 [code_ir_scalar oip_binder_value]"
| "code_ir_command (Wire_Record_Terminal oip_binder_kind oip_binder_reference) =
    code_ir_node 117 [code_ir_scalar oip_binder_kind,code_ir_scalar oip_binder_reference]"
| "code_ir_command (Wire_Deliver oip_binder_reference) = code_ir_node 118 [code_ir_scalar oip_binder_reference]"
| "code_ir_command (Wire_Refund oip_binder_generation oip_binder_reference) =
    code_ir_node 119 [code_ir_scalar oip_binder_generation,code_ir_scalar oip_binder_reference]"
| "code_ir_command (Wire_Reconcile oip_binder_generation oip_binder_reference) =
    code_ir_node 120 [code_ir_scalar oip_binder_generation,code_ir_scalar oip_binder_reference]"
| "code_ir_command (Wire_Write oip_binder_generation oip_binder_value) =
    code_ir_node 121 [code_ir_scalar oip_binder_generation,code_ir_scalar oip_binder_value]"
| "code_ir_command Wire_Publish = code_ir_node 122 []"

definition code_ir_credential :: "product_lock_credential \<Rightarrow> nat list" where
  "code_ir_credential oip_binder_credential =
    (let oip_binder_token = credential_token oip_binder_credential in code_ir_node 101
      [code_ir_scalar (token_asset oip_binder_token),code_ir_scalar (token_owner oip_binder_token),
       code_ir_scalar (token_generation oip_binder_token),code_ir_scalar (credential_epoch oip_binder_credential),
       code_ir_pair (credential_origin oip_binder_credential)])"

definition code_ir_native :: "wire_core \<Rightarrow> wire_native_call \<Rightarrow> nat list" where
  "code_ir_native oip_binder_core oip_binder_native =
    (let oip_binder_payload = code_source_payload_from_native oip_binder_core oip_binder_native None [] Wire_Publish;
         oip_binder_binding = source_payload_binding oip_binder_payload
     in code_ir_node 100
       [code_ir_scalar (source_payload_message oip_binder_payload),code_ir_pair (native_id oip_binder_native),
        code_ir_scalar (source_payload_session oip_binder_payload),code_ir_cut (source_payload_cut oip_binder_payload),
        code_ir_scalar (source_payload_origin_epoch oip_binder_payload),code_ir_pair (source_binding_origin oip_binder_binding),
        code_ir_scalar (source_binding_asset oip_binder_binding),code_ir_scalar (source_binding_owner oip_binder_binding),
        code_ir_scalar (source_binding_destination oip_binder_binding),code_ir_scalar (source_binding_recipient oip_binder_binding),
        code_ir_scalar (source_binding_amount oip_binder_binding),code_ir_scalar (source_payload_endpoint oip_binder_payload),
        code_ir_scalar (source_payload_caller oip_binder_payload)])"

definition code_ir_legal_fields :: "code_legal_fields \<Rightarrow> nat list" where
  "code_ir_legal_fields oip_binder_order = code_ir_node 102
    [code_ir_scalar (legal_action_number oip_binder_order),code_ir_scalar (legal_officer oip_binder_order),
     code_ir_scalar (legal_jurisdiction oip_binder_order),code_ir_scalar (legal_basis oip_binder_order),
     code_ir_scalar (legal_issuance_epoch oip_binder_order),code_ir_set (legal_scope oip_binder_order),
     code_ir_option code_ir_pair (legal_predecessor oip_binder_order),
     code_ir_option code_ir_scalar (legal_destination oip_binder_order),
     code_ir_option code_ir_scalar (legal_appeal_deadline oip_binder_order)]"

definition code_ir_enforcement :: "code_enforcement_fields \<Rightarrow> nat list" where
  "code_ir_enforcement oip_binder_order = code_ir_node 108
    [code_ir_scalar (enforcement_officer oip_binder_order),code_ir_scalar (enforcement_jurisdiction oip_binder_order),
     code_ir_scalar (enforcement_basis oip_binder_order),code_ir_set (enforcement_assets oip_binder_order),
     code_ir_option code_ir_pair (enforcement_prior_seizure oip_binder_order),
     code_ir_option code_ir_scalar (enforcement_appeal_deadline oip_binder_order)]"

definition code_ir_spend_fields :: "code_spend_fields \<Rightarrow> nat list" where
  "code_ir_spend_fields oip_binder_spend = code_ir_node 103
    [code_ir_scalar (spend_reference oip_binder_spend),code_ir_scalar (spend_sender oip_binder_spend),
     code_ir_scalar (spend_recipient oip_binder_spend),code_ir_scalar (spend_kind_number oip_binder_spend),
     code_ir_scalar (spend_amount oip_binder_spend),code_ir_option code_ir_enforcement (spend_enforcement oip_binder_spend),
     code_ir_option code_ir_bytes (spend_proof oip_binder_spend)]"

definition code_typed_ordinary_ir :: "wire_core \<Rightarrow> nat list option" where
  "code_typed_ordinary_ir oip_binder_core =
    (case code_decode_ordinary oip_binder_core of Code_Ordinary_Refused oip_binder_reason \<Rightarrow> None
     | Code_Ordinary_Ready oip_binder_native oip_binder_credential oip_binder_versions oip_binder_command \<Rightarrow> Some
       (code_ir_node 10 [code_ir_native oip_binder_core oip_binder_native,code_ir_option code_ir_credential oip_binder_credential,
         code_ir_list code_ir_pair oip_binder_versions,code_ir_command oip_binder_command,
         code_ir_list code_ir_bytes (native_proof_bytes oip_binder_native)]))"

definition code_typed_legal_ir :: "wire_core \<Rightarrow> nat list option" where
  "code_typed_legal_ir oip_binder_core =
    (case code_decode_legal oip_binder_core of Code_Legal_Refused oip_binder_reason \<Rightarrow> None
     | Code_Legal_Ready oip_binder_native oip_binder_stage oip_binder_order oip_binder_proof \<Rightarrow> Some
       (code_ir_node 11 [code_ir_native oip_binder_core oip_binder_native,
         code_ir_scalar (case oip_binder_stage of Code_Source_Emission \<Rightarrow> 0 | Code_Receiving_Commit \<Rightarrow> 1),
         code_ir_legal_fields oip_binder_order,code_ir_bytes oip_binder_proof]))"

definition code_typed_spend_ir :: "wire_core \<Rightarrow> nat list option" where
  "code_typed_spend_ir oip_binder_core =
    (case code_decode_spend oip_binder_core of Code_Spend_Refused oip_binder_reason \<Rightarrow> None
     | Code_Spend_Ready oip_binder_native oip_binder_spend \<Rightarrow> Some
       (code_ir_node 12 [code_ir_native oip_binder_core oip_binder_native,code_ir_spend_fields oip_binder_spend]))"

lemma an_ordinary_summary_consumes_its_actual_decoded_values:
  assumes "code_decode_ordinary oip_binder_core = Code_Ordinary_Ready oip_binder_native oip_binder_credential oip_binder_versions oip_binder_command"
  shows "code_typed_ordinary_ir oip_binder_core = Some
    (code_ir_node 10 [code_ir_native oip_binder_core oip_binder_native,code_ir_option code_ir_credential oip_binder_credential,
      code_ir_list code_ir_pair oip_binder_versions,code_ir_command oip_binder_command,
      code_ir_list code_ir_bytes (native_proof_bytes oip_binder_native)])"
  using assms by (simp add: code_typed_ordinary_ir_def)

lemma a_legal_summary_consumes_its_actual_decoded_values:
  assumes "code_decode_legal oip_binder_core = Code_Legal_Ready oip_binder_native oip_binder_stage oip_binder_order oip_binder_proof"
  shows "code_typed_legal_ir oip_binder_core = Some
    (code_ir_node 11 [code_ir_native oip_binder_core oip_binder_native,
      code_ir_scalar (case oip_binder_stage of Code_Source_Emission \<Rightarrow> 0 | Code_Receiving_Commit \<Rightarrow> 1),
      code_ir_legal_fields oip_binder_order,code_ir_bytes oip_binder_proof])"
  using assms by (simp add: code_typed_legal_ir_def)

lemma a_spend_summary_consumes_its_actual_decoded_values:
  assumes "code_decode_spend oip_binder_core = Code_Spend_Ready oip_binder_native oip_binder_spend"
  shows "code_typed_spend_ir oip_binder_core = Some (code_ir_node 12
    [code_ir_native oip_binder_core oip_binder_native,code_ir_spend_fields oip_binder_spend])"
  using assms by (simp add: code_typed_spend_ir_def)

lemma the_native_summary_keeps_the_actual_binding_owner_endpoint_and_caller:
  "code_ir_native oip_binder_core oip_binder_native = code_ir_node 100
    [code_ir_scalar (native_reference oip_binder_native),code_ir_pair (native_id oip_binder_native),
     code_ir_scalar (native_session oip_binder_native),code_ir_cut (native_cut oip_binder_native),
     code_ir_scalar (native_origin_epoch oip_binder_native),code_ir_pair (native_origin oip_binder_native),
     code_ir_scalar (native_asset oip_binder_native),code_ir_scalar (native_funding_owner oip_binder_native),
     code_ir_scalar (native_destination oip_binder_native),code_ir_scalar (native_recipient oip_binder_native),
     code_ir_scalar (native_amount oip_binder_native),code_ir_scalar (wire_target_domain oip_binder_core),
     code_ir_scalar (fst (native_id oip_binder_native))]"
  by (simp add: code_ir_native_def code_source_payload_from_native_def code_source_binding_from_native_def)

lemma different_typed_commands_are_not_collapsed_to_an_accept_boolean:
  "code_ir_command (Wire_Reserve oip_binder_value) \<noteq> code_ir_command (Wire_Debit oip_binder_value)"
  "code_ir_command (Wire_Write oip_binder_first oip_binder_second) \<noteq> code_ir_command (Wire_Reconcile oip_binder_first oip_binder_second)"
  by (simp_all add: code_ir_node_def)

end
