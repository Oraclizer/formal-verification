theory Wire_Code_Fixed_Call_Request
  imports Wire_Code_Operands_Regulated
begin

record code_source_binding =
  source_binding_origin :: source_key
  source_binding_asset :: nat
  source_binding_owner :: nat
  source_binding_destination :: nat
  source_binding_recipient :: nat
  source_binding_amount :: nat

record code_source_call_payload =
  source_payload_message :: nat
  source_payload_origin_epoch :: nat
  source_payload_endpoint :: nat
  source_payload_caller :: nat
  source_payload_session :: nat
  source_payload_cut :: product_cut
  source_payload_binding :: code_source_binding
  source_payload_credential :: "product_lock_credential option"
  source_payload_versions :: "(nat \<times> nat) list"
  source_payload_command :: ordinary_wire_command

definition code_source_binding_from_native :: "wire_native_call \<Rightarrow> code_source_binding" where
  "code_source_binding_from_native native =
    \<lparr>source_binding_origin = native_origin native,source_binding_asset = native_asset native,
     source_binding_owner = native_funding_owner native,source_binding_destination = native_destination native,
     source_binding_recipient = native_recipient native,source_binding_amount = native_amount native\<rparr>"

definition code_source_payload_from_native ::
  "wire_core \<Rightarrow> wire_native_call \<Rightarrow> product_lock_credential option \<Rightarrow> (nat \<times> nat) list \<Rightarrow>
    ordinary_wire_command \<Rightarrow> code_source_call_payload" where
  "code_source_payload_from_native core native credential versions command =
    \<lparr>source_payload_message = native_reference native,source_payload_origin_epoch = native_origin_epoch native,
     source_payload_endpoint = wire_target_domain core,source_payload_caller = fst (native_id native),
     source_payload_session = native_session native,source_payload_cut = native_cut native,
     source_payload_binding = code_source_binding_from_native native,source_payload_credential = credential,
     source_payload_versions = versions,source_payload_command = command\<rparr>"

datatype code_source_product_action =
    Code_Source_Ordinary_Action code_source_call_payload
  | Code_Source_Legal_Action_Data code_legal_stage code_source_call_payload code_legal_fields
  | Code_Source_Spend_Action_Data code_source_call_payload code_spend_fields

datatype code_source_call_operand =
    Code_Source_Ordinary_Operand wire_native_call "product_lock_credential option" "(nat \<times> nat) list" ordinary_wire_command
  | Code_Source_Legal_Operand wire_native_call code_legal_stage code_legal_fields wire_bytes
  | Code_Source_Spend_Operand wire_native_call code_spend_fields

datatype code_source_call_decode =
    Code_Source_Call_Refused wire_refusal
  | Code_Source_Call_Ready code_source_call_operand
  | Code_Source_Not_A_Call

definition code_decode_source_call_operand :: "wire_core \<Rightarrow> code_source_call_decode" where
  "code_decode_source_call_operand core =
    (let family = wire_message_family core; operation = wire_opcode (wire_operation_body core) in
     if (family = Wire_State_Sync \<and> operation = 6) \<or> (family = Wire_Regulatory \<and> operation = 3) then
       (case code_decode_spend core of Code_Spend_Refused reason \<Rightarrow> Code_Source_Call_Refused reason
        | Code_Spend_Ready native parsed_spend \<Rightarrow> Code_Source_Call_Ready (Code_Source_Spend_Operand native parsed_spend))
     else if family \<in> {Wire_State_Sync,Wire_Lock} then
       (case code_decode_ordinary core of Code_Ordinary_Refused reason \<Rightarrow> Code_Source_Call_Refused reason
        | Code_Ordinary_Ready native credential versions command \<Rightarrow>
            Code_Source_Call_Ready (Code_Source_Ordinary_Operand native credential versions command))
     else if family = Wire_Regulatory then
       (case code_decode_legal core of Code_Legal_Refused reason \<Rightarrow> Code_Source_Call_Refused reason
        | Code_Legal_Ready native stage parsed_legal raw_proof \<Rightarrow>
            Code_Source_Call_Ready (Code_Source_Legal_Operand native stage parsed_legal raw_proof))
     else Code_Source_Not_A_Call)"

record code_source_action_request =
  source_request_target :: nat
  source_request_id :: client_call_id
  source_request_expected :: product_cut
  source_request_action :: code_source_product_action

fun code_source_operand_native :: "code_source_call_operand \<Rightarrow> wire_native_call" where
  "code_source_operand_native (Code_Source_Ordinary_Operand native credential versions command) = native"
| "code_source_operand_native (Code_Source_Legal_Operand native stage parsed_legal raw_proof) = native"
| "code_source_operand_native (Code_Source_Spend_Operand native parsed_spend) = native"

fun code_source_action_from_operand :: "wire_core \<Rightarrow> code_source_call_operand \<Rightarrow> code_source_product_action" where
  "code_source_action_from_operand core (Code_Source_Ordinary_Operand native credential versions command) =
    Code_Source_Ordinary_Action (code_source_payload_from_native core native credential versions command)"
| "code_source_action_from_operand core (Code_Source_Legal_Operand native stage parsed_legal raw_proof) =
    Code_Source_Legal_Action_Data stage (code_source_payload_from_native core native None [] Wire_Publish) parsed_legal"
| "code_source_action_from_operand core (Code_Source_Spend_Operand native parsed_spend) =
    Code_Source_Spend_Action_Data (code_source_payload_from_native core native None [] Wire_Publish) parsed_spend"

fun code_source_action_payload :: "code_source_product_action \<Rightarrow> code_source_call_payload" where
  "code_source_action_payload (Code_Source_Ordinary_Action payload) = payload"
| "code_source_action_payload (Code_Source_Legal_Action_Data stage payload order) = payload"
| "code_source_action_payload (Code_Source_Spend_Action_Data payload authorization) = payload"

definition code_source_request_from_operand :: "nat \<Rightarrow> wire_core \<Rightarrow> code_source_call_operand \<Rightarrow> code_source_action_request" where
  "code_source_request_from_operand target core operand =
    (let native = code_source_operand_native operand in
     \<lparr>source_request_target = target,source_request_id = native_id native,source_request_expected = native_cut native,
      source_request_action = code_source_action_from_operand core operand\<rparr>)"

definition code_materialize_source_call :: "nat \<Rightarrow> wire_core \<Rightarrow> (wire_refusal + code_source_action_request option)" where
  "code_materialize_source_call target core =
    (case code_decode_source_call_operand core of Code_Source_Call_Refused reason \<Rightarrow> Inl reason
     | Code_Source_Not_A_Call \<Rightarrow> Inr None
     | Code_Source_Call_Ready operand \<Rightarrow> Inr (Some (code_source_request_from_operand target core operand)))"

lemma the_fixed_source_binding_preserves_every_actual_binding_field:
  "source_binding_origin (code_source_binding_from_native native) = native_origin native"
  "source_binding_asset (code_source_binding_from_native native) = native_asset native"
  "source_binding_owner (code_source_binding_from_native native) = native_funding_owner native"
  "source_binding_destination (code_source_binding_from_native native) = native_destination native"
  "source_binding_recipient (code_source_binding_from_native native) = native_recipient native"
  "source_binding_amount (code_source_binding_from_native native) = native_amount native"
  by (simp_all add: code_source_binding_from_native_def)

lemma the_fixed_source_payload_keeps_the_exact_signed_header_credential_and_versions:
  "source_payload_message (code_source_payload_from_native core native credential versions command) = native_reference native"
  "source_payload_origin_epoch (code_source_payload_from_native core native credential versions command) = native_origin_epoch native"
  "source_payload_endpoint (code_source_payload_from_native core native credential versions command) = wire_target_domain core"
  "source_payload_caller (code_source_payload_from_native core native credential versions command) = fst (native_id native)"
  "source_payload_session (code_source_payload_from_native core native credential versions command) = native_session native"
  "source_payload_cut (code_source_payload_from_native core native credential versions command) = native_cut native"
  "source_payload_credential (code_source_payload_from_native core native credential versions command) = credential"
  "source_payload_versions (code_source_payload_from_native core native credential versions command) = versions"
  "source_payload_command (code_source_payload_from_native core native credential versions command) = command"
  by (simp_all add: code_source_payload_from_native_def)

theorem a_materialized_source_call_is_the_fixed_decoded_action_without_a_raw_request_argument:
  assumes "code_materialize_source_call target core = Inr (Some request)"
  obtains operand
  where "code_decode_source_call_operand core = Code_Source_Call_Ready operand"
    "request = code_source_request_from_operand target core operand"
    "source_request_id request = native_id (code_source_operand_native operand)"
    "source_request_expected request = native_cut (code_source_operand_native operand)"
    "source_request_target request = target"
    "source_request_action request = code_source_action_from_operand core operand"
  using assms by (auto simp: code_materialize_source_call_def code_source_request_from_operand_def Let_def
    split: code_source_call_decode.splits)

lemma an_actual_ordinary_operand_has_one_fixed_full_source_product_action:
  "code_source_action_from_operand core (Code_Source_Ordinary_Operand native credential versions command) =
    Code_Source_Ordinary_Action (code_source_payload_from_native core native credential versions command)"
  by simp

lemma an_actual_legal_operand_preserves_the_stage_and_original_order_fields:
  "code_source_action_from_operand core (Code_Source_Legal_Operand native stage parsed_legal raw_proof) =
    Code_Source_Legal_Action_Data stage (code_source_payload_from_native core native None [] Wire_Publish) parsed_legal"
  by simp

lemma an_actual_spend_operand_cannot_be_replaced_with_an_ordinary_action:
  "code_source_action_from_operand core (Code_Source_Spend_Operand native parsed_spend) \<noteq>
    Code_Source_Ordinary_Action arbitrary_payload"
  by simp

lemma a_fixed_source_action_keeps_its_exact_core_endpoint:
  "source_payload_endpoint (code_source_action_payload (code_source_action_from_operand core operand)) = wire_target_domain core"
  by (cases operand) (simp_all add: code_source_payload_from_native_def)

lemma a_decoded_call_has_the_existing_exact_native_header:
  assumes "code_decode_source_call_operand core = Code_Source_Call_Ready operand"
  shows "decode_native_call_prefix core = Some (code_source_operand_native operand)"
  using assms
  by (auto simp: code_decode_source_call_operand_def Let_def
    dest: every_source_ordinary_result_retains_the_existing_decoded_operands(1)
      a_source_legal_result_keeps_the_stage_endpoint_origin_epoch_and_proof(1)
      a_source_spend_has_the_exact_destination_and_two_u64_amounts(1)
    split: code_ordinary_result.splits code_legal_result.splits code_spend_result.splits if_splits)

theorem a_materialized_call_keeps_the_authenticated_caller_namespace:
  assumes accepted: "code_materialize_source_call target core = Inr (Some request)"
  shows "fst (source_request_id request) = wire_principal core"
proof -
  obtain operand where decoded: "code_decode_source_call_operand core = Code_Source_Call_Ready operand"
    and same: "request = code_source_request_from_operand target core operand"
    using accepted by (auto simp: code_materialize_source_call_def split: code_source_call_decode.splits)
  have prefix: "decode_native_call_prefix core = Some (code_source_operand_native operand)"
    by (rule a_decoded_call_has_the_existing_exact_native_header[OF decoded])
  have caller: "fst (native_id (code_source_operand_native operand)) = wire_principal core"
    using native_transport_never_truncates_the_caller_namespace_or_epoch[OF prefix] by simp
  show ?thesis using caller by (simp add: same code_source_request_from_operand_def Let_def)
qed

theorem a_materialized_current_scope_call_cannot_substitute_its_target:
  assumes scope_matches: "current_wire_scope scope core"
    and accepted: "code_materialize_source_call (boundary_target scope) core = Inr (Some request)"
  shows "source_request_target request = wire_target_domain core"
    "source_payload_endpoint (code_source_action_payload (source_request_action request)) = wire_target_domain core"
proof -
  obtain operand where same: "request = code_source_request_from_operand (boundary_target scope) core operand"
    using accepted by (auto simp: code_materialize_source_call_def split: code_source_call_decode.splits)
  have target: "boundary_target scope = wire_target_domain core"
    using scope_matches by (simp add: current_wire_scope_def)
  show "source_request_target request = wire_target_domain core"
    by (simp add: same code_source_request_from_operand_def Let_def target)
  show "source_payload_endpoint (code_source_action_payload (source_request_action request)) = wire_target_domain core"
    by (simp add: same code_source_request_from_operand_def Let_def a_fixed_source_action_keeps_its_exact_core_endpoint)
qed

text \<open>
  Source: operands.rs native/ordinary/legal/spend and wire.rs request_at.
  This is a fixed value materializer with no arbitrary decode/attach/request
  callback. In particular Binding.owner is retained inside the source action.
  The old execution_request has additional certificate/context-version and
  binding-operation/separator fields absent from Rust's Binding/CallPayload.
  Their authoritative projection and current consumer execution remain
  separate M145/M159 obligations. This source constructor alone does not
  establish execution in the old product model or actual compiled Rust.
  Legal/spend preserve the native default command only as an unused payload
  field; their distinct action carries the legal order or spend authorization.
  Raw legal proof bytes remain in the decoded operand for the pre-execution
  proof adapter, not as a newly invented product action credential.
\<close>

end
