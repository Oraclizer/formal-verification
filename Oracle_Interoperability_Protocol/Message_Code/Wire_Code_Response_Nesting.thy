theory Wire_Code_Response_Nesting
  imports Wire_Code_Operands_Native Wire_Code_Response_Status
begin

definition code_same_original where
  "code_same_original core original \<longleftrightarrow>
    wire_deployment core = wire_deployment original \<and>
    wire_source_domain core = wire_source_domain original \<and>
    wire_target_domain core = wire_target_domain original \<and>
    wire_principal core = wire_principal original \<and>
    wire_authority_epoch core = wire_authority_epoch original \<and> wire_version original = 6"

definition code_response_commit_matches :: "nat option \<Rightarrow> nat \<Rightarrow> bool" where
  "code_response_commit_matches position revision \<longleftrightarrow>
    (case position of None \<Rightarrow> True | Some retained \<Rightarrow> retained = revision)"

datatype code_nested_operand =
    Code_Nested_Ordinary wire_native_call ordinary_wire_command
  | Code_Nested_Legal client_call_id
  | Code_Nested_Spend client_call_id
  | Code_Nested_Receipt wire_core
  | Code_Nested_Response
  | Code_Nested_Other

text \<open>
  The operand classification is an explicit interface to the recursive
  operand decoder.  The theorems below do not certify a caller-supplied
  classification.  Closing that decoder interface is a separate obligation.
\<close>

fun code_check_nested_response where
  "code_check_nested_response nested (Code_Nested_Ordinary native command) call_id position =
    (if native_id native \<noteq> call_id \<or>
       ((case command of Wire_Debit generation \<Rightarrow> True | _ \<Rightarrow> False) \<and>
        \<not> code_response_commit_matches position (cut_revision (native_cut native)))
     then Some Invalid_Wire_Format else None)"
| "code_check_nested_response nested (Code_Nested_Legal nested_id) call_id position =
    (if nested_id \<noteq> call_id then Some Invalid_Wire_Format else None)"
| "code_check_nested_response nested (Code_Nested_Spend nested_id) call_id position =
    (if nested_id \<noteq> call_id then Some Invalid_Wire_Format else None)"
| "code_check_nested_response nested (Code_Nested_Receipt original) call_id position =
    (if \<not> code_same_original nested original then Some Invalid_Wire_Source
     else case code_native_call_prefix original of None \<Rightarrow> Some Invalid_Wire_Format | Some native \<Rightarrow>
       if native_id native \<noteq> call_id \<or>
         (wire_message_family original = Wire_State_Sync \<and> wire_opcode (wire_operation_body original) = 1 \<and>
          \<not> code_response_commit_matches position (cut_revision (native_cut native)))
       then Some Invalid_Wire_Format else None)"
| "code_check_nested_response nested Code_Nested_Response call_id position = Some Invalid_Wire_Format"
| "code_check_nested_response nested Code_Nested_Other call_id position = None"

theorem a_response_around_an_exact_receipt_checks_the_inner_version_identity_and_debit_cut:
  assumes accepted: "code_check_nested_response nested (Code_Nested_Receipt original) call_id position = None"
  obtains native where "wire_version original = 6"
    "wire_deployment original = wire_deployment nested"
    "wire_source_domain original = wire_source_domain nested"
    "wire_target_domain original = wire_target_domain nested"
    "wire_principal original = wire_principal nested"
    "wire_authority_epoch original = wire_authority_epoch nested"
    "decode_native_call_prefix original = Some native"
    "native_id native = call_id"
    "wire_message_family original = Wire_State_Sync \<and> wire_opcode (wire_operation_body original) = 1
       \<longrightarrow> code_response_commit_matches position (cut_revision (native_cut native))"
proof -
  obtain native where exact: "code_same_original nested original"
    and source: "code_native_call_prefix original = Some native"
    and id: "native_id native = call_id"
    and position: "wire_message_family original = Wire_State_Sync \<and> wire_opcode (wire_operation_body original) = 1
       \<longrightarrow> code_response_commit_matches position (cut_revision (native_cut native))"
    using accepted by (auto split: option.splits if_splits)
  have header: "wire_version original = 6"
    "wire_deployment original = wire_deployment nested"
    "wire_source_domain original = wire_source_domain nested"
    "wire_target_domain original = wire_target_domain nested"
    "wire_principal original = wire_principal nested"
    "wire_authority_epoch original = wire_authority_epoch nested"
    using exact by (auto simp: code_same_original_def)
  have decoded: "decode_native_call_prefix original = Some native"
    by (rule a_source_native_prefix_has_the_exact_product_header(1)[OF source])
  show thesis by (rule that[OF header decoded id position])
qed

lemma a_receipt_with_another_inner_version_is_a_source_refusal:
  "wire_version original \<noteq> 6 \<Longrightarrow>
    code_check_nested_response nested (Code_Nested_Receipt original) call_id position = Some Invalid_Wire_Source"
  by (simp add: code_same_original_def)

lemma a_receipt_with_a_different_inner_principal_is_a_source_refusal:
  "wire_principal nested \<noteq> wire_principal original \<Longrightarrow>
    code_check_nested_response nested (Code_Nested_Receipt original) call_id position = Some Invalid_Wire_Source"
  by (simp add: code_same_original_def)

lemma an_inner_debit_cannot_substitute_its_retained_commit_position:
  assumes "code_same_original nested original" "code_native_call_prefix original = Some native"
    "wire_message_family original = Wire_State_Sync" "wire_opcode (wire_operation_body original) = 1"
    "revision \<noteq> cut_revision (native_cut native)"
  shows "code_check_nested_response nested (Code_Nested_Receipt original) call_id (Some revision) =
    Some Invalid_Wire_Format"
  using assms by (simp add: code_response_commit_matches_def)

lemma another_response_cannot_be_the_nested_response_original:
  "code_check_nested_response nested Code_Nested_Response call_id position = Some Invalid_Wire_Format"
  by simp

end
