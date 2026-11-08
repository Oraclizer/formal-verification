theory Wire_Response_General_Getters
  imports Wire_Response_Fixed_Receiver
    "OIP_Message_Code.Wire_Code_Fixed_Call_Request"
begin

fun response_general_nested_operand :: "code_source_call_operand \<Rightarrow> code_nested_operand" where
  "response_general_nested_operand (Code_Source_Ordinary_Operand native credential versions command) =
    Code_Nested_Ordinary native command"
| "response_general_nested_operand (Code_Source_Legal_Operand native stage parsed_legal raw_proof) =
    Code_Nested_Legal (native_id native)"
| "response_general_nested_operand (Code_Source_Spend_Operand native parsed_spend) =
    Code_Nested_Spend (native_id native)"

definition response_general_nonordinary :: "wire_core \<Rightarrow> code_source_call_operand option" where
  "response_general_nonordinary core =
    (case code_decode_source_call_operand core of
       Code_Source_Call_Ready operand \<Rightarrow>
         (case operand of Code_Source_Ordinary_Operand native credential versions command \<Rightarrow> None
          | Code_Source_Legal_Operand native stage parsed_legal raw_proof \<Rightarrow> Some operand
          | Code_Source_Spend_Operand native parsed_spend \<Rightarrow> Some operand)
     | _ \<Rightarrow> None)"

lemma response_general_selection_is_the_actual_fixed_call_decoder:
  assumes "response_general_nonordinary core = Some operand"
  shows "code_decode_source_call_operand core = Code_Source_Call_Ready operand"
    "(\<exists>native stage parsed_legal raw_proof.
       operand = Code_Source_Legal_Operand native stage parsed_legal raw_proof) \<or>
     (\<exists>native parsed_spend. operand = Code_Source_Spend_Operand native parsed_spend)"
  using assms by (auto simp: response_general_nonordinary_def
    split: code_source_call_decode.splits code_source_call_operand.splits)

lemma response_general_actual_call_has_the_same_recursive_source_class:
  assumes "code_decode_source_call_operand core = Code_Source_Call_Ready operand"
  shows "code_decode_operand_tree (Suc fuel) core = Code_Tree_Ready (response_general_nested_operand operand)"
  using assms by (auto simp: code_decode_source_call_operand_def code_ordinary_tree_def
    code_legal_tree_def code_spend_tree_def Let_def
    split: code_ordinary_result.splits code_legal_result.splits code_spend_result.splits if_splits)

theorem response_general_selected_caller_is_the_fixed_native_id:
  assumes selected: "response_general_nonordinary core = Some operand"
  shows "code_response_caller core = Inr (native_id (code_source_operand_native operand))"
    "decode_native_call_prefix core = Some (code_source_operand_native operand)"
proof -
  have actual_decode: "code_decode_source_call_operand core = Code_Source_Call_Ready operand"
    by (rule response_general_selection_is_the_actual_fixed_call_decoder(1)[OF selected])
  have one_level: "code_decode_operand_tree 1 core = Code_Tree_Ready (response_general_nested_operand operand)"
    using response_general_actual_call_has_the_same_recursive_source_class[OF actual_decode,where fuel=0]
    by (simp only: One_nat_def)
  show "code_response_caller core = Inr (native_id (code_source_operand_native operand))"
    using one_level by (cases operand) (simp_all add: code_response_caller_def)
  show "decode_native_call_prefix core = Some (code_source_operand_native operand)"
    by (rule a_decoded_call_has_the_existing_exact_native_header[OF actual_decode])
qed

lemma response_general_legal_decode_has_its_actual_operation_tag:
  assumes "code_decode_legal core = Code_Legal_Ready native stage parsed_legal raw_proof"
  shows "wire_opcode (wire_operation_body core) \<in> {1,2}"
  using assms by (auto simp: code_decode_legal_def Let_def
    split: option.splits list.splits if_splits)

lemma response_general_selected_legal_or_spend_is_not_an_original_debit:
  assumes "response_general_nonordinary core = Some operand"
  shows "\<not> (wire_message_family core = Wire_State_Sync \<and> wire_opcode (wire_operation_body core) = 1)"
  using assms by (auto simp: response_general_nonordinary_def code_decode_source_call_operand_def Let_def
    split: code_source_call_decode.splits code_source_call_operand.splits code_ordinary_result.splits
      code_legal_result.splits code_spend_result.splits if_splits)

lemma response_general_selected_call_has_the_actual_native_response_shape:
  assumes "response_general_nonordinary core = Some operand"
  shows "code_response_call_shape (wire_message_family core) (wire_opcode (wire_operation_body core))"
  using assms
  by (auto simp: response_general_nonordinary_def code_decode_source_call_operand_def
    code_response_call_shape_def Let_def
    dest: response_general_legal_decode_has_its_actual_operation_tag
    split: code_source_call_decode.splits code_source_call_operand.splits code_ordinary_result.splits
      code_legal_result.splits code_spend_result.splits if_splits)

lemma response_general_legal_and_spend_results_keep_their_source_positions:
  "response_fixed_result (Response_Fixed_Received (Code_Source_Legal_Action (Code_Source_Legal_Emitted position))
      (Some (Code_Source_Legal_Receipt (Code_Source_Legal_Emitted position)))) = (26,Some position)"
  "response_fixed_result (Response_Fixed_Received (Code_Source_Legal_Action (Code_Source_Legal_Applied position))
      (Some (Code_Source_Legal_Receipt (Code_Source_Legal_Applied position)))) = (27,Some position)"
  "response_fixed_result (Response_Fixed_Received (Code_Source_Spend_Action (Code_Source_Spend_Executed position))
      (Some (Code_Source_Spend_Receipt (Code_Source_Spend_Executed position)))) = (28,Some position)"
  by simp_all

text \<open>
  This selector consumes the existing fixed source call decoder and retains
  all Legal/Spend native fields and raw proof data. It does not accept a
  caller-provided classifier or a passed-guard Boolean. Positions above are
  the supplied actual source Outcome observations, never an input-cut alias.
\<close>

end
