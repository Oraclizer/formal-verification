theory Wire_Code_Operand_Tree
  imports Wire_Code_Operands_Governance Wire_Code_Response_Nesting
begin

datatype code_operand_tree_result =
    Code_Tree_Refused wire_refusal
  | Code_Tree_Ready code_nested_operand
  | Code_Tree_Pending

definition code_ordinary_tree where
  "code_ordinary_tree core =
    (case code_decode_ordinary core of Code_Ordinary_Refused reason \<Rightarrow> Code_Tree_Refused reason
     | Code_Ordinary_Ready native credential versions command \<Rightarrow>
       Code_Tree_Ready (Code_Nested_Ordinary native command))"

definition code_legal_tree where
  "code_legal_tree core =
    (case code_decode_legal core of Code_Legal_Refused reason \<Rightarrow> Code_Tree_Refused reason
     | Code_Legal_Ready native stage parsed_fields proof \<Rightarrow> Code_Tree_Ready (Code_Nested_Legal (native_id native)))"

definition code_spend_tree where
  "code_spend_tree core =
    (case code_decode_spend core of Code_Spend_Refused reason \<Rightarrow> Code_Tree_Refused reason
     | Code_Spend_Ready native parsed_fields \<Rightarrow> Code_Tree_Ready (Code_Nested_Spend (native_id native)))"

definition code_receipt_tree_finish where
  "code_receipt_tree_finish original decoded =
    (case decoded of
       Code_Tree_Ready (Code_Nested_Ordinary native command) \<Rightarrow> Code_Tree_Ready (Code_Nested_Receipt original)
     | Code_Tree_Ready (Code_Nested_Legal call_id) \<Rightarrow> Code_Tree_Ready (Code_Nested_Receipt original)
     | Code_Tree_Ready (Code_Nested_Spend call_id) \<Rightarrow> Code_Tree_Ready (Code_Nested_Receipt original)
     | Code_Tree_Ready other \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format
     | Code_Tree_Refused reason \<Rightarrow> Code_Tree_Refused reason
     | Code_Tree_Pending \<Rightarrow> Code_Tree_Pending)"

definition code_response_tree_finish where
  "code_response_tree_finish core nested decoded =
    (case response_result_words (wire_words (wire_operation_body core)) of None \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format
     | Some (call_id,kind,number,position) \<Rightarrow>
       if kind \<noteq> Recorded_Result \<and> position \<noteq> None then Code_Tree_Refused Invalid_Wire_Format
       else if wire_version nested \<noteq> wire_version core \<or> wire_deployment nested \<noteq> wire_deployment core \<or>
         wire_principal nested \<noteq> fst call_id \<or> wire_source_domain nested \<noteq> wire_target_domain core \<or>
         wire_target_domain nested \<noteq> wire_source_domain core
       then Code_Tree_Refused Invalid_Wire_Source
       else case code_check_nested_response nested decoded call_id position of
         Some reason \<Rightarrow> Code_Tree_Refused reason | None \<Rightarrow> Code_Tree_Ready Code_Nested_Response)"

definition code_response_tree_after_nested where
  "code_response_tree_after_nested core nested result =
    (case result of Code_Tree_Refused reason \<Rightarrow> Code_Tree_Refused reason
     | Code_Tree_Pending \<Rightarrow> Code_Tree_Pending
     | Code_Tree_Ready decoded \<Rightarrow> code_response_tree_finish core nested decoded)"

fun code_decode_operand_tree :: "nat \<Rightarrow> wire_core \<Rightarrow> code_operand_tree_result" where
  "code_decode_operand_tree 0 core = Code_Tree_Refused Invalid_Wire_Format"
| "code_decode_operand_tree (Suc fuel) core =
    (let body = wire_operation_body core; family = wire_message_family core; operation = wire_opcode body in
     if (family = Wire_State_Sync \<and> operation = 6) \<or> (family = Wire_Regulatory \<and> operation = 3)
     then code_spend_tree core
     else if family \<in> {Wire_State_Sync,Wire_Lock} then code_ordinary_tree core
     else if family = Wire_Regulatory then code_legal_tree core
     else if family = Wire_Query then
       (if operation = 8 then
         (case (wire_words body,wire_blobs body) of ([session],[original_bytes]) \<Rightarrow>
           if wire_deadline body \<noteq> Deadline_Absent \<or> fuel = 0 then Code_Tree_Refused Invalid_Wire_Format
           else (case decode_wire_core original_bytes of None \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format
             | Some original \<Rightarrow> code_receipt_tree_finish original (code_decode_operand_tree fuel original))
          | _ \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format)
        else case code_decode_query_nonreceipt core of None \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format
          | Some query \<Rightarrow> Code_Tree_Ready Code_Nested_Other)
     else if family = Wire_Ack then
       (if operation = 2 then
         (if wire_deadline body \<noteq> Deadline_Absent then Code_Tree_Refused Invalid_Wire_Format
          else case wire_blobs body of [original_bytes] \<Rightarrow>
            (case decode_wire_core original_bytes of None \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format
             | Some original \<Rightarrow> code_response_tree_after_nested core original (code_decode_operand_tree fuel original))
           | _ \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format)
        else case code_decode_settlement_ack core of None \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format
          | Some ack \<Rightarrow> Code_Tree_Ready Code_Nested_Other)
     else if family = Wire_Heartbeat then
       (case code_decode_heartbeat core of None \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format
        | Some heartbeat \<Rightarrow> Code_Tree_Ready Code_Nested_Other)
     else if family = Wire_Governance then
       (case code_decode_governance core of None \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format
        | Some governance \<Rightarrow> Code_Tree_Ready Code_Nested_Other)
     else Code_Tree_Refused Invalid_Wire_Format)"

lemma a_receipt_tree_accepts_only_a_decoded_call:
  assumes "code_receipt_tree_finish original decoded = Code_Tree_Ready (Code_Nested_Receipt original)"
  shows "(\<exists>native command. decoded = Code_Tree_Ready (Code_Nested_Ordinary native command)) \<or>
    (\<exists>call_id. decoded = Code_Tree_Ready (Code_Nested_Legal call_id)) \<or>
    (\<exists>call_id. decoded = Code_Tree_Ready (Code_Nested_Spend call_id))"
  using assms by (cases decoded; auto simp: code_receipt_tree_finish_def split: code_nested_operand.splits)

theorem the_recursive_response_slice_keeps_the_header_and_inner_check:
  assumes "code_response_tree_finish core nested decoded = Code_Tree_Ready Code_Nested_Response"
  obtains call_id kind number position where
    "response_result_words (wire_words (wire_operation_body core)) = Some (call_id,kind,number,position)"
    "wire_version nested = wire_version core" "wire_deployment nested = wire_deployment core"
    "wire_principal nested = fst call_id" "wire_source_domain nested = wire_target_domain core"
    "wire_target_domain nested = wire_source_domain core"
    "code_check_nested_response nested decoded call_id position = None"
  using assms by (auto simp: code_response_tree_finish_def split: option.splits prod.splits if_splits)

lemma an_inner_failure_precedes_every_response_word_or_header_check:
  "code_response_tree_after_nested core nested (Code_Tree_Refused reason) = Code_Tree_Refused reason"
  by (simp add: code_response_tree_after_nested_def)

lemma an_unimplemented_nested_scope_cannot_be_silently_accepted:
  "code_response_tree_after_nested core nested Code_Tree_Pending = Code_Tree_Pending"
  "code_receipt_tree_finish original Code_Tree_Pending = Code_Tree_Pending"
  by (simp_all add: code_response_tree_after_nested_def code_receipt_tree_finish_def)

lemma ordinary_legal_and_spend_models_have_no_pending_constructor:
  "code_ordinary_tree core \<noteq> Code_Tree_Pending"
  "code_legal_tree core \<noteq> Code_Tree_Pending"
  "code_spend_tree core \<noteq> Code_Tree_Pending"
  by (auto simp: code_ordinary_tree_def code_legal_tree_def code_spend_tree_def
    split: code_ordinary_result.splits code_legal_result.splits code_spend_result.splits)

lemma receipt_pending_is_exactly_a_pending_inner_decode:
  "code_receipt_tree_finish original decoded = Code_Tree_Pending \<longleftrightarrow> decoded = Code_Tree_Pending"
  by (cases decoded)
    (auto simp: code_receipt_tree_finish_def split: code_nested_operand.splits)

lemma response_word_and_header_checks_have_no_pending_constructor:
  "code_response_tree_finish core nested decoded \<noteq> Code_Tree_Pending"
  by (auto simp: code_response_tree_finish_def split: option.splits prod.splits if_splits)

lemma response_pending_is_exactly_a_pending_inner_decode:
  "code_response_tree_after_nested core nested decoded = Code_Tree_Pending \<longleftrightarrow> decoded = Code_Tree_Pending"
  by (cases decoded)
    (simp_all add: code_response_tree_after_nested_def response_word_and_header_checks_have_no_pending_constructor)

theorem every_declared_operand_family_has_an_executable_model_branch:
  "code_decode_operand_tree depth core \<noteq> Code_Tree_Pending"
  by (induction depth arbitrary: core)
    (auto simp: Let_def ordinary_legal_and_spend_models_have_no_pending_constructor
      receipt_pending_is_exactly_a_pending_inner_decode response_pending_is_exactly_a_pending_inner_decode
      split: option.splits list.splits if_splits)

end
