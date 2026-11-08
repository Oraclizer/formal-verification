theory Wire_Response_Fixed_Expected
  imports Wire_Response_Fixed_Preimage
begin

definition response_fixed_expected_decode :: "wire_core \<Rightarrow> wire_refusal + code_nested_operand" where
  "response_fixed_expected_decode core =
    (case code_decode_operand_tree 1 core of
       Code_Tree_Refused reason \<Rightarrow> Inl reason
     | Code_Tree_Ready decoded \<Rightarrow> Inr decoded
     | Code_Tree_Pending \<Rightarrow> Inl Invalid_Wire_Format)"

fun response_fixed_caller_from_decoded :: "code_nested_operand \<Rightarrow> wire_refusal + client_call_id" where
  "response_fixed_caller_from_decoded (Code_Nested_Ordinary native command) = Inr (native_id native)"
| "response_fixed_caller_from_decoded (Code_Nested_Legal call_id) = Inr call_id"
| "response_fixed_caller_from_decoded (Code_Nested_Spend call_id) = Inr call_id"
| "response_fixed_caller_from_decoded decoded = Inl Invalid_Wire_Format"

lemma response_fixed_expected_then_caller_is_the_existing_source_projection:
  fixes core :: wire_core
  shows "(case response_fixed_expected_decode core of Inl reason \<Rightarrow> Inl reason
      | Inr decoded \<Rightarrow> response_fixed_caller_from_decoded decoded) = code_response_caller core"
  unfolding response_fixed_expected_decode_def code_response_caller_def
  by (cases "code_decode_operand_tree 1 core";
      simp split: code_nested_operand.splits)

lemma response_fixed_actual_expected_and_caller_keep_the_original_call_id:
  assumes "response_fixed_expected_decode core = Inr decoded"
    "response_fixed_caller_from_decoded decoded = Inr call_id"
  shows "code_response_caller core = Inr call_id"
  using response_fixed_expected_then_caller_is_the_existing_source_projection[of core] assms by simp

lemma response_fixed_existing_caller_success_has_an_actual_expected_decoding:
  assumes "code_response_caller core = Inr call_id"
  obtains decoded where "response_fixed_expected_decode core = Inr decoded"
    "response_fixed_caller_from_decoded decoded = Inr call_id"
  using response_fixed_expected_then_caller_is_the_existing_source_projection[of core] assms
  by (cases "response_fixed_expected_decode core"; auto)

lemma response_fixed_expected_query_decode_is_read_or_format_error:
  fixes query :: wire_core
  assumes "wire_message_family query = Wire_Query"
  shows "response_fixed_expected_decode query = Inr Code_Nested_Other \<or>
    response_fixed_expected_decode query = Inl Invalid_Wire_Format"
  using assms by (simp add: response_fixed_expected_decode_def One_nat_def Let_def
    split: option.splits list.splits prod.splits if_splits)

lemma response_fixed_expected_query_eight_fails_before_byte_comparison:
  fixes query :: wire_core
  assumes "wire_message_family query = Wire_Query" "wire_opcode (wire_operation_body query) = 8"
  shows "response_fixed_expected_decode query = Inl Invalid_Wire_Format"
  using assms by (simp add: response_fixed_expected_decode_def One_nat_def Let_def
    split: list.splits prod.splits if_splits)

text \<open>
  Rust response.rs423 decodes the expected operands before the byte comparison.
  The caller_id projection at425 is a separate operation reached only after
  exact original bytes match. These getters carry the actual depth1 decoder
  result; they do not accept a supplied classification or validation Boolean.
  Pending is unreachable for the existing complete operand decoder and is
  conservatively refused rather than interpreted as a call.
\<close>

end
