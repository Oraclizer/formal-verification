theory Wire_Response_General_Check
  imports Wire_Response_General_Receipt_Query Wire_Response_Fixed_Check
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    response_general_selection_is_the_actual_fixed_call_decoder
    response_general_actual_call_has_the_same_recursive_source_class
    response_general_selected_caller_is_the_fixed_native_id
    response_general_legal_decode_has_its_actual_operation_tag
    response_general_selected_legal_or_spend_is_not_an_original_debit
    response_general_selected_call_has_the_actual_native_response_shape
    response_general_legal_and_spend_results_keep_their_source_positions
    response_general_nonordinary_validation_consumes_hol_correlation
    response_general_source_emission_correlates_for_the_selected_legal_or_spend
    response_general_current_client_correlates_the_same_legal_or_spend_original
    response_general_nested_receipt_is_selected_by_the_actual_decoder
    response_general_nested_receipt_consumes_its_actual_inner_identity_and_commit_check
    response_general_nested_receipt_keeps_the_exact_response_word_tuple
    response_general_query_has_no_depth_one_response_caller
    response_general_query_eight_is_refused_at_one_core_level
    response_general_structural_receipt_requires_the_actual_larger_nesting_depth
    response_general_expected_query_is_format_refused_after_response_shape
    response_general_query_decode_success_and_original_mismatch_is_replay
    response_general_query_eight_decode_error_precedes_any_original_mismatch
    response_general_query_is_never_an_accepted_expected_native_call
    response_general_current_client_does_not_accept_an_expected_query
    response_general_query_cannot_pass_signed_response_preparation
    response_general_query_original_cannot_produce_a_signed_emission
    response_general_distinct_canonical_families_have_distinct_original_bytes
    response_general_receipt_wrapper_cannot_be_relabelled_as_its_inner_expected_call
    response_general_format_and_original_conflict_keep_the_source_error_numbers})
  then () else error "Unexpected oracle in general native-call correlation and receipt/query API scope"
\<close>

text \<open>
  This theory checks the native-call correlation claims listed above.
  The claims concern typed call selection, response shape and receipt/query
  validation. Product-state and StoredCall provenance, complete resolver
  execution and financial replay are separate obligations. A retained cut
  and a commit position are distinct values.
\<close>

end
