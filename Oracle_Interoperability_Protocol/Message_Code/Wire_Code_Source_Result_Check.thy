theory Wire_Code_Source_Result_Check
  imports Wire_Code_Reference_Result
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    every_source_accepted_result_has_a_known_recorded_code
    every_source_ordinary_result_has_a_known_recorded_code
    a_source_ordinary_result_keeps_its_exact_commit_annotation
    a_well_annotated_source_ordinary_result_uses_the_existing_recorded_table
    a_source_legal_refusal_has_an_existing_uncommitted_result
    every_source_legal_result_has_the_existing_kind_and_commit_presence
    every_source_spend_result_has_the_existing_kind_and_commit_presence
    an_exact_ordinary_receipt_precedes_the_unresolved_fallback
    a_mismatched_ordinary_receipt_cannot_substitute_its_outcome
    a_matching_legal_busy_receipt_is_recorded_but_an_unretained_busy_is_delivery
    every_source_wire_validation_error_has_a_known_uncommitted_status
    every_source_error_response_is_known_and_uncommitted
    an_annotated_source_debit_has_the_exact_existing_payload_position
    source_publication_refusal_classes_precede_a_saved_guard_error
    a_saved_guard_refusal_survives_an_unclassified_transaction_hold
    a_product_error_precedes_the_postcommit_response_lost_flag
    a_lost_response_is_classified_only_after_a_successful_transaction
    source_result_classification_preserves_the_transaction_selected_state
    a_publication_deadline_becomes_delivery_status_fifty_two
    a_saved_product_refusal_is_not_replaced_by_an_unsigned_generic_hold})
  then () else error "Unexpected oracle in source outcome observations and transaction result classification"
\<close>

end
