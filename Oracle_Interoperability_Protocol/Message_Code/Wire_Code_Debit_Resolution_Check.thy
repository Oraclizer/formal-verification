theory Wire_Code_Debit_Resolution_Check
  imports Wire_Code_Debit_Resolution
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    source_resolution_revocation_is_checked_but_cancellation_is_not_reconsumed
    a_changed_original_request_is_an_exact_disposition_conflict
    an_identical_pending_packet_needs_no_second_saved_packet_decode
    a_different_pending_body_for_the_same_authenticated_key_is_a_conflict
    a_successful_resolution_fence_compares_the_actual_revision_and_exact_bytes
    a_changed_control_body_cannot_pass_even_with_the_same_physical_revision
    a_changed_physical_revision_cannot_pass_even_with_the_same_control_body
    the_source_original_request_transport_is_recomputed_from_its_own_packet
    receipt_credential_lookup_does_not_reconsume_deadline_active_or_version_state
    a_missing_debit_credential_cannot_close_unseen_work
    a_close_requires_current_execute_authorization
    a_failed_control_replacement_is_not_reported_as_an_explicit_rejection
    a_completed_nonclosing_resolution_keeps_the_exact_observation
    an_identical_published_source_debit_returns_the_actual_collected_receipt
    a_waiting_receipt_cannot_report_an_already_published_control_as_unresolved
    a_rejected_original_with_a_waiting_receipt_still_fences_the_exact_observation})
  then () else error "Unexpected oracle in exact source control or Debit resolution tail"
\<close>

end
