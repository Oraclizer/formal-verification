theory Wire_Code_Reference_Composition_Check
  imports Wire_Code_Reference_Publication Wire_Code_Response_Assembly Wire_Code_Dispatch
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    a_modern_reference_prefix_keeps_the_exact_packet_and_selected_boundary
    an_accepted_modern_prefix_uses_the_exact_channel_peer_key
    the_modern_prefix_refuses_an_overlimit_signed_ttl_before_any_consumer
    a_decoded_original_debit_keeps_the_native_id_origin_and_generation
    a_failed_modern_prefix_has_no_ordered_admission_effect
    every_changed_source_debit_admission_reuses_the_actual_ordered_consumer
    a_changed_current_identity_refuses_debit_publication
    an_authorized_retained_debit_has_both_current_execute_and_receipt_permissions
    a_ready_debit_publication_keeps_its_admission_clock_and_peer_key
    a_refused_debit_publication_preserves_the_entire_product_image
    a_pending_model_publication_cannot_commit_a_product_image
    the_ready_source_debit_publishes_the_exact_existing_product_image_atomically
    the_source_response_core_has_exactly_the_existing_typed_response_body
    a_checked_source_response_packet_is_the_actual_guarded_reference_encoding
    the_checked_source_response_decodes_and_correlates_to_the_exact_original
    a_checked_source_response_has_the_exact_source_packet_bytes
    a_started_dispatcher_has_a_positive_representable_wait
    an_oversize_dispatch_is_refused_before_queueing
    a_queued_dispatch_uses_the_smaller_caller_or_configured_deadline
    an_unqueued_in_range_dispatch_is_unresolved
    a_reply_after_the_wait_deadline_is_unresolved_even_if_it_arrived
    a_live_received_worker_result_keeps_its_exact_error_or_response
    the_dispatch_worker_packet_credential_is_the_owned_packet
    the_dispatch_resolver_does_not_close_an_unresolved_original
    an_expired_wait_does_not_roll_back_the_workers_retained_state})
  then () else error "Unexpected oracle in reference admission publication response assembly or dispatch"
\<close>

end
