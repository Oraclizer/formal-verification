theory Wire_Code_Reference_Boundary_Check
  imports Wire_Code_Response_Preflight Wire_Code_Debit_Recovery
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    the_dispatcher_packet_identity_test_is_not_a_cryptographic_signature_test
    the_nonordered_delivery_guard_has_the_existing_service_window
    the_ordered_delivery_guard_does_not_recheck_the_service_deadline
    explicit_cancellation_precedes_a_service_deadline_refusal
    every_source_boundary_uses_the_channel_peer_key_and_exact_live_cut
    the_two_source_signature_checks_use_identical_key_bytes_after_boundary_admission
    a_different_selected_key_is_a_source_refusal_before_any_product_consumer
    ordered_publication_can_reuse_its_admission_time_without_retesting_a_later_clock
    code_short_varint_length
    code_two_octet_varint_length
    code_varint_length_is_monotone
    code_fixed_response_words_have_value_independent_width
    the_source_response_body_length_depends_only_on_word_count_and_original_length
    source_response_body_is_the_actual_operation_body
    source_fixed_response_header_has_constant_width
    the_source_response_packet_length_ignores_fixed_field_values
    the_source_response_length_is_monotone_in_its_word_count
    measuring_six_response_words_bounds_every_valid_source_response
    the_six_word_placeholder_measures_the_bound_exactly
    a_preflight_original_is_verified_with_the_peer_key_before_a_response
    a_failed_original_preflight_has_no_product_effect_or_signed_response
    every_signed_response_passes_the_original_preflight
    every_signed_response_to_the_source_preflight_has_a_verified_original
    resolution_rechecks_the_signed_origin_clock_instead_of_the_current_delivery_clock
    resolution_cannot_fail_only_because_the_original_delivery_clock_is_now_late
    a_checked_applied_resolution_returns_the_exact_received_native_debit
    current_receipt_authorization_is_required_for_an_applied_response})
  then () else error "Unexpected oracle in reference boundary, response preflight and applied resolution"
\<close>

end
