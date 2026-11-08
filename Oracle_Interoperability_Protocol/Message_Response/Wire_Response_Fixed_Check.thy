theory Wire_Response_Fixed_Check
  imports Wire_Response_Fixed_Receiver
begin

definition response_fixed_observed_debit where
  "response_fixed_observed_debit = \<lparr>source_outcome_reply = Code_Source_Accepted Code_Source_Debited_Reply,
     source_outcome_commit = Some 2\<rparr>"

lemma response_fixed_observed_debit_keeps_the_actual_fixture_result_fields:
  "response_fixed_words (7,33) (response_fixed_result
      (Response_Fixed_Received (Code_Source_Ordinary_Collected response_fixed_observed_debit)
        (Some (Code_Source_Ordinary_Receipt (Code_Source_Collected response_fixed_observed_debit))))) =
    Some (Recorded_Result,12,Some 2,[7,33,1,12,1,2])"
  by (simp add: response_fixed_observed_debit_def response_fixed_words_def response_fixed_descriptor_def
    code_source_ordinary_result_def code_response_words_def reference_result_codes_def)

lemma response_fixed_debited_without_a_commit_cannot_be_encoded:
  "response_fixed_words (7,33) (12,None) = None"
  by (simp add: response_fixed_words_def response_fixed_descriptor_def)

text \<open>
  The literal observation above is the actual sampled StoredCall value from
  the independently checked Rust fixture. This source-level example does not
  itself establish runtime provenance or equality of commit/cut coordinates.
  The original packet and actual product consumer must supply that relation.
\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    response_fixed_descriptor_is_the_literal_source_kind_commit_table
    response_fixed_words_keep_the_actual_position_without_replacing_it_by_a_cut
    response_fixed_parsed_words_reconstruct_the_actual_response_body
    response_fixed_matching_debit_receipt_keeps_the_retained_commit
    response_fixed_mismatched_receipt_is_not_a_result_supplier
    response_fixed_atomicity_is_the_first_member_of_the_finite_source_set
    response_fixed_core_has_no_caller_selected_outer_header
    response_fixed_core_is_the_existing_source_constructor_with_fixed_getters
    response_fixed_binding_preimage_uses_the_same_original_atomicity_and_words
    response_fixed_uuid_has_the_source_version_and_variant
    response_fixed_parameters_forward_the_immutable_config_and_clock_read
    response_fixed_unframe_recovers_exactly_the_core_that_was_signed
    response_fixed_sign_forwards_the_exact_framed_bytes_to_the_curve_primitive
    response_fixed_sign_refuses_an_unframed_or_unavailable_clock_input
    response_fixed_source_uuid_never_uses_a_supplied_uuid_as_its_binding
    response_fixed_canonical_packet_getter_keeps_the_received_core_bytes
    response_fixed_original_signature_reads_only_the_original_and_channel_peer
    response_fixed_preflight_selects_one_canonical_original_and_exact_peer_preimage
    response_fixed_parser_preserves_the_actual_nested_fields_and_checks
    response_fixed_parser_reuses_the_existing_recursive_source_decoder
    response_fixed_validation_keeps_the_exact_original_and_caller
    response_fixed_direct_debit_caller_is_the_actual_native_id
    response_fixed_direct_debit_validation_consumes_the_existing_hol_correlation
    response_fixed_encoding_has_actual_source_getter_preimage_and_postcheck_evidence
    response_fixed_typed_packet_decodes_to_the_same_source_value
    response_fixed_emission_keeps_the_actual_canonical_packet_bytes
    response_fixed_emission_sends_only_the_exact_constructed_preimage_to_the_signer
    response_fixed_emission_returns_the_exact_converted_kind_code_and_position
    response_fixed_emission_for_a_direct_debit_reaches_the_existing_correlation_consumer
    response_fixed_received_original_cannot_be_replaced_at_the_encoding_interface
    response_fixed_admission_keeps_the_actual_client_boundary_and_parsed_value
    response_fixed_client_admission_verifies_the_exact_received_preimage_with_the_current_peer
    response_fixed_original_byte_conflict_is_a_replay_refusal_after_shape_and_caller
    response_fixed_client_debit_admission_consumes_the_hol_response_relation
    response_fixed_unknown_status_remains_a_category_observation
    response_fixed_client_admission_always_has_a_typed_known_or_unknown_status
    response_fixed_observed_debit_keeps_the_actual_fixture_result_fields
    response_fixed_debited_without_a_commit_cannot_be_encoded})
  then () else error "Unexpected oracle in fixed source response field/preimage/correlation link"
\<close>

end
