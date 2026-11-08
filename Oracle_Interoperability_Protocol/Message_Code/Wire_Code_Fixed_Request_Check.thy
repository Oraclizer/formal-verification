theory Wire_Code_Fixed_Request_Check
  imports Wire_Code_Fixed_Call_Request Wire_Code_Fixed_Read_Execution
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    the_fixed_source_binding_preserves_every_actual_binding_field
    the_fixed_source_payload_keeps_the_exact_signed_header_credential_and_versions
    a_materialized_source_call_is_the_fixed_decoded_action_without_a_raw_request_argument
    an_actual_ordinary_operand_has_one_fixed_full_source_product_action
    an_actual_legal_operand_preserves_the_stage_and_original_order_fields
    an_actual_spend_operand_cannot_be_replaced_with_an_ordinary_action
    a_fixed_source_action_keeps_its_exact_core_endpoint
    a_decoded_call_has_the_existing_exact_native_header
    a_materialized_call_keeps_the_authenticated_caller_namespace
    a_materialized_current_scope_call_cannot_substitute_its_target
    a_source_read_uses_the_existing_exact_authenticated_invocation
    a_current_source_application_query_keeps_the_session_epoch_cut_and_asset
    source_attestation.the_prechecked_source_read_selector_is_the_existing_product_service_selector
    source_attestation.the_source_read_service_consumes_only_the_received_canonical_core
    reference_trace_consumer.an_unselected_source_read_cannot_enter_the_current_authority
    reference_trace_consumer.a_fixed_decoded_source_read_uses_the_actual_current_reference_consumer
    reference_trace_consumer.an_executed_source_read_has_the_exact_received_core_and_fixed_current_service
    reference_trace_consumer.the_current_identity_policy_can_refuse_the_fixed_read_without_a_cache_or_state_effect})
  then () else error "Unexpected oracle in fixed source requests or actual reference read consumption"
\<close>

end
