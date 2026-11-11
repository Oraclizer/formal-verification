theory Wire_Code_Finite_Closed_Check
  imports Wire_Code_Finite_Closed_Financial
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      the_finite_current_use_test_consumes_exact_epoch_version_and_explicit_permission_pattern
      absent_finite_context_entries_have_the_named_existing_defaults
      the_data_only_context_and_version_wrapper_is_the_same_frozen_debit
      finite_asset_claims_are_the_exact_existing_footprint_override
      finite_acquire_event_interprets_the_exact_existing_reservation_and_footprint
      finite_acquire_commit_interprets_the_exact_existing_state_and_event
      finite_dispatch_commit_interprets_the_exact_existing_state_and_event
      the_finite_reserve_and_frozen_reserve_are_exactly_the_same_operation
      the_finite_dispatch_and_frozen_dispatch_are_exactly_the_same_operation
      closed_current_use_is_exactly_the_interpreted_existing_test
      closed_footprint_is_exactly_the_interpreted_existing_footprint
      closed_metadata_is_exactly_the_interpreted_existing_permission
      closed_ownership_is_exactly_the_interpreted_existing_finite_query
      closed_reserve_is_the_same_finite_reserve_with_the_interpreted_context
      closed_dispatch_is_the_same_finite_dispatch_with_the_interpreted_context
      closed_debit_is_the_same_finite_debit_with_the_interpreted_context
      each_closed_data_command_is_exactly_its_frozen_financial_operation})
  then () else error "Unexpected oracle in closed finite financial operation"
\<close>

end
