theory Wire_Code_Finite_Source_Slice_Check
  imports Wire_Code_Finite_Source_Slice
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      a_fixed_finite_model_request_keeps_the_exact_native_caller_and_current_context_coordinate
      a_raw_finite_selection_has_only_the_received_packet_and_fixed_source_request
      a_finite_raw_selector_never_accepts_a_replacement_request_from_its_caller
      an_unbound_generation_or_source_owner_cannot_reach_the_finite_financial_consumer
      each_finite_slice_outcome_keeps_its_program_produced_position
      a_finite_slice_outcome_has_exactly_the_existing_source_recorded_kind_and_commit_rule
      the_finite_source_revision_is_not_set_from_an_observed_after_state
      a_committed_source_slice_uses_the_selected_fixed_financial_operation})
  then () else error "Unexpected oracle in raw finite source slice helpers"
\<close>

end
