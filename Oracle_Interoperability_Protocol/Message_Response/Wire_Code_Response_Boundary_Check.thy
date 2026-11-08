theory Wire_Code_Response_Boundary_Check
  imports Wire_Code_Response_Boundary_Result
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    a_parsed_received_value_is_consumed_by_the_existing_result_converter
    different_actual_spend_roots_cannot_supply_a_matching_projected_receipt
    a_root_mismatch_keeps_the_existing_unresolved_conversion
    matching_full_spend_values_keep_the_actual_commit
    retained_legal_busy_precedes_the_delivery_busy_fallback
    the_same_boundary_outcome_supplies_the_exact_recorded_position
    a_boundary_error_tag_is_converted_instead_of_being_echoed})
  then () else error "Unexpected oracle in typed response-result boundary helpers"
\<close>

end
