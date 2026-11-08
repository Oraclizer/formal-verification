theory Wire_Code_Source_Boundary_Depth_Check
  imports Wire_Code_Reference_Composition_Check
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    the_source_boundary_pair_and_depth_are_the_same_selected_record
    a_projected_source_selection_retains_its_exact_depth
    a_zero_depth_source_selection_cannot_admit_a_pending_debit
    a_ready_debit_publication_uses_depth_from_the_same_source_selection})
  then () else error "Unexpected oracle in source selected Boundary depth preservation"
\<close>

end
