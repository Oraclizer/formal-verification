theory Wire_Code_Finite_Integer_Check
  imports Wire_Code_Finite_Integer_ABI
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      invalid_finite_seed_metadata_cannot_create_an_opaque_runner
      invalid_integer_octets_cannot_change_the_finite_runner
      an_in_domain_integer_step_calls_only_the_fixed_raw_model_operation
      integer_decision_keeps_the_model_outcome_code_and_commit})
  then () else error "Unexpected oracle in opaque finite integer ABI"
\<close>

end
