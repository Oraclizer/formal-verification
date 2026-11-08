theory Wire_Code_Response_Binding_Boundary_Check
  imports Wire_Code_Response_Binding_Boundary
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    the_boundary_mode_is_the_existing_finite_channel_atomicity
    the_boundary_binding_uses_the_exact_existing_result_words_and_original
    the_uuid_primitive_request_is_the_existing_config_getter_preimage})
  then () else error "Unexpected oracle in typed result-to-binding primitive requests"
\<close>

end
