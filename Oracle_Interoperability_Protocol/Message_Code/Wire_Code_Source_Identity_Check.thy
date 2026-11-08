theory Wire_Code_Source_Identity_Check
  imports Wire_Code_Source_Identity
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      the_source_active_identity_is_the_existing_current_model_identity_check
      a_source_authorized_call_consumes_its_exact_current_session_namespace_and_typed_action
      the_source_signature_adapter_receives_the_whole_fixed_typed_action
      the_source_known_endpoint_guard_is_an_explicit_additional_path_check
      source_authorize_call_does_not_replace_the_fresh_expected_cut_coherence_check
      an_authorized_materialized_call_keeps_the_received_principal_and_current_identity})
  then () else error "Unexpected oracle in source current identity path"
\<close>

end
