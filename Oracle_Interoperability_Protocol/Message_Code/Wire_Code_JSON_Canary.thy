theory Wire_Code_JSON_Canary
  imports Wire_Code_JSON_Contexts "HOL-Library.Code_Target_Nat"
begin

definition code_fixed_context_json :: wire_bytes where
  "code_fixed_context_json = [91,123,34,101,110,100,112,111,105,110,116,34,58,50,44,34,101,112,111,99,104,34,58,57,44,34,103,114,97,110,116,115,34,58,91,91,55,44,34,78,111,114,109,97,108,34,44,34,82,101,115,101,114,118,101,34,93,44,91,55,44,34,78,111,114,109,97,108,34,44,34,68,101,98,105,116,34,93,93,44,34,100,101,112,101,110,100,101,110,99,105,101,115,34,58,91,91,49,55,44,91,49,55,44,49,56,93,93,93,44,34,119,114,105,116,101,95,112,101,114,109,105,115,115,105,111,110,115,34,58,91,91,55,44,49,55,44,49,93,93,125,93]"

definition code_fixed_sessions_json :: wire_bytes where
  "code_fixed_sessions_json = [91,91,53,44,123,34,112,114,105,110,99,105,112,97,108,34,58,55,44,34,97,117,116,104,111,114,105,116,121,95,101,112,111,99,104,34,58,57,125,93,93]"

definition code_fixed_context_value :: code_json_endpoint_context where
  "code_fixed_context_value = \<lparr>json_context_endpoint = 2,json_context_epoch = 9,
    json_context_grants = [(7,0,0),(7,0,2)],json_context_dependencies = [(17,[17,18])],
    json_context_write_permissions = [(7,17,1)]\<rparr>"

lemma the_published_context_json_has_the_exact_typed_value:
  "code_json_contexts code_fixed_context_json = Some [code_fixed_context_value]"
  by code_simp

lemma the_published_session_binding_json_has_the_exact_typed_value:
  "code_json_session_bindings code_fixed_sessions_json =
    Some [(5,\<lparr>json_session_principal = 7,json_session_epoch = 9\<rparr>)]"
  by code_simp

lemma reversing_the_two_permission_variants_is_not_a_canonical_set:
  "code_json_contexts [91,123,34,101,110,100,112,111,105,110,116,34,58,50,44,34,101,112,111,99,104,34,58,57,44,34,103,114,97,110,116,115,34,58,91,91,55,44,34,78,111,114,109,97,108,34,44,34,68,101,98,105,116,34,93,44,91,55,44,34,78,111,114,109,97,108,34,44,34,82,101,115,101,114,118,101,34,93,93,44,34,100,101,112,101,110,100,101,110,99,105,101,115,34,58,91,91,49,55,44,91,49,55,44,49,56,93,93,93,44,34,119,114,105,116,101,95,112,101,114,109,105,115,115,105,111,110,115,34,58,91,91,55,44,49,55,44,49,93,93,125,93] = None"
  by code_simp

lemma canonical_json_never_rounds_an_integer_above_two_to_fifty_three:
  "code_json_complete code_json_u64 (code_json_ascii ''9007199254740993'') = Some 9007199254740993"
  by code_simp

lemma a_json_integer_at_two_to_sixty_four_is_outside_the_source_domain:
  "code_json_complete code_json_u64 (code_json_ascii ''18446744073709551616'') = None"
  by code_simp

lemma noncanonical_leading_zero_and_trailing_space_are_refused:
  "code_json_complete code_json_u64 (code_json_ascii ''01'') = None"
  "code_json_session_bindings (code_fixed_sessions_json @ [32]) = None"
  by code_simp+

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    the_published_context_json_has_the_exact_typed_value
    the_published_session_binding_json_has_the_exact_typed_value
    reversing_the_two_permission_variants_is_not_a_canonical_set
    canonical_json_never_rounds_an_integer_above_two_to_fifty_three
    a_json_integer_at_two_to_sixty_four_is_outside_the_source_domain
    noncanonical_leading_zero_and_trailing_space_are_refused})
  then () else error "Unexpected oracle in governance JSON fixed vectors"
\<close>

end
