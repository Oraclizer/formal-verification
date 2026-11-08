theory Wire_Code_Response_List_Atomicity_Check
  imports Wire_Code_Response_List_Atomicity
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    the_list_atomicity_is_the_existing_list_boundary_value
    the_constructed_channel_uses_exactly_the_list_atomicity
    a_constructed_context_has_the_same_exact_atomicity
    a_parsed_context_has_the_same_exact_atomicity
    an_integer_context_has_the_same_exact_atomicity
    a_parsed_sender_supplies_the_same_exact_atomicity})
  then () else error "Unexpected oracle in finite provider-list atomicity"
\<close>

end
