theory Wire_Code_Response_Executable_Check
  imports Wire_Code_Response_Executable_ABI
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    the_list_atomicity_is_the_existing_list_boundary_value
    a_parsed_sender_supplies_the_same_exact_atomicity
    code_exec_original_preflight_is_original
    code_exec_fixed_encode_is_original
    code_exec_received_encode_is_original
    code_exec_original_selection_is_original
    code_exec_selected_sender_queries_is_original
    code_exec_sender_queries_is_original
    code_exec_sender_is_original
    code_exec_boundary_sender_is_original
    code_exec_without_result_is_original
    code_exec_prefix_selected_is_original
    code_exec_queries_integer_is_original
    code_exec_sender_integer_is_original
    code_exec_prefix_integer_is_original
    code_exec_egress_queries_flat_is_original
    code_exec_encode_boundary_queries_flat_is_original
    code_exec_egress_flat_oracle_is_original
    code_exec_encode_boundary_flat_oracle_is_original
    code_exec_egress_prefix_flat_is_original
    code_exec_encode_boundary_prefix_flat_is_original
    code_exec_egress_and_admit_flat_oracle_is_original})
  then () else error "Unexpected oracle in finite-list executable full response"
\<close>

text \<open>
  This checks new helper equivalences only. No old function/code equation,
  datatype or library instance is replaced. Public frontends have no added
  argument or condition; every internal scalar premise comes from the
  existing successful integer context constructor and its finite getter.
\<close>

end
