theory Wire_Code_Response_Executable_Names
  imports Wire_Code_Response_Executable_Check
begin

code_identifier
  constant code_exec_egress_queries_flat \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_egress_queries_flat"
| constant code_exec_encode_boundary_queries_flat \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_encode_boundary_queries_flat"
| constant code_exec_egress_flat_oracle \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_egress_flat_oracle"
| constant code_exec_encode_boundary_flat_oracle \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_encode_boundary_flat_oracle"
| constant code_exec_egress_prefix_flat \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_egress_prefix_flat"
| constant code_exec_encode_boundary_prefix_flat \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_encode_boundary_prefix_flat"
| constant code_exec_egress_and_admit_flat_oracle \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_egress_and_admit_flat_oracle"

text \<open>
  These are the official generator's mandatory identifiers for new proved
  helpers. No old identifier/rule or generated ML implementation is edited.
  External module/function/argument/result ABI names remain unchanged.
\<close>

end
