theory Wire_Code_Response_Current_Export
  imports Wire_Code_Response_Current_Identity
begin

export_code code_response_result_flat_oracle
  code_response_binding_flat_oracle code_response_uuid_preimage_flat_oracle
  code_exec_egress_queries_flat code_exec_encode_boundary_queries_flat
  code_exec_egress_flat_oracle code_exec_encode_boundary_flat_oracle
  code_exec_egress_prefix_flat code_exec_encode_boundary_prefix_flat
  code_response_admit_queries_flat code_response_admit_flat_oracle
  code_exec_egress_and_admit_flat_oracle code_response_full_model_identity
  in SML module_name OIP_Wire_Response_Boundary file_prefix "oip_wire_response_current"

text \<open>
  Fresh execution helpers are mapped to the unchanged external ABI by the
  official code_identifier declarations. Only the new definition code
  equations are used for the specialization. No nat finite/enum instance,
  library patch, old code equation replacement or generated ML edit exists.
\<close>

end
