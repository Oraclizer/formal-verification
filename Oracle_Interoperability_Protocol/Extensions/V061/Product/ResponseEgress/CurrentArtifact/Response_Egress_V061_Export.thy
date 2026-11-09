theory Response_Egress_V061_Export
  imports "OIP_Response_Egress_V061_Runtime_V7.Response_Egress_V061_ABI"
begin

definition response_v061_model_identity :: "unit \<Rightarrow> integer list list" where
  "response_v061_model_identity ignored = response_v061_identity_fields ''081861a0122d120ac7ff90b5aa363d9072e3824296b0f2687c78c515eeee7610''"

lemma response_v061_model_identity_has_the_bound_source:
  "length (response_v061_model_identity ()) = 6"
  "last (response_v061_model_identity ()) = map integer_of_nat (code_json_ascii ''081861a0122d120ac7ff90b5aa363d9072e3824296b0f2687c78c515eeee7610'')"
  by (simp_all add: response_v061_model_identity_def response_v061_identity_fields_def comp_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms response_v061_model_identity_has_the_bound_source})
  then () else error "Unexpected oracle in the v0.6.1 response identity"
\<close>

code_identifier constant response_v061_model_identity \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_full_model_identity"

export_code response_v061_result_flat_oracle
  code_response_binding_flat_oracle code_response_uuid_preimage_flat_oracle
  response_v061_egress_queries_flat response_v061_encode_boundary_queries_flat
  response_v061_egress_flat_oracle response_v061_encode_boundary_flat_oracle
  response_v061_egress_prefix_flat response_v061_encode_boundary_prefix_flat
  response_v061_admit_queries_flat response_v061_admit_flat_oracle
  response_v061_egress_and_admit_flat_oracle response_v061_model_identity
  in SML module_name OIP_Wire_Response_Boundary file_prefix "oip_wire_response_full_v061"

end
