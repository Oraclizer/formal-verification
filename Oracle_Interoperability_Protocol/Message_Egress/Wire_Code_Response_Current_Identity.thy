theory Wire_Code_Response_Current_Identity
  imports Wire_Code_Response_Executable_Names
begin

definition code_response_full_model_identity :: "unit \<Rightarrow> integer list list" where
  "code_response_full_model_identity = (\<lambda>oip_identity_ignored.
    map (map integer_of_nat \<circ> code_json_ascii)
      [''1'',''intinf-response-full-v1'',''wire-response-sender-client-v1'',
       ''OIP_Wire_Response_Boundary.code_response_egress_flat_oracle'',''HOL-Library.Code_Target_Nat'',
       ''28500a91beb9478d3de97ed0d9a2913bf7ea3202a5b546627e02df53b998b207''])"

lemma the_current_full_identity_has_exactly_six_fields:
  "length (code_response_full_model_identity ()) = 6"
  by (simp add: code_response_full_model_identity_def)

lemma the_current_full_identity_binds_the_selected_source_epoch:
  "last (code_response_full_model_identity ()) = map integer_of_nat
    (code_json_ascii ''28500a91beb9478d3de97ed0d9a2913bf7ea3202a5b546627e02df53b998b207'')"
  by (simp add: code_response_full_model_identity_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    the_current_full_identity_has_exactly_six_fields
    the_current_full_identity_binds_the_selected_source_epoch})
  then () else error "Unexpected oracle in selected source epoch full identity"
\<close>

text \<open>
  This parameterless six-field identity records the schema, integer ABI,
  sender/client scope, entry point, natural-number interpretation and
  selected source epoch. It is independent of the Typed constant.
  Identity values do not by themselves establish artifact origin or
  implementation conformance.
\<close>

end
