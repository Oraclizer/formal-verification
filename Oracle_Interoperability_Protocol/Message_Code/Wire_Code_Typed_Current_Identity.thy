theory Wire_Code_Typed_Current_Identity
  imports Wire_Code_Typed_Summary_Check
begin

definition code_typed_model_identity :: "unit \<Rightarrow> integer list list" where
  "code_typed_model_identity = (\<lambda>oip_identity_ignored.
    map (map integer_of_nat \<circ> code_json_ascii)
      [''1'',''intinf-wire-values-v2'',''wire-v6-general-31-values'',
       ''OIP_Wire_Oracle.code_typed_transport_flat_oracle'',''HOL-Library.Code_Target_Nat'',
       ''28500a91beb9478d3de97ed0d9a2913bf7ea3202a5b546627e02df53b998b207''])"

lemma the_current_typed_identity_has_exactly_six_fields:
  "length (code_typed_model_identity ()) = 6"
  by (simp add: code_typed_model_identity_def)

lemma the_current_typed_identity_binds_the_selected_source_epoch:
  "last (code_typed_model_identity ()) = map integer_of_nat
    (code_json_ascii ''28500a91beb9478d3de97ed0d9a2913bf7ea3202a5b546627e02df53b998b207'')"
  by (simp add: code_typed_model_identity_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    the_current_typed_identity_has_exactly_six_fields
    the_current_typed_identity_binds_the_selected_source_epoch})
  then () else error "Unexpected oracle in selected source epoch typed identity"
\<close>

text \<open>
  This parameterless identity records the interface schema, integer ABI,
  semantic scope, entry point, natural-number interpretation and selected
  source epoch. Its fingerprint is a fixed constant rather than a runtime
  argument. It is independent of other identity constants. An identity
  value alone does not establish artifact origin or implementation
  conformance.
\<close>

end
