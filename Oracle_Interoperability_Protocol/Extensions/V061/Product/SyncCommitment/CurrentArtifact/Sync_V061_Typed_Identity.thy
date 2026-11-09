theory Sync_V061_Typed_Identity
  imports "OIP_Sync_V061_Position_Nested_IR.Sync_V061_Nested_IR"
begin

definition sync_v061_typed_model_identity :: "unit \<Rightarrow> integer list list" where
  "sync_v061_typed_model_identity = (\<lambda>ignored.
    map (map integer_of_nat \<circ> code_json_ascii) [''1'',''intinf-wire-values-v2'',''wire-v6-general-33-values'',''OIP_Wire_Oracle_V061.sync_v061_nested_transport_flat'',''HOL-Library.Code_Target_Nat'',''9fe7621c9aa01a48c90cecf91829290682dc63d2d7738571b872186f30a98c5c''])"

lemma sync_v061_typed_identity_has_six_fields:
  "length (sync_v061_typed_model_identity ()) = 6"
  by (simp add: sync_v061_typed_model_identity_def)

lemma sync_v061_typed_identity_binds_its_consumer_source:
  "last (sync_v061_typed_model_identity ()) = map integer_of_nat (code_json_ascii ''9fe7621c9aa01a48c90cecf91829290682dc63d2d7738571b872186f30a98c5c'')"
  by (simp add: sync_v061_typed_model_identity_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_v061_typed_identity_has_six_fields
      sync_v061_typed_identity_binds_its_consumer_source})
  then () else error "Unexpected oracle in the v0.6.1 typed identity"
\<close>

export_code sync_v061_nested_transport_flat sync_v061_typed_model_identity
  in SML module_name OIP_Wire_Oracle_V061 file_prefix "oip_wire_values_v061_current"

end
