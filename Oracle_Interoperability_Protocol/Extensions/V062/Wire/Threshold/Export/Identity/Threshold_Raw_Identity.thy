theory Threshold_Raw_Identity
  imports "OIP_P19_Threshold_Export.P19_Threshold_Export"
begin

text \<open>The raw packet export consumes the selected roster and exact
key and signature observations from its caller. The export retains the
verified parser and threshold checks, including the distinction between
unavailable observations and a protocol refusal.\<close>

definition threshold_raw_packet ::
  "integer \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
   (integer \<times> integer list) list \<Rightarrow> (integer list \<times> bool) list \<Rightarrow>
   (integer list \<times> integer list \<times> integer list \<times> bool) list \<Rightarrow>
   integer list \<Rightarrow> (integer list \<times> integer list list) option" where
  "threshold_raw_packet = p19_export_integer_packet"

lemma threshold_raw_packet_reuses_the_verified_export:
  "threshold_raw_packet = p19_export_integer_packet"
  by (rule threshold_raw_packet_def)

definition threshold_raw_model_identity :: "unit \<Rightarrow> integer list list" where
  "threshold_raw_model_identity ignored =
    map (map integer_of_nat \<circ> code_json_ascii)
      [''1'', ''intinf-threshold-raw-v1'', ''wire-v6-threshold-raw-observed-primitives'',
       ''OIP_Threshold_Raw_ABI.threshold_raw_packet'', ''HOL-Library.Code_Target_Nat'',
       ''7edc3b1dd127d9ad0e30ff6f2dab57eb3bf624ea60b6b588413534fd148d33a8'']"

lemma threshold_raw_identity_binds_scope_entrypoint_and_source:
  "length (threshold_raw_model_identity ()) = 6"
  "threshold_raw_model_identity () ! 2 =
    map integer_of_nat (code_json_ascii ''wire-v6-threshold-raw-observed-primitives'')"
  "threshold_raw_model_identity () ! 3 =
    map integer_of_nat (code_json_ascii ''OIP_Threshold_Raw_ABI.threshold_raw_packet'')"
  "last (threshold_raw_model_identity ()) =
    map integer_of_nat (code_json_ascii ''7edc3b1dd127d9ad0e30ff6f2dab57eb3bf624ea60b6b588413534fd148d33a8'')"
  by (simp_all add: threshold_raw_model_identity_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      threshold_raw_packet_reuses_the_verified_export
      threshold_raw_identity_binds_scope_entrypoint_and_source
      p19_export_success_reuses_the_verified_threshold_contract
      a_strict_observation_is_bound_to_all_three_exact_inputs
      p19_required_strict_metadata_failure_is_not_signature_refusal})
  then () else error "Unexpected oracle in the threshold raw artifact"
\<close>

export_code threshold_raw_packet threshold_raw_model_identity
  in SML module_name OIP_Threshold_Raw_ABI file_prefix "oip_threshold_raw_abi"

end
