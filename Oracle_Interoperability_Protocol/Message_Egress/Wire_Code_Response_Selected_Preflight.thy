theory Wire_Code_Response_Selected_Preflight
  imports Wire_Code_Response_List_Atomicity_Check
begin

definition code_exec_original_preflight where
  "code_exec_original_preflight = (\<lambda>(oip_exec_selected_mode :: nat option) oip_exec_low_config oip_exec_low_channel oip_exec_low_site oip_exec_low_curve_verify oip_exec_low_frame_limit oip_exec_low_bytes.
    code_original_response_preflight (response_channel_profile oip_exec_low_channel)
      (response_fixed_channel_guard oip_exec_low_config oip_exec_low_channel)
      (response_site_ordered_control oip_exec_low_site \<noteq> None)
      (response_site_security_ordered_profile oip_exec_low_site = Some (response_site_profile oip_exec_low_site))
      (fst (response_site_profile oip_exec_low_site)) oip_exec_low_frame_limit (oip_exec_selected_mode)
      (\<lambda>oip_exec_low_core oip_exec_low_preimage oip_exec_low_signature. oip_exec_low_curve_verify (response_channel_remote_key oip_exec_low_channel) oip_exec_low_preimage oip_exec_low_signature) oip_exec_low_bytes)"

lemma code_exec_original_preflight_is_original:
  fixes oip_exec_selected_mode :: "nat option"
  assumes oip_exec_mode_matches: "oip_exec_selected_mode = response_fixed_atomicity oip_exec_low_channel"
  shows "code_exec_original_preflight oip_exec_selected_mode oip_exec_low_config oip_exec_low_channel oip_exec_low_site oip_exec_low_curve_verify oip_exec_low_frame_limit oip_exec_low_bytes =
    response_fixed_original_preflight oip_exec_low_config oip_exec_low_channel oip_exec_low_site oip_exec_low_curve_verify oip_exec_low_frame_limit oip_exec_low_bytes"
  using oip_exec_mode_matches
  by (simp add: code_exec_original_preflight_def response_fixed_original_preflight_def Let_def 
    cong: sum.case_cong option.case_cong)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms code_exec_original_preflight_is_original})
  then () else error "Unexpected oracle in selected-mode original preflight"
\<close>

end
