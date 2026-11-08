theory Wire_Code_Response_Selected_Received
  imports Wire_Code_Response_Selected_Encode
begin

definition code_exec_received_encode where
  "code_exec_received_encode = (\<lambda>(oip_exec_selected_mode :: nat option) oip_exec_low_hash oip_exec_low_curve_sign oip_exec_low_signing_key oip_exec_low_curve_verify oip_exec_low_config oip_exec_low_channel oip_exec_low_site oip_exec_low_parameters_clock oip_exec_low_signing_clock oip_exec_low_original_bytes oip_exec_low_observation oip_exec_low_frame_limit.
    (case code_exec_original_preflight oip_exec_selected_mode oip_exec_low_config oip_exec_low_channel oip_exec_low_site oip_exec_low_curve_verify oip_exec_low_frame_limit oip_exec_low_original_bytes of
       Inl oip_exec_low_reason \<Rightarrow> Inl (Response_Fixed_Encoding_Refused oip_exec_low_reason)
     | Inr (oip_exec_low_original,oip_exec_low_call_id) \<Rightarrow> code_exec_fixed_encode oip_exec_selected_mode oip_exec_low_hash oip_exec_low_curve_sign oip_exec_low_signing_key oip_exec_low_curve_verify oip_exec_low_config oip_exec_low_channel
         oip_exec_low_parameters_clock oip_exec_low_signing_clock (packet_core oip_exec_low_original) oip_exec_low_call_id oip_exec_low_observation oip_exec_low_frame_limit))"

lemma code_exec_received_encode_is_original:
  fixes oip_exec_selected_mode :: "nat option"
  assumes oip_exec_mode_matches: "oip_exec_selected_mode = response_fixed_atomicity oip_exec_low_channel"
  shows "code_exec_received_encode oip_exec_selected_mode oip_exec_low_hash oip_exec_low_curve_sign oip_exec_low_signing_key oip_exec_low_curve_verify oip_exec_low_config oip_exec_low_channel oip_exec_low_site oip_exec_low_parameters_clock oip_exec_low_signing_clock oip_exec_low_original_bytes oip_exec_low_observation oip_exec_low_frame_limit =
    response_fixed_encode_for_received_original oip_exec_low_hash oip_exec_low_curve_sign oip_exec_low_signing_key oip_exec_low_curve_verify oip_exec_low_config oip_exec_low_channel oip_exec_low_site oip_exec_low_parameters_clock oip_exec_low_signing_clock oip_exec_low_original_bytes oip_exec_low_observation oip_exec_low_frame_limit"
proof -
  have oip_exec_preflight_same:
    "code_exec_original_preflight oip_exec_selected_mode oip_exec_low_config oip_exec_low_channel oip_exec_low_site
       oip_exec_low_curve_verify oip_exec_low_frame_limit oip_exec_low_original_bytes =
     response_fixed_original_preflight oip_exec_low_config oip_exec_low_channel oip_exec_low_site
       oip_exec_low_curve_verify oip_exec_low_frame_limit oip_exec_low_original_bytes"
    by (rule code_exec_original_preflight_is_original[OF oip_exec_mode_matches])
  show ?thesis
  proof (cases "response_fixed_original_preflight oip_exec_low_config oip_exec_low_channel oip_exec_low_site
      oip_exec_low_curve_verify oip_exec_low_frame_limit oip_exec_low_original_bytes")
    case (Inl oip_exec_refusal)
    then show ?thesis using oip_exec_preflight_same
      by (simp add: code_exec_received_encode_def response_fixed_encode_for_received_original_def)
  next
    case (Inr oip_exec_pair)
    obtain oip_exec_packet oip_exec_call
    where oip_exec_pair: "oip_exec_pair = (oip_exec_packet,oip_exec_call)"
      by (cases oip_exec_pair) auto
    have oip_exec_encode_same:
      "code_exec_fixed_encode oip_exec_selected_mode oip_exec_low_hash oip_exec_low_curve_sign
         oip_exec_low_signing_key oip_exec_low_curve_verify oip_exec_low_config oip_exec_low_channel
         oip_exec_low_parameters_clock oip_exec_low_signing_clock (packet_core oip_exec_packet) oip_exec_call
         oip_exec_low_observation oip_exec_low_frame_limit =
       response_fixed_encode oip_exec_low_hash oip_exec_low_curve_sign oip_exec_low_signing_key oip_exec_low_curve_verify
         oip_exec_low_config oip_exec_low_channel oip_exec_low_parameters_clock oip_exec_low_signing_clock
         (packet_core oip_exec_packet) oip_exec_call oip_exec_low_observation oip_exec_low_frame_limit"
      by (rule code_exec_fixed_encode_is_original[OF oip_exec_mode_matches])
    show ?thesis using Inr oip_exec_pair oip_exec_preflight_same oip_exec_encode_same
      by (simp add: code_exec_received_encode_def response_fixed_encode_for_received_original_def)
  qed
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms code_exec_received_encode_is_original})
  then () else error "Unexpected oracle in selected-mode original sender"
\<close>

end
