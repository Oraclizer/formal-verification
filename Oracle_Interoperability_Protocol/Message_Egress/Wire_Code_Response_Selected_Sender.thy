theory Wire_Code_Response_Selected_Sender
  imports Wire_Code_Response_Selected_Queries
begin

definition code_exec_sender where
  "code_exec_sender = (\<lambda>(oip_exec_selected_mode :: nat option) oip_full_context oip_full_observation oip_full_original
      oip_full_hashes oip_full_signatures oip_full_verifications.
    code_exec_received_encode oip_exec_selected_mode (code_full_hash oip_full_hashes)
      (code_full_sign oip_full_signatures (response_channel_local_key (full_response_channel oip_full_context))) ()
      (code_full_verify oip_full_verifications)
      (full_response_config oip_full_context) (full_response_channel oip_full_context) (full_response_site oip_full_context)
      (full_parameters_clock oip_full_context) (full_signing_clock oip_full_context)
      oip_full_original oip_full_observation (full_response_frame_limit oip_full_context))"

lemma code_exec_sender_is_original:
  fixes oip_exec_selected_mode :: "nat option"
  assumes oip_exec_mode_matches: "oip_exec_selected_mode = response_fixed_atomicity (full_response_channel oip_full_context)"
  shows "code_exec_sender oip_exec_selected_mode oip_full_context oip_full_observation oip_full_original
      oip_full_hashes oip_full_signatures oip_full_verifications =
    code_full_sender oip_full_context oip_full_observation oip_full_original
      oip_full_hashes oip_full_signatures oip_full_verifications"
  by (simp only: code_exec_sender_def code_full_sender_def
      code_exec_received_encode_is_original[OF oip_exec_mode_matches])

definition code_exec_boundary_sender where
  "code_exec_boundary_sender = (\<lambda>(oip_exec_selected_mode :: nat option) oip_full_context oip_full_observation oip_full_bytes
      oip_full_hashes oip_full_signatures oip_full_verifications.
    (case decode_wire_packet oip_full_bytes of
       None \<Rightarrow> Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Format)
     | Some oip_full_original \<Rightarrow>
         (case code_response_caller (packet_core oip_full_original) of
            Inl oip_full_reason \<Rightarrow> Inl (Response_Fixed_Encoding_Refused oip_full_reason)
          | Inr oip_full_call \<Rightarrow>
              code_exec_fixed_encode oip_exec_selected_mode (code_full_hash oip_full_hashes)
                (code_full_sign oip_full_signatures (response_channel_local_key (full_response_channel oip_full_context))) ()
                (code_full_verify oip_full_verifications)
                (full_response_config oip_full_context) (full_response_channel oip_full_context)
                (full_parameters_clock oip_full_context) (full_signing_clock oip_full_context)
                (packet_core oip_full_original) oip_full_call oip_full_observation
                (full_response_frame_limit oip_full_context))))"

lemma code_exec_boundary_sender_is_original:
  fixes oip_exec_selected_mode :: "nat option"
  assumes oip_exec_mode_matches: "oip_exec_selected_mode = response_fixed_atomicity (full_response_channel oip_full_context)"
  shows "code_exec_boundary_sender oip_exec_selected_mode oip_full_context oip_full_observation oip_full_bytes
      oip_full_hashes oip_full_signatures oip_full_verifications =
    code_full_boundary_sender oip_full_context oip_full_observation oip_full_bytes
      oip_full_hashes oip_full_signatures oip_full_verifications"
  by (simp only: code_exec_boundary_sender_def code_full_boundary_sender_def
      code_exec_fixed_encode_is_original[OF oip_exec_mode_matches]
      cong: option.case_cong sum.case_cong if_cong)

definition code_exec_without_result where
  "code_exec_without_result = (\<lambda>(oip_exec_selected_mode :: nat option) oip_full_context oip_full_bytes oip_full_verifications.
    (case code_exec_original_selection oip_exec_selected_mode oip_full_context oip_full_bytes oip_full_verifications of
       (oip_full_selected,oip_full_queries) \<Rightarrow>
         (if oip_full_queries \<noteq> [] then (-2,[])
          else (case code_exec_original_preflight oip_exec_selected_mode (full_response_config oip_full_context)
                  (full_response_channel oip_full_context) (full_response_site oip_full_context)
                  (code_full_verify oip_full_verifications) (full_response_frame_limit oip_full_context) oip_full_bytes of
                  Inl oip_full_reason \<Rightarrow> (integer_of_nat (code_transport_refusal_number oip_full_reason),[])
                | Inr oip_full_original \<Rightarrow> (-1,[])))))"

lemma code_exec_without_result_is_original:
  fixes oip_exec_selected_mode :: "nat option"
  assumes oip_exec_mode_matches: "oip_exec_selected_mode = response_fixed_atomicity (full_response_channel oip_full_context)"
  shows "code_exec_without_result oip_exec_selected_mode oip_full_context oip_full_bytes oip_full_verifications =
    code_full_without_result oip_full_context oip_full_bytes oip_full_verifications"
  by (simp only: code_exec_without_result_def code_full_without_result_def
      code_exec_original_selection_is_original[OF oip_exec_mode_matches]
      code_exec_original_preflight_is_original[OF oip_exec_mode_matches]
      cong: prod.case_cong sum.case_cong option.case_cong if_cong)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    code_exec_sender_is_original
    code_exec_boundary_sender_is_original
    code_exec_without_result_is_original})
  then () else error "Unexpected oracle in selected-mode full sender"
\<close>

end
