theory Wire_Code_Response_Selected_Queries
  imports Wire_Code_Response_Selected_Received
begin

definition code_exec_original_selection where
  "code_exec_original_selection = (\<lambda>(oip_exec_selected_mode :: nat option) oip_full_context oip_full_bytes oip_full_verifications.
    let oip_full_channel = full_response_channel oip_full_context;
        oip_full_attempt = code_exec_original_preflight oip_exec_selected_mode (full_response_config oip_full_context)
          oip_full_channel (full_response_site oip_full_context) (code_full_probe_verify oip_full_verifications)
          (full_response_frame_limit oip_full_context) oip_full_bytes
    in (case oip_full_attempt of
         Inr oip_full_selected \<Rightarrow> (Some oip_full_selected,[])
       | Inl oip_full_reason \<Rightarrow>
           (if oip_full_reason \<noteq> Invalid_Wire_Signature then (None,[])
            else (case decode_wire_packet oip_full_bytes of
                    None \<Rightarrow> (None,[])
                  | Some oip_full_original \<Rightarrow>
                      (if wire_signature_scheme (packet_core oip_full_original) = 2 \<or>
                          wire_signature_scheme (packet_core oip_full_original) \<notin>
                            negotiated_schemes (response_channel_profile oip_full_channel)
                       then (None,[])
                       else (None,code_full_need_verify oip_full_verifications
                         (response_channel_remote_key oip_full_channel)
                         (envelope_signing_bytes (packet_core oip_full_original))
                         (packet_signature oip_full_original)))))))"

lemma code_exec_original_selection_is_original:
  fixes oip_exec_selected_mode :: "nat option"
  assumes oip_exec_mode_matches: "oip_exec_selected_mode = response_fixed_atomicity (full_response_channel oip_full_context)"
  shows "code_exec_original_selection oip_exec_selected_mode oip_full_context oip_full_bytes oip_full_verifications =
    code_full_original_selection oip_full_context oip_full_bytes oip_full_verifications"
  by (simp only: code_exec_original_selection_def code_full_original_selection_def Let_def
      code_exec_original_preflight_is_original[OF oip_exec_mode_matches]
      cong: sum.case_cong option.case_cong if_cong)

definition code_exec_selected_sender_queries where
  "code_exec_selected_sender_queries = (\<lambda>(oip_exec_selected_mode :: nat option) oip_full_context oip_full_observation
      oip_full_original oip_full_call oip_full_hashes oip_full_signatures oip_full_verifications.
    (case response_fixed_words oip_full_call (response_fixed_result oip_full_observation) of
       None \<Rightarrow> []
     | Some (oip_full_kind,oip_full_number,oip_full_position,oip_full_words) \<Rightarrow>
         (case oip_exec_selected_mode of
            None \<Rightarrow> []
          | Some oip_full_atomicity \<Rightarrow>
              (let oip_full_binding_message = response_fixed_binding_preimage
                    (encode_wire_core (packet_core oip_full_original)) oip_full_atomicity oip_full_words
               in (case code_full_lookup_hash oip_full_hashes oip_full_binding_message of
                     None \<Rightarrow> [code_full_hash_query oip_full_binding_message]
                   | Some oip_full_binding \<Rightarrow> code_full_after_binding_queries oip_full_context
                       (packet_core oip_full_original) oip_full_atomicity oip_full_words oip_full_binding
                       oip_full_hashes oip_full_signatures oip_full_verifications)))))"

lemma code_exec_selected_sender_queries_is_original:
  fixes oip_exec_selected_mode :: "nat option"
  assumes oip_exec_mode_matches: "oip_exec_selected_mode = response_fixed_atomicity (full_response_channel oip_full_context)"
  shows "code_exec_selected_sender_queries oip_exec_selected_mode oip_full_context oip_full_observation oip_full_original
      oip_full_call oip_full_hashes oip_full_signatures oip_full_verifications =
    code_full_selected_sender_queries oip_full_context oip_full_observation oip_full_original
      oip_full_call oip_full_hashes oip_full_signatures oip_full_verifications"
  using oip_exec_mode_matches
  by (simp add: code_exec_selected_sender_queries_def code_full_selected_sender_queries_def Let_def
      cong: sum.case_cong option.case_cong if_cong)

definition code_exec_sender_queries where
  "code_exec_sender_queries = (\<lambda>(oip_exec_selected_mode :: nat option) oip_full_include_original oip_full_context
      oip_full_observation oip_full_bytes oip_full_hashes oip_full_signatures oip_full_verifications.
    if oip_full_include_original then
      (case code_exec_original_selection oip_exec_selected_mode oip_full_context oip_full_bytes oip_full_verifications of
         (None,oip_full_queries) \<Rightarrow> oip_full_queries
       | (Some (oip_full_original,oip_full_call),oip_full_queries) \<Rightarrow>
           code_exec_selected_sender_queries oip_exec_selected_mode oip_full_context oip_full_observation
             oip_full_original oip_full_call oip_full_hashes oip_full_signatures oip_full_verifications)
    else
      (case decode_wire_packet oip_full_bytes of
         None \<Rightarrow> []
       | Some oip_full_original \<Rightarrow>
           (case code_response_caller (packet_core oip_full_original) of
              Inl oip_full_reason \<Rightarrow> []
            | Inr oip_full_call \<Rightarrow>
                code_exec_selected_sender_queries oip_exec_selected_mode oip_full_context oip_full_observation
                  oip_full_original oip_full_call oip_full_hashes oip_full_signatures oip_full_verifications)))"

lemma code_exec_sender_queries_is_original:
  fixes oip_exec_selected_mode :: "nat option"
  assumes oip_exec_mode_matches: "oip_exec_selected_mode = response_fixed_atomicity (full_response_channel oip_full_context)"
  shows "code_exec_sender_queries oip_exec_selected_mode oip_full_include_original oip_full_context oip_full_observation
      oip_full_bytes oip_full_hashes oip_full_signatures oip_full_verifications =
    code_full_sender_queries oip_full_include_original oip_full_context oip_full_observation
      oip_full_bytes oip_full_hashes oip_full_signatures oip_full_verifications"
  by (simp only: code_exec_sender_queries_def code_full_sender_queries_def
      code_exec_original_selection_is_original[OF oip_exec_mode_matches]
      code_exec_selected_sender_queries_is_original[OF oip_exec_mode_matches]
      cong: sum.case_cong option.case_cong prod.case_cong if_cong)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    code_exec_original_selection_is_original
    code_exec_selected_sender_queries_is_original
    code_exec_sender_queries_is_original})
  then () else error "Unexpected oracle in selected-mode response queries"
\<close>

end
