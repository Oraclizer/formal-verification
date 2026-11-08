theory Wire_Code_Response_Selected_Prefix
  imports Wire_Code_Response_Selected_Sender
begin

definition code_exec_prefix_selected where
  "code_exec_prefix_selected = (\<lambda>(oip_exec_selected_mode :: nat option) oip_full_context oip_full_observation
      oip_full_original oip_full_call oip_full_hashes oip_full_signatures.
    let (oip_full_number,oip_full_position) = response_fixed_result oip_full_observation;
        oip_full_base = ((replicate 14 [])[0 :=
          [oip_full_number,if oip_full_position = None then 0 else 1,
            (case oip_full_position of None \<Rightarrow> 0 | Some oip_full_optional_position \<Rightarrow> oip_full_optional_position)]])
          [3 := encode_wire_core (packet_core oip_full_original)]
    in (case response_fixed_words oip_full_call (response_fixed_result oip_full_observation) of
         None \<Rightarrow> oip_full_base
       | Some (oip_full_kind,oip_full_code,oip_full_commit,oip_full_words) \<Rightarrow>
           (let oip_full_with_words = oip_full_base[1 := oip_full_words]
            in (case oip_exec_selected_mode of
                 None \<Rightarrow> oip_full_with_words
               | Some oip_full_atomicity \<Rightarrow>
                   (let oip_full_binding_message = response_fixed_binding_preimage
                         (encode_wire_core (packet_core oip_full_original)) oip_full_atomicity oip_full_words;
                        oip_full_with_binding =
                          (oip_full_with_words[2 := [oip_full_atomicity]])[4 := oip_full_binding_message]
                    in (case code_full_lookup_hash oip_full_hashes oip_full_binding_message of
                         None \<Rightarrow> oip_full_with_binding
                       | Some oip_full_binding \<Rightarrow>
                           (let oip_full_with_digest = oip_full_with_binding[5 := oip_full_binding]
                            in (if \<not> response_fixed_channel_current (full_response_config oip_full_context)
                                  (full_response_channel oip_full_context)
                                then oip_full_with_digest
                                else (case full_parameters_clock oip_full_context of
                                       None \<Rightarrow> oip_full_with_digest
                                     | Some oip_full_issued \<Rightarrow>
                                         (let oip_full_uuid_message = response_fixed_uuid_preimage
                                               (full_response_config oip_full_context) oip_full_binding oip_full_issued;
                                              oip_full_with_uuid_message = oip_full_with_digest[6 := oip_full_uuid_message]
                                          in (case code_full_lookup_hash oip_full_hashes oip_full_uuid_message of
                                               None \<Rightarrow> oip_full_with_uuid_message
                                             | Some oip_full_uuid_digest \<Rightarrow>
                                                 code_full_prefix_after_uuid oip_full_context
                                                   (packet_core oip_full_original) oip_full_atomicity oip_full_words
                                                   oip_full_binding oip_full_hashes oip_full_signatures
                                                   (oip_full_with_uuid_message[7 := oip_full_uuid_digest]))))))))))))"

lemma code_exec_prefix_selected_is_original:
  fixes oip_exec_selected_mode :: "nat option"
  assumes oip_exec_mode_matches: "oip_exec_selected_mode = response_fixed_atomicity (full_response_channel oip_full_context)"
  shows "code_exec_prefix_selected oip_exec_selected_mode oip_full_context oip_full_observation oip_full_original
      oip_full_call oip_full_hashes oip_full_signatures =
    code_full_prefix_selected oip_full_context oip_full_observation oip_full_original
      oip_full_call oip_full_hashes oip_full_signatures"
  using oip_exec_mode_matches
  by (simp add: code_exec_prefix_selected_def code_full_prefix_selected_def Let_def
      cong: option.case_cong prod.case_cong if_cong)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms code_exec_prefix_selected_is_original})
  then () else error "Unexpected oracle in selected-mode response prefix"
\<close>

end
