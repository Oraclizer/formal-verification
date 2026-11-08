theory Wire_Code_Response_Executable_ABI
  imports Wire_Code_Response_Selected_Prefix
begin

definition code_exec_queries_integer ::
  "bool \<Rightarrow> integer list list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow> (integer \<times> integer list list)" where
  "code_exec_queries_integer = (\<lambda>oip_full_include_original oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows.
    (case code_full_sender_input oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows of
       None \<Rightarrow> (-1,[])
     | Some (oip_full_context,oip_full_observation,oip_full_bytes,oip_full_hashes,oip_full_signatures,oip_full_verifications) \<Rightarrow>
         (let oip_exec_mode_value = code_response_list_atomicity ((map (map nat_of_integer) oip_full_rows) ! 2)
          in (case oip_full_observation of
               None \<Rightarrow>
                 (if \<not> oip_full_include_original then (-1,[])
                  else (case code_exec_original_selection oip_exec_mode_value oip_full_context oip_full_bytes oip_full_verifications of
                          (Some oip_full_selected,oip_full_queries) \<Rightarrow> (-1,[])
                        | (None,oip_full_queries) \<Rightarrow> (0,map (map integer_of_nat) oip_full_queries)))
             | Some oip_full_actual \<Rightarrow>
                 (0,map (map integer_of_nat) (code_exec_sender_queries oip_exec_mode_value oip_full_include_original oip_full_context oip_full_actual oip_full_bytes oip_full_hashes oip_full_signatures oip_full_verifications))))))"

lemma code_exec_queries_integer_is_original:
  "code_exec_queries_integer oip_full_include_original oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows = code_full_queries_integer oip_full_include_original oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows"
proof (cases "code_full_sender_input oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows")
  case None
  then show ?thesis by (simp add: code_exec_queries_integer_def code_full_queries_integer_def)
next
  case (Some oip_exec_bundle)
  obtain oip_exec_context oip_exec_observation oip_exec_bytes oip_exec_hashes oip_exec_signatures oip_exec_verifications
  where oip_exec_bundle: "oip_exec_bundle = (oip_exec_context,oip_exec_observation,oip_exec_bytes,oip_exec_hashes,oip_exec_signatures,oip_exec_verifications)"
    by (cases oip_exec_bundle rule: prod_cases6) blast
  have oip_exec_parsed: "code_full_sender_input oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows = Some (oip_exec_context,oip_exec_observation,oip_exec_bytes,oip_exec_hashes,oip_exec_signatures,oip_exec_verifications)"
    using Some oip_exec_bundle by simp
  have oip_exec_mode_matches: "code_response_list_atomicity ((map (map nat_of_integer) oip_full_rows) ! 2) =
      response_fixed_atomicity (full_response_channel oip_exec_context)"
    using a_parsed_sender_supplies_the_same_exact_atomicity[OF oip_exec_parsed] by (rule sym)
  show ?thesis
    using oip_exec_parsed
    by (simp add: code_exec_queries_integer_def code_full_queries_integer_def Let_def code_exec_original_selection_is_original[OF oip_exec_mode_matches] code_exec_sender_queries_is_original[OF oip_exec_mode_matches]
      cong: sum.case_cong option.case_cong prod.case_cong if_cong)
qed

definition code_exec_sender_integer ::
  "bool \<Rightarrow> integer list list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow> (integer \<times> integer list list)" where
  "code_exec_sender_integer = (\<lambda>oip_full_include_original oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows.
    (case code_full_sender_input oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows of
       None \<Rightarrow> (-1,[])
     | Some (oip_full_context,oip_full_observation,oip_full_bytes,oip_full_hashes,oip_full_signatures,oip_full_verifications) \<Rightarrow>
         (let oip_exec_mode_value = code_response_list_atomicity ((map (map nat_of_integer) oip_full_rows) ! 2)
          in (case oip_full_observation of
               None \<Rightarrow>
                 (if oip_full_include_original then (code_exec_without_result oip_exec_mode_value oip_full_context oip_full_bytes oip_full_verifications :: integer \<times> integer list list) else (-1,[]))
             | Some oip_full_actual \<Rightarrow>
                 (if code_exec_sender_queries oip_exec_mode_value oip_full_include_original oip_full_context oip_full_actual oip_full_bytes oip_full_hashes oip_full_signatures oip_full_verifications \<noteq> [] then (-2,[])
                  else code_full_pack_sender oip_full_context oip_full_hashes
                    (if oip_full_include_original then code_exec_sender oip_exec_mode_value oip_full_context oip_full_actual oip_full_bytes oip_full_hashes oip_full_signatures oip_full_verifications
                     else code_exec_boundary_sender oip_exec_mode_value oip_full_context oip_full_actual oip_full_bytes oip_full_hashes oip_full_signatures oip_full_verifications))))))"

lemma code_exec_sender_integer_is_original:
  "code_exec_sender_integer oip_full_include_original oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows = code_full_sender_integer oip_full_include_original oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows"
proof (cases "code_full_sender_input oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows")
  case None
  then show ?thesis by (simp add: code_exec_sender_integer_def code_full_sender_integer_def)
next
  case (Some oip_exec_bundle)
  obtain oip_exec_context oip_exec_observation oip_exec_bytes oip_exec_hashes oip_exec_signatures oip_exec_verifications
  where oip_exec_bundle: "oip_exec_bundle = (oip_exec_context,oip_exec_observation,oip_exec_bytes,oip_exec_hashes,oip_exec_signatures,oip_exec_verifications)"
    by (cases oip_exec_bundle rule: prod_cases6) blast
  have oip_exec_parsed: "code_full_sender_input oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows = Some (oip_exec_context,oip_exec_observation,oip_exec_bytes,oip_exec_hashes,oip_exec_signatures,oip_exec_verifications)"
    using Some oip_exec_bundle by simp
  have oip_exec_mode_matches: "code_response_list_atomicity ((map (map nat_of_integer) oip_full_rows) ! 2) =
      response_fixed_atomicity (full_response_channel oip_exec_context)"
    using a_parsed_sender_supplies_the_same_exact_atomicity[OF oip_exec_parsed] by (rule sym)
  show ?thesis
    using oip_exec_parsed
    by (simp add: code_exec_sender_integer_def code_full_sender_integer_def Let_def code_exec_without_result_is_original[OF oip_exec_mode_matches] code_exec_sender_queries_is_original[OF oip_exec_mode_matches] code_exec_sender_is_original[OF oip_exec_mode_matches] code_exec_boundary_sender_is_original[OF oip_exec_mode_matches]
      cong: sum.case_cong option.case_cong prod.case_cong if_cong)
qed

definition code_exec_prefix_integer ::
  "bool \<Rightarrow> integer list list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow> (integer \<times> integer list list)" where
  "code_exec_prefix_integer = (\<lambda>oip_full_include_original oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows.
    (case code_full_sender_input oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows of
       None \<Rightarrow> (-1,[])
     | Some (oip_full_context,oip_full_observation,oip_full_bytes,oip_full_hashes,oip_full_signatures,oip_full_verifications) \<Rightarrow>
         (let oip_exec_mode_value = code_response_list_atomicity ((map (map nat_of_integer) oip_full_rows) ! 2)
          in (case oip_full_observation of
               None \<Rightarrow>
                 (if \<not> oip_full_include_original then (-1,[])
                  else (case (code_exec_without_result oip_exec_mode_value oip_full_context oip_full_bytes oip_full_verifications :: integer \<times> integer list list) of
                          (oip_full_status,oip_full_output) \<Rightarrow>
                            (if oip_full_status = -1 \<or> oip_full_status = -2 then (oip_full_status,[]) else (0,[]))))
             | Some oip_full_actual \<Rightarrow>
                 (if code_exec_sender_queries oip_exec_mode_value oip_full_include_original oip_full_context oip_full_actual oip_full_bytes oip_full_hashes oip_full_signatures oip_full_verifications \<noteq> [] then (-2,[])
                  else (let oip_full_selected =
                          (if oip_full_include_original then fst (code_exec_original_selection oip_exec_mode_value oip_full_context oip_full_bytes oip_full_verifications)
                           else (case decode_wire_packet oip_full_bytes of
                                   None \<Rightarrow> None
                                 | Some oip_full_packet \<Rightarrow>
                                     (case code_response_caller (packet_core oip_full_packet) of
                                        Inl oip_full_reason \<Rightarrow> None
                                      | Inr oip_full_call \<Rightarrow> Some (oip_full_packet,oip_full_call))))
                        in (case oip_full_selected of
                             None \<Rightarrow> (0,[])
                           | Some (oip_full_packet,oip_full_call) \<Rightarrow>
                               (0,map (map integer_of_nat) (code_exec_prefix_selected oip_exec_mode_value oip_full_context oip_full_actual oip_full_packet oip_full_call oip_full_hashes oip_full_signatures)))))))))"

lemma code_exec_prefix_integer_is_original:
  "code_exec_prefix_integer oip_full_include_original oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows = code_full_prefix_integer oip_full_include_original oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows"
proof (cases "code_full_sender_input oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows")
  case None
  then show ?thesis by (simp add: code_exec_prefix_integer_def code_full_prefix_integer_def)
next
  case (Some oip_exec_bundle)
  obtain oip_exec_context oip_exec_observation oip_exec_bytes oip_exec_hashes oip_exec_signatures oip_exec_verifications
  where oip_exec_bundle: "oip_exec_bundle = (oip_exec_context,oip_exec_observation,oip_exec_bytes,oip_exec_hashes,oip_exec_signatures,oip_exec_verifications)"
    by (cases oip_exec_bundle rule: prod_cases6) blast
  have oip_exec_parsed: "code_full_sender_input oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows = Some (oip_exec_context,oip_exec_observation,oip_exec_bytes,oip_exec_hashes,oip_exec_signatures,oip_exec_verifications)"
    using Some oip_exec_bundle by simp
  have oip_exec_mode_matches: "code_response_list_atomicity ((map (map nat_of_integer) oip_full_rows) ! 2) =
      response_fixed_atomicity (full_response_channel oip_exec_context)"
    using a_parsed_sender_supplies_the_same_exact_atomicity[OF oip_exec_parsed] by (rule sym)
  show ?thesis
    using oip_exec_parsed
    by (simp add: code_exec_prefix_integer_def code_full_prefix_integer_def Let_def code_exec_without_result_is_original[OF oip_exec_mode_matches] code_exec_sender_queries_is_original[OF oip_exec_mode_matches] code_exec_original_selection_is_original[OF oip_exec_mode_matches] code_exec_prefix_selected_is_original[OF oip_exec_mode_matches]
      cong: sum.case_cong option.case_cong prod.case_cong if_cong)
qed

definition code_exec_egress_queries_flat ::
  "integer list list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow> (integer \<times> integer list list)" where
  "code_exec_egress_queries_flat = code_exec_queries_integer True"

lemma code_exec_egress_queries_flat_is_original:
  "code_exec_egress_queries_flat = code_response_egress_queries_flat"
  by (rule ext)+
    (simp add: code_exec_egress_queries_flat_def code_response_egress_queries_flat_def code_exec_queries_integer_is_original)

definition code_exec_encode_boundary_queries_flat ::
  "integer list list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow> (integer \<times> integer list list)" where
  "code_exec_encode_boundary_queries_flat = code_exec_queries_integer False"

lemma code_exec_encode_boundary_queries_flat_is_original:
  "code_exec_encode_boundary_queries_flat = code_response_encode_boundary_queries_flat"
  by (rule ext)+
    (simp add: code_exec_encode_boundary_queries_flat_def code_response_encode_boundary_queries_flat_def code_exec_queries_integer_is_original)

definition code_exec_egress_flat_oracle ::
  "integer list list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow> (integer \<times> integer list list)" where
  "code_exec_egress_flat_oracle = code_exec_sender_integer True"

lemma code_exec_egress_flat_oracle_is_original:
  "code_exec_egress_flat_oracle = code_response_egress_flat_oracle"
  by (rule ext)+
    (simp add: code_exec_egress_flat_oracle_def code_response_egress_flat_oracle_def code_exec_sender_integer_is_original)

definition code_exec_encode_boundary_flat_oracle ::
  "integer list list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow> (integer \<times> integer list list)" where
  "code_exec_encode_boundary_flat_oracle = code_exec_sender_integer False"

lemma code_exec_encode_boundary_flat_oracle_is_original:
  "code_exec_encode_boundary_flat_oracle = code_response_encode_boundary_flat_oracle"
  by (rule ext)+
    (simp add: code_exec_encode_boundary_flat_oracle_def code_response_encode_boundary_flat_oracle_def code_exec_sender_integer_is_original)

definition code_exec_egress_prefix_flat ::
  "integer list list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow> (integer \<times> integer list list)" where
  "code_exec_egress_prefix_flat = code_exec_prefix_integer True"

lemma code_exec_egress_prefix_flat_is_original:
  "code_exec_egress_prefix_flat = code_response_egress_prefix_flat"
  by (rule ext)+
    (simp add: code_exec_egress_prefix_flat_def code_response_egress_prefix_flat_def code_exec_prefix_integer_is_original)

definition code_exec_encode_boundary_prefix_flat ::
  "integer list list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow> (integer \<times> integer list list)" where
  "code_exec_encode_boundary_prefix_flat = code_exec_prefix_integer False"

lemma code_exec_encode_boundary_prefix_flat_is_original:
  "code_exec_encode_boundary_prefix_flat = code_response_encode_boundary_prefix_flat"
  by (rule ext)+
    (simp add: code_exec_encode_boundary_prefix_flat_def code_response_encode_boundary_prefix_flat_def code_exec_prefix_integer_is_original)

definition code_exec_egress_and_admit_flat_oracle ::
  "integer list list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow>
    (integer \<times> integer list list \<times> integer \<times> integer list)" where
  "code_exec_egress_and_admit_flat_oracle = (\<lambda>oip_full_sender_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows oip_full_client_rows oip_full_client_verify_rows.
    let (oip_full_sender_status,oip_full_output) =
      code_exec_egress_flat_oracle oip_full_sender_rows oip_full_mode oip_full_reply oip_full_retained_present
        oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows
    in if oip_full_sender_status \<noteq> 0 then (oip_full_sender_status,oip_full_output,-3,[])
    else let (oip_full_client_status,oip_full_client_output) =
      code_response_admit_flat_oracle oip_full_client_rows oip_full_original (oip_full_output ! 12) oip_full_client_verify_rows
    in (oip_full_sender_status,oip_full_output,oip_full_client_status,oip_full_client_output))"

lemma code_exec_egress_and_admit_flat_oracle_is_original:
  "code_exec_egress_and_admit_flat_oracle = code_response_egress_and_admit_flat_oracle"
  by (rule ext)+
    (simp add: code_exec_egress_and_admit_flat_oracle_def code_response_egress_and_admit_flat_oracle_def code_exec_egress_flat_oracle_is_original)

text \<open>
  Only the new constants above receive their own ordinary definition code
  equations. Original definitions and code equations are not dropped,
  replaced or printed differently. Every public integer entry is proved
  equal on all its original inputs; the finite mode comes from its existing
  successful parser/constructor rather than an added input assumption.
\<close>

end
