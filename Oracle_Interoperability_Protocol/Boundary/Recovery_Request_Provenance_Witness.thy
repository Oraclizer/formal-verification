theory Recovery_Request_Provenance_Witness
  imports "Recovery_Request_Provenance_Word"
begin

definition state_has_ask_witness where
  "state_has_ask_witness step R0 requests R \<longleftrightarrow>
    (\<exists>word. requested_subsequence word requests \<and> R = run_product_action_word step word R0)"

lemma genesis_image_has_ask_witness [simp]:
  "state_has_ask_witness step R0 requests R0"
  unfolding state_has_ask_witness_def
proof (rule exI[of _ "[]"], rule conjI)
  show "requested_subsequence [] requests" by (rule requested_subsequence.empty)
  show "R0 = run_product_action_word step [] R0" by simp
qed

lemma ask_witness_append_right:
  assumes "state_has_ask_witness step R0 requests R"
  shows "state_has_ask_witness step R0 (requests @ suffix) R"
proof -
  have exists_word: "\<exists>word. requested_subsequence word requests \<and>
      R = run_product_action_word step word R0"
    using assms unfolding state_has_ask_witness_def .
  show ?thesis unfolding state_has_ask_witness_def
  proof (rule exE[OF exists_word])
    fix word
    assume both: "requested_subsequence word requests \<and> R = run_product_action_word step word R0"
    show "\<exists>word. requested_subsequence word (requests @ suffix) \<and>
        R = run_product_action_word step word R0"
    proof (rule exI[of _ word], rule conjI)
      show "requested_subsequence word (requests @ suffix)"
        by (rule requested_subsequence_append_right[OF conjunct1[OF both]])
      show "R = run_product_action_word step word R0" by (rule conjunct2[OF both])
    qed
  qed
qed

lemma one_actual_ask_extends_its_base_witness:
  assumes reach: "state_has_ask_witness step R0 requests R"
  shows "state_has_ask_witness step R0 (requests @ [(connection, action)]) (fst (step connection action R))"
proof -
  have exists_word: "\<exists>word. requested_subsequence word requests \<and>
      R = run_product_action_word step word R0"
    using reach unfolding state_has_ask_witness_def .
  show ?thesis unfolding state_has_ask_witness_def
  proof (rule exE[OF exists_word])
    fix word
    assume both: "requested_subsequence word requests \<and> R = run_product_action_word step word R0"
    have extended: "requested_subsequence (word @ [(connection, action)]) (requests @ [(connection, action)])"
      by (rule requested_subsequence_snoc[OF conjunct1[OF both]])
    have result: "fst (step connection action R) =
        run_product_action_word step (word @ [(connection, action)]) R0"
      using conjunct2[OF both] by (simp add: product_word_snoc)
    show "\<exists>word. requested_subsequence word (requests @ [(connection, action)]) \<and>
        fst (step connection action R) = run_product_action_word step word R0"
    proof (rule exI[of _ "word @ [(connection, action)]"], rule conjI)
      show "requested_subsequence (word @ [(connection, action)]) (requests @ [(connection, action)])"
        by (rule extended)
      show "fst (step connection action R) = run_product_action_word step (word @ [(connection, action)]) R0"
        by (rule result)
    qed
  qed
qed

lemma an_actual_single_request_has_a_state_witness:
  "state_has_ask_witness step R0 (actual_ask_word [Ask connection action]) (fst (step connection action R0))"
  using one_actual_ask_extends_its_base_witness[of step R0 "[]" R0 connection action] by simp

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms genesis_image_has_ask_witness ask_witness_append_right
      one_actual_ask_extends_its_base_witness an_actual_single_request_has_a_state_witness})
  then () else error "Unexpected oracle in Recovery_Request_Provenance_Witness"
\<close>

end
