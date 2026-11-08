theory Recovery_Request_Provenance_Types
  imports "Recovery_Request_Provenance_Archive"
begin

lemma a_changed_toy_image_cannot_be_invented_without_an_ask:
  "\<not> state_has_ask_witness toy_step R0 (actual_ask_word []) (toy_bump R0)"
proof
  assume old: "state_has_ask_witness toy_step R0 (actual_ask_word []) (toy_bump R0)"
  have exists_word: "\<exists>word. requested_subsequence word [] \<and>
      toy_bump R0 = run_product_action_word toy_step word R0"
    using old by (simp only: actual_ask_word_Nil state_has_ask_witness_def)
  show False
  proof (rule exE[OF exists_word])
    fix word
    assume both: "requested_subsequence word [] \<and> toy_bump R0 = run_product_action_word toy_step word R0"
    have empty_word: "word = []"
      by (rule requested_subsequence_empty_right[OF conjunct1[OF both]])
    have "toy_bump R0 = R0" using conjunct2[OF both] empty_word by simp
    then show False by simp
  qed
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms a_changed_toy_image_cannot_be_invented_without_an_ask})
  then () else error "Unexpected oracle in Recovery_Request_Provenance_Types"
\<close>

end
