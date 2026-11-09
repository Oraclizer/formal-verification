theory Sync_V061_Concrete_Supplier
  imports Sync_V061_Supplier_Readback
begin

record ('stores, 'digest) supplier_vote =
  supplier_vote_selection :: "('stores, 'digest) supplier_selection"
  supplier_vote_signature :: "nat \<times> wire_bytes"

definition supplier_issue_commitment where
  "supplier_issue_commitment read_current rules signer local_key sign_bytes expected =
    Option.bind (read_current (snd (sync_source_stream_of (supplier_selection_statement expected)))) (\<lambda>current_token.
      Option.bind (supplier_rule_for rules (supplier_selection_statement current_token)) (\<lambda>roster.
        if current_token = expected \<and> supplier_roster_signers roster signer = Some local_key
        then Some \<lparr>supplier_vote_selection = current_token,
          supplier_vote_signature = (signer,sign_bytes (sync_statement_bytes (supplier_selection_statement current_token)))\<rparr>
        else None))"

lemma supplier_issued_vote_consumes_the_current_token_and_registered_key:
  assumes "supplier_issue_commitment read_current rules signer local_key sign_bytes expected = Some vote"
  shows "read_current (snd (sync_source_stream_of (supplier_selection_statement expected))) = Some expected"
    "\<exists>roster. supplier_rule_for rules (supplier_selection_statement expected) = Some roster \<and>
      supplier_roster_signers roster signer = Some local_key"
    "supplier_vote_selection vote = expected"
    "supplier_vote_signature vote = (signer,sign_bytes (sync_statement_bytes (supplier_selection_statement expected)))"
  using assms by (auto simp: supplier_issue_commitment_def bind_eq_Some_conv split: if_splits)

lemma supplier_issue_fails_if_the_readback_is_unavailable_or_the_exact_token_or_key_differs:
  "read_current (snd (sync_source_stream_of (supplier_selection_statement expected))) = None \<Longrightarrow>
    supplier_issue_commitment read_current rules signer local_key sign_bytes expected = None"
  "read_current (snd (sync_source_stream_of (supplier_selection_statement expected))) = Some current_token \<Longrightarrow>
   supplier_rule_for rules (supplier_selection_statement current_token) = Some roster \<Longrightarrow>
   current_token \<noteq> expected \<or> supplier_roster_signers roster signer \<noteq> Some local_key \<Longrightarrow>
    supplier_issue_commitment read_current rules signer local_key sign_bytes expected = None"
  by (auto simp: supplier_issue_commitment_def)

lemma supplier_issue_from_the_concrete_reader_uses_the_independent_mark:
  assumes issued: "supplier_issue_commitment
    (supplier_selected_commitment verify deployment rules records stores archives journal observed)
    rules signer local_key sign_bytes expected = Some vote"
  shows "journal = observed" "observed \<in> archives"
    "supplier_selection_stores (supplier_vote_selection vote) = stores"
    "supplier_selection_mark (supplier_vote_selection vote) = supplier_snapshot_mark observed"
proof -
  note bound = supplier_issued_vote_consumes_the_current_token_and_registered_key[OF issued]
  note read = supplier_selection_is_the_exact_store_mark_statement_and_quorum[OF bound(1)]
  show "journal = observed" using read by blast
  show "observed \<in> archives" using read by blast
  show "supplier_selection_stores (supplier_vote_selection vote) = stores" using bound(3) read by blast
  show "supplier_selection_mark (supplier_vote_selection vote) = supplier_snapshot_mark observed" using bound(3) read by blast
qed

lemma supplier_journal_rollback_cannot_issue_a_vote:
  assumes "journal \<noteq> observed"
  shows "supplier_issue_commitment
    (supplier_selected_commitment verify deployment rules records stores archives journal observed)
    rules signer local_key sign_bytes expected = None"
  using supplier_rollback_or_unselected_archive_refuses_readback[OF disjI1[OF assms]]
  by (simp add: supplier_selected_commitment_def supplier_issue_commitment_def)

definition supplier_sorted_signatures where
  "supplier_sorted_signatures votes = sort_key fst (map supplier_vote_signature votes)"

definition supplier_encode_sorted where
  "supplier_encode_sorted statement signatures =
    (if sorted_wrt (<) (map fst signatures) \<and> length signatures < 2^64
     then Some (sync_proof_bytes statement signatures) else None)"

definition supplier_assemble_proof where
  "supplier_assemble_proof selected votes =
    (if supplier_selection_quorum selected \<le> length votes \<and>
         (\<forall>vote \<in> set votes. supplier_vote_selection vote = selected)
     then supplier_encode_sorted (supplier_selection_statement selected) (supplier_sorted_signatures votes)
     else None)"

lemma supplier_assembly_consumes_the_same_selection_and_sorted_distinct_signer_ids:
  assumes "supplier_assemble_proof selected votes = Some blob"
  shows "supplier_selection_quorum selected \<le> length votes"
    "\<forall>vote \<in> set votes. supplier_vote_selection vote = selected"
    "sorted_wrt (<) (map fst (supplier_sorted_signatures votes))"
    "distinct (map fst (supplier_sorted_signatures votes))"
    "blob = sync_proof_bytes (supplier_selection_statement selected) (supplier_sorted_signatures votes)"
  using assms by (auto simp: supplier_assemble_proof_def supplier_encode_sorted_def strict_sorted_iff split: if_splits)

lemma supplier_strict_signer_order_is_unique_after_sorting:
  assumes accepted: "supplier_assemble_proof selected votes = Some blob"
    and ordered: "sorted_wrt (<) (map fst output)"
    and same: "set output = set (supplier_sorted_signatures votes)"
  shows "output = supplier_sorted_signatures votes"
proof -
  have model_order: "sorted_wrt (<) (map fst (supplier_sorted_signatures votes))"
    by (rule supplier_assembly_consumes_the_same_selection_and_sorted_distinct_signer_ids(3)[OF accepted])
  have keys: "inj_on fst (set output)"
    using ordered by (auto simp: strict_sorted_iff distinct_map)
  show ?thesis
    by (rule map_sorted_distinct_set_unique[of fst])
       (use keys ordered model_order same in \<open>auto simp: strict_sorted_iff\<close>)
qed

theorem supplier_assembled_signatures_are_from_each_signers_independent_read:
  assumes issued: "\<forall>vote \<in> set votes. \<exists>signer.
    supplier_issue_commitment (read_by signer) rules signer (local_keys signer) (sign_by signer) selected = Some vote"
    and assembled: "supplier_assemble_proof selected votes = Some blob"
  shows "\<forall>(signer,signature) \<in> set (supplier_sorted_signatures votes).
    read_by signer (snd (sync_source_stream_of (supplier_selection_statement selected))) = Some selected \<and>
    (\<exists>roster. supplier_rule_for rules (supplier_selection_statement selected) = Some roster \<and>
      supplier_roster_signers roster signer = Some (local_keys signer)) \<and>
    signature = sign_by signer (sync_statement_bytes (supplier_selection_statement selected))"
    "blob = sync_proof_bytes (supplier_selection_statement selected) (supplier_sorted_signatures votes)"
proof -
  show "\<forall>(signer,signature) \<in> set (supplier_sorted_signatures votes).
    read_by signer (snd (sync_source_stream_of (supplier_selection_statement selected))) = Some selected \<and>
    (\<exists>roster. supplier_rule_for rules (supplier_selection_statement selected) = Some roster \<and>
      supplier_roster_signers roster signer = Some (local_keys signer)) \<and>
    signature = sign_by signer (sync_statement_bytes (supplier_selection_statement selected))"
  proof (intro ballI)
    fix item
    assume member: "item \<in> set (supplier_sorted_signatures votes)"
    obtain vote where present: "vote \<in> set votes" and signature: "item = supplier_vote_signature vote"
      using member by (auto simp: supplier_sorted_signatures_def)
    obtain signer where signed: "supplier_issue_commitment (read_by signer) rules signer
      (local_keys signer) (sign_by signer) selected = Some vote"
      using issued present by blast
    note checks = supplier_issued_vote_consumes_the_current_token_and_registered_key[OF signed]
    show "case item of (signer,signature) \<Rightarrow>
      read_by signer (snd (sync_source_stream_of (supplier_selection_statement selected))) = Some selected \<and>
      (\<exists>roster. supplier_rule_for rules (supplier_selection_statement selected) = Some roster \<and>
        supplier_roster_signers roster signer = Some (local_keys signer)) \<and>
      signature = sign_by signer (sync_statement_bytes (supplier_selection_statement selected))"
      using signature checks(1,2,4) by simp
  qed
  show "blob = sync_proof_bytes (supplier_selection_statement selected) (supplier_sorted_signatures votes)"
    by (rule supplier_assembly_consumes_the_same_selection_and_sorted_distinct_signer_ids(5)[OF assembled])
qed

lemma supplier_zero_quorum_requires_the_reader_constructor_guard:
  assumes "supplier_selection_quorum selected = 0"
  shows "supplier_assemble_proof selected [] = Some (sync_proof_bytes (supplier_selection_statement selected) [])"
  using assms by (simp add: supplier_assemble_proof_def supplier_sorted_signatures_def supplier_encode_sorted_def)

abbreviation supplier_example_vote where
  "supplier_example_vote token signer signature \<equiv>
    \<lparr>supplier_vote_selection = token, supplier_vote_signature = (signer,signature)\<rparr>"

lemma supplier_quorum_and_duplicate_controls:
  assumes "supplier_selection_quorum selected = 2"
  shows "supplier_assemble_proof selected [supplier_example_vote selected 2 sig_two, supplier_example_vote selected 1 sig_one] =
    Some (sync_proof_bytes (supplier_selection_statement selected) [(1,sig_one),(2,sig_two)])"
    "supplier_assemble_proof selected [supplier_example_vote selected 1 sig_one] = None"
    "supplier_encode_sorted (supplier_selection_statement selected) [(1,sig_one)] =
      Some (sync_proof_bytes (supplier_selection_statement selected) [(1,sig_one)])"
    "supplier_assemble_proof selected [supplier_example_vote selected 1 sig_one, supplier_example_vote selected 1 sig_two] = None"
  using assms by (simp_all add: supplier_assemble_proof_def supplier_sorted_signatures_def supplier_encode_sorted_def)

lemma supplier_identity_mismatch_reaches_the_exact_token_check:
  assumes "supplier_selection_quorum selected = 2" "different \<noteq> selected"
  shows "supplier_assemble_proof selected [supplier_example_vote different 2 sig_two, supplier_example_vote selected 1 sig_one] = None"
    "supplier_encode_sorted (supplier_selection_statement selected)
      (supplier_sorted_signatures [supplier_example_vote different 2 sig_two, supplier_example_vote selected 1 sig_one]) =
      Some (sync_proof_bytes (supplier_selection_statement selected) [(1,sig_one),(2,sig_two)])"
  using assms by (simp_all add: supplier_assemble_proof_def supplier_sorted_signatures_def supplier_encode_sorted_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    supplier_authenticated_record_consumes_exact_statement_and_registered_issuer
    supplier_append_checks_event_and_reuses_monotone_source_append
    supplier_reused_event_reaches_the_event_guard_when_the_other_stream_can_append
    supplier_replay_cannot_drop_a_seen_event
    supplier_rollback_or_unselected_archive_refuses_readback
    supplier_token_equality_uses_all_four_components
    supplier_selection_is_the_exact_store_mark_statement_and_quorum
    supplier_selected_quorum_is_nonzero_under_the_reader_constructor_check
    supplier_issued_vote_consumes_the_current_token_and_registered_key
    supplier_issue_fails_if_the_readback_is_unavailable_or_the_exact_token_or_key_differs
    supplier_issue_from_the_concrete_reader_uses_the_independent_mark supplier_journal_rollback_cannot_issue_a_vote
    supplier_assembly_consumes_the_same_selection_and_sorted_distinct_signer_ids
    supplier_strict_signer_order_is_unique_after_sorting
    supplier_assembled_signatures_are_from_each_signers_independent_read
    supplier_zero_quorum_requires_the_reader_constructor_guard supplier_quorum_and_duplicate_controls
    supplier_identity_mismatch_reaches_the_exact_token_check})
  then () else error "Unexpected oracle in the concrete SyncCommitment supplier"
\<close>

end
