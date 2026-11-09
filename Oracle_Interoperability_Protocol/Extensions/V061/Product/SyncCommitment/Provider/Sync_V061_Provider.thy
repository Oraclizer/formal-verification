theory Sync_V061_Provider
  imports "OIP_Sync_V061_Position_Selection.Sync_V061_Selection" "OIP_Reference_Profile.Reference_Source_Reader_Code"
begin

type_synonym sync_source_stream = "nat \<times> sync_stream"

definition sync_source_stream_of where
  "sync_source_stream_of a = (sync_deployment a,(sync_asset a,sync_origin a))"

definition sync_source_monotone_append where
  "sync_source_monotone_append selected stream a =
    (if sync_source_stream_of a = stream \<and>
        (case selected stream of None \<Rightarrow> sync_predecessor a = None
         | Some prior \<Rightarrow> sync_position (sync_item prior) < sync_position (sync_item a) \<and>
             (sync_predecessor a = None \<or> sync_predecessor a = Some (sync_commitment (sync_item prior))))
     then Some (selected(stream := Some a)) else None)"

lemma sync_source_append_requires_position_progress_across_epochs:
  assumes "sync_source_monotone_append selected stream a = Some updated" "selected stream = Some prior"
  shows "sync_position (sync_item prior) < sync_position (sync_item a)"
    "updated stream = Some a"
    "other \<noteq> stream \<Longrightarrow> updated other = selected other"
  using assms by (auto simp: sync_source_monotone_append_def split: if_splits)

definition sync_read_source_for_signer where
  "sync_read_source_for_signer valid journals source stream signer =
    issue_at_source_selection valid (journals signer) (source_selected_observation source) stream"

definition sync_selected_quorum_issue ::
  "(sync_source_stream \<Rightarrow> sync_statement \<Rightarrow> bool) \<Rightarrow>
   (nat \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes) \<Rightarrow>
   (nat \<Rightarrow> (sync_source_stream \<Rightarrow> sync_statement option) option) \<Rightarrow>
   (sync_source_stream, sync_statement) reference_source_storage \<Rightarrow>
   sync_source_stream \<Rightarrow> nat list \<Rightarrow> (sync_statement \<times> sync_votes) option" where
  "sync_selected_quorum_issue valid sign journals source stream signers =
    (case signers of [] \<Rightarrow> None
     | signer # rest \<Rightarrow>
       Option.bind (sync_read_source_for_signer valid journals source stream signer) (\<lambda>a.
         if (\<forall>i \<in> set rest. sync_read_source_for_signer valid journals source stream i = Some a)
         then Some (a,map (\<lambda>i. (i,sign i (sync_statement_bytes a))) signers) else None))"

lemma sync_a_successful_signer_read_uses_the_independent_selection:
  assumes "sync_read_source_for_signer valid journals source stream signer = Some a"
  shows "source_selection source stream = Some a"
    "journals signer = source_selected_observation source" "valid stream a"
  using assms by (auto simp: sync_read_source_for_signer_def source_selected_observation_def
    issue_at_source_selection_def split: option.splits if_splits)

theorem sync_all_issuing_signers_consume_one_selected_statement:
  assumes "sync_selected_quorum_issue valid sign journals source stream signers = Some (a,votes)"
  shows "source_selection source stream = Some a"
    "signers \<noteq> []"
    "\<forall>i \<in> set signers. sync_read_source_for_signer valid journals source stream i = Some a"
    "votes = map (\<lambda>i. (i,sign i (sync_statement_bytes a))) signers"
proof -
  obtain signer rest where split: "signers = signer # rest"
    and first: "sync_read_source_for_signer valid journals source stream signer = Some a"
    and all_rest: "\<forall>i \<in> set rest. sync_read_source_for_signer valid journals source stream i = Some a"
    and signed: "votes = map (\<lambda>i. (i,sign i (sync_statement_bytes a))) signers"
    using assms by (cases signers) (auto simp: sync_selected_quorum_issue_def bind_eq_Some_conv split: if_splits)
  show "source_selection source stream = Some a"
    by (rule sync_a_successful_signer_read_uses_the_independent_selection(1)[OF first])
  show "signers \<noteq> []" using split by simp
  show "\<forall>i \<in> set signers. sync_read_source_for_signer valid journals source stream i = Some a"
    using split first all_rest by simp
  show "votes = map (\<lambda>i. (i,sign i (sync_statement_bytes a))) signers" by (rule signed)
qed

lemma sync_rolled_back_source_journal_cannot_supply_a_vote:
  "journals signer \<noteq> source_selected_observation source \<Longrightarrow>
    sync_read_source_for_signer valid journals source stream signer = None"
  unfolding sync_read_source_for_signer_def
  by (rule no_source_vote_without_the_selected_journal, rule disjI2, assumption)

theorem sync_actual_selected_reader_supplies_the_source_vote:
  assumes actual: "read_rust_source_decision decode encode digest registered valid revision raw witness stream = Some a"
    and related: "rust_selected_source_view witness = source_selected_observation source"
  obtains journal where "decode raw = Some journal" "encode journal = raw"
    "witness = Rust_Source_Selected journal (revision,digest raw)" "0 < revision"
    "sync_read_source_for_signer valid (\<lambda>_. Some (map_of (rust_source_decisions journal))) source stream signer = Some a"
proof (rule every_successful_rust_source_read_at_the_exact_mark_refines_the_selected_vote[OF actual related])
  fix journal
  assume decoded: "decode raw = Some journal" and exact: "encode journal = raw"
    and mark: "witness = Rust_Source_Selected journal (revision,digest raw)" and positive: "0 < revision"
    and vote: "issue_at_source_selection valid (Some (map_of (rust_source_decisions journal)))
      (source_selected_observation source) stream = Some a"
  show thesis by (rule that[OF decoded exact mark positive]) (simp add: sync_read_source_for_signer_def vote)
qed

lemma sync_issued_and_verified_source_statement_has_both_bindings:
  assumes issued: "sync_selected_quorum_issue valid sign journals source stream signers = Some (a,votes)"
    and accepted: "sync_proof_ok verify registry core request a votes"
  shows "source_selection source stream = Some a" "sync_item a = sync_requested request"
  using sync_all_issuing_signers_consume_one_selected_statement(1)[OF issued]
    sync_accepted_proof_binds_every_request_field_and_current_roster(5)[OF accepted] by auto

theorem sync_published_fresh_result_joins_the_selected_source_and_receiver:
  assumes canonical: "sync_decode_core raw = Some core"
    and operand: "sync_read_operands core = Some request"
    and fresh: "sync_outcome_table (witness_control actual) (sync_call request) = None"
    and issued: "sync_selected_quorum_issue valid sign journals source stream signers = Some (a,votes)"
    and submitted: "sync_decode_proof (sync_attestation request) = Some (a,votes)"
    and published: "sync_publish_record verify core archives archive observed actual =
      Some (selected,Sync_Recorded (Sync_Committed position))"
  shows "source_selection source stream = Some a"
    "sync_retained (witness_control selected) (sync_key request) = Some (sync_item a)"
    "sync_outcome_table (witness_control selected) (sync_call request) = Some (raw,Sync_Committed position)"
    "sync_reopen_selected archives selected selected = Some (witness_control selected)"
proof -
  note selected = sync_published_reply_and_recovery_use_one_selected_record[OF published]
  obtain actual_statement actual_votes where
    decoded_proof: "sync_decode_proof (sync_attestation request) = Some (actual_statement,actual_votes)"
    and fields: "sync_item actual_statement = sync_requested request"
    and state: "witness_control selected = sync_commit_record (witness_control actual) core request actual_statement"
    and revision: "position = cut_revision (sync_current_cut (witness_control actual))"
    using sync_verified_fresh_success_is_the_single_attested_commit[OF operand fresh selected(4)] by blast
  have same_statement: "actual_statement = a" using decoded_proof submitted by simp
  have raw: "encode_wire_core core = raw" by (rule sync_decoded_core_has_the_exact_bytes[OF canonical])
  show "source_selection source stream = Some a"
    by (rule sync_all_issuing_signers_consume_one_selected_statement(1)[OF issued])
  have retained: "sync_retained (sync_commit_record (witness_control actual) core request actual_statement)
      (sync_key request) = Some (sync_requested request)"
    by (rule sync_commit_projects_the_single_stream_and_next_revision(1))
  show "sync_retained (witness_control selected) (sync_key request) = Some (sync_item a)"
    using retained fields state same_statement by simp
  have stored: "sync_outcome_table (sync_commit_record (witness_control actual) core request actual_statement) (sync_call request) =
    Some (encode_wire_core core,Sync_Committed (cut_revision (sync_current_cut (witness_control actual))))"
    by (rule sync_commit_records_the_origin_event_and_exact_core(2))
  show "sync_outcome_table (witness_control selected) (sync_call request) = Some (raw,Sync_Committed position)"
    using stored state raw revision by simp
  show "sync_reopen_selected archives selected selected = Some (witness_control selected)" by (rule selected(5))
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_source_append_requires_position_progress_across_epochs
    sync_all_issuing_signers_consume_one_selected_statement sync_rolled_back_source_journal_cannot_supply_a_vote
    sync_actual_selected_reader_supplies_the_source_vote sync_issued_and_verified_source_statement_has_both_bindings
    sync_published_fresh_result_joins_the_selected_source_and_receiver})
  then () else error "Unexpected oracle in SyncCommitment source provider"
\<close>

end
