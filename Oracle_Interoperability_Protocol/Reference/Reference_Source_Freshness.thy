theory Reference_Source_Freshness
  imports "Reference_Evidence_Supply"
begin

datatype ('origin, 'decision) reference_source_stage =
    Source_Selected
  | Source_Appending 'origin 'decision
  | Source_Repairing

record ('origin, 'decision) reference_source_storage =
  source_journal :: "'origin \<Rightarrow> 'decision option"
  source_selection :: "'origin \<Rightarrow> 'decision option"
  source_stage :: "('origin, 'decision) reference_source_stage"

datatype ('origin, 'decision) reference_source_action =
    Reserve_Source "'origin \<Rightarrow> 'decision option" 'origin 'decision
  | Prepare_Source "'origin \<Rightarrow> 'decision option" 'origin 'decision
  | Select_Source "'origin \<Rightarrow> 'decision option" 'origin 'decision
  | Restore_Source "'origin \<Rightarrow> 'decision option"
  | Begin_Source_Repair bool "'origin \<Rightarrow> 'decision option"
  | Repair_Source bool "'origin \<Rightarrow> 'decision option"

fun reference_source_write where
  "reference_source_write verified (Reserve_Source expected origin decision) state =
    (if source_stage state = Source_Selected \<and> expected = source_selection state \<and> source_journal state = expected \<and>
        expected origin = None \<and> verified origin decision
     then state\<lparr>source_stage := Source_Appending origin decision\<rparr> else state)"
| "reference_source_write verified (Prepare_Source expected origin decision) state =
    (if source_stage state = Source_Appending origin decision \<and> expected = source_selection state \<and>
        source_journal state = expected \<and> expected origin = None \<and> verified origin decision
     then state\<lparr>source_journal := expected(origin := Some decision)\<rparr> else state)"
| "reference_source_write verified (Select_Source expected origin decision) state =
    (if source_stage state = Source_Appending origin decision \<and> expected = source_selection state \<and>
        expected origin = None \<and> verified origin decision \<and>
        source_journal state = expected(origin := Some decision)
     then state\<lparr>source_selection := expected(origin := Some decision), source_stage := Source_Selected\<rparr> else state)"
| "reference_source_write verified (Restore_Source old) state = state\<lparr>source_journal := old\<rparr>"
| "reference_source_write verified (Begin_Source_Repair authorized expected) state =
    (if authorized \<and> source_stage state = Source_Selected \<and> expected = source_selection state
     then state\<lparr>source_stage := Source_Repairing\<rparr> else state)"
| "reference_source_write verified (Repair_Source authorized expected) state =
    (if authorized \<and> source_stage state = Source_Repairing \<and> expected = source_selection state
     then state\<lparr>source_journal := expected, source_stage := Source_Selected\<rparr> else state)"

fun reference_source_writes where
  "reference_source_writes verified [] state = state"
| "reference_source_writes verified (write # rest) state =
    reference_source_writes verified rest (reference_source_write verified write state)"

definition issue_at_source_selection where
  "issue_at_source_selection verified journal_read witness_read origin =
    (case witness_read of None \<Rightarrow> None | Some selected \<Rightarrow>
      if journal_read = Some selected
      then case selected origin of None \<Rightarrow> None
         | Some decision \<Rightarrow> if verified origin decision then Some decision else None
      else None)"

definition source_selected_observation where
  "source_selected_observation state =
    (if source_stage state = Source_Selected then Some (source_selection state) else None)"

lemma source_read_agrees_with_the_independent_selection:
  assumes "issue_at_source_selection verified journal (Some selected) origin = Some decision"
  shows "journal = Some selected" "selected origin = Some decision" "verified origin decision"
  using assms by (auto simp: issue_at_source_selection_def split: option.splits if_splits)

lemma no_source_vote_without_the_selected_journal:
  assumes "witness = None \<or> journal \<noteq> witness"
  shows "issue_at_source_selection verified journal witness origin = None"
  using assms by (cases witness) (auto simp: issue_at_source_selection_def)

lemma one_source_write_preserves_every_previously_selected_decision:
  assumes "source_selection state origin = Some decision"
  shows "source_selection (reference_source_write verified action state) origin = Some decision"
  using assms by (cases action) (auto split: if_splits)

lemma source_writes_preserve_every_previously_selected_decision:
  assumes "source_selection state origin = Some decision"
  shows "source_selection (reference_source_writes verified writes state) origin = Some decision"
  using assms by (induction writes arbitrary: state) (auto intro: one_source_write_preserves_every_previously_selected_decision)

theorem two_votes_for_one_origin_have_the_same_exact_decision_across_source_writes:
  assumes first: "issue_at_source_selection verified early (source_selected_observation before) origin = Some initial"
    and later: "issue_at_source_selection verified late
       (source_selected_observation (reference_source_writes verified writes before)) origin = Some observed"
  shows "observed = initial"
proof -
  have exact_first: "issue_at_source_selection verified early (Some (source_selection before)) origin = Some initial"
    using first by (auto simp: source_selected_observation_def issue_at_source_selection_def split: if_splits)
  have exact_later: "issue_at_source_selection verified late
      (Some (source_selection (reference_source_writes verified writes before))) origin = Some observed"
    using later by (auto simp: source_selected_observation_def issue_at_source_selection_def split: if_splits)
  have prior: "source_selection before origin = Some initial"
    by (rule source_read_agrees_with_the_independent_selection(2)[OF exact_first])
  note retained = source_writes_preserve_every_previously_selected_decision[OF prior, where verified=verified and writes=writes]
  note exact = source_read_agrees_with_the_independent_selection(2)[OF exact_later]
  show ?thesis using retained exact by simp
qed

theorem a_source_quorum_from_the_selected_journal_has_the_exact_authoritative_record:
  assumes issued: "issue_at_source_selection valid journal (source_selected_observation state)
       (evidence_profile claim, fst (evidence_payload claim)) = Some (evidence_epoch claim, snd (evidence_payload claim))"
    and quorum: "source_certificate_quorum keys verify required claim proofs"
  shows "authoritative_source_certificate (source_selection state) keys verify required claim proofs"
proof -
  have exact: "issue_at_source_selection valid journal (Some (source_selection state))
      (evidence_profile claim, fst (evidence_payload claim)) = Some (evidence_epoch claim, snd (evidence_payload claim))"
    using issued by (auto simp: source_selected_observation_def issue_at_source_selection_def split: if_splits)
  show ?thesis using source_read_agrees_with_the_independent_selection(2)[OF exact] quorum
    by (cases "evidence_payload claim") (simp add: authoritative_source_certificate_def)
qed

lemma source_rollback_alone_cannot_issue_or_replace_the_selected_decision:
  fixes valid
  assumes stale: "old \<noteq> source_selection state"
    and original: "source_selection state origin = Some initial"
  defines "restored \<equiv> reference_source_write valid (Restore_Source old) state"
  shows "issue_at_source_selection valid (Some (source_journal restored)) (source_selected_observation restored) origin = None"
    "reference_source_write valid (Select_Source (source_selection state) origin conflicting) restored = restored"
  using stale original by (simp_all add: restored_def issue_at_source_selection_def source_selected_observation_def split: if_splits)

lemma removing_the_independent_readback_admits_the_same_stale_signed_record:
  assumes "old origin = Some decision" "valid origin decision" "old \<noteq> selected"
  shows "issue_at_source_selection valid (Some old) (Some selected) origin = None"
    "issue_at_source_selection valid (Some old) (Some old) origin = Some decision"
  using assms by (simp_all add: issue_at_source_selection_def)

lemma an_interrupted_append_holds_and_only_the_reserved_decision_can_be_selected:
  fixes prior reserved prepared selected
  assumes empty: "source_selection state origin = None" and valid: "valid origin decision"
    and ready: "source_journal state = source_selection state" "source_stage state = Source_Selected"
  defines "prior \<equiv> source_selection state"
    and "reserved \<equiv> reference_source_write valid (Reserve_Source prior origin decision) state"
    and "prepared \<equiv> reference_source_write valid (Prepare_Source prior origin decision) reserved"
    and "selected \<equiv> reference_source_write valid (Select_Source prior origin decision) prepared"
  shows "issue_at_source_selection valid (Some (source_journal reserved)) (source_selected_observation reserved) origin = None"
    "issue_at_source_selection valid (Some (source_journal prepared)) (source_selected_observation prepared) origin = None"
    "issue_at_source_selection valid (Some (source_journal selected)) (source_selected_observation selected) origin = Some decision"
    "reference_source_write valid (Select_Source prior origin decision) selected = selected"
    "conflicting \<noteq> decision \<Longrightarrow>
      reference_source_write valid (Select_Source prior origin conflicting) prepared = prepared"
  using empty valid ready
  by (simp_all add: prior_def reserved_def prepared_def selected_def issue_at_source_selection_def source_selected_observation_def)

lemma exact_authorized_repair_restores_the_same_source_vote:
  fixes started repaired
  assumes "source_selection state origin = Some decision" "valid origin decision" "source_stage state = Source_Selected"
  defines "started \<equiv> reference_source_write valid (Begin_Source_Repair True (source_selection state)) state"
    and "repaired \<equiv> reference_source_write valid (Repair_Source True (source_selection state)) started"
  shows "issue_at_source_selection valid (Some (source_journal repaired)) (source_selected_observation repaired) origin = Some decision"
  using assms by (simp add: repaired_def started_def issue_at_source_selection_def source_selected_observation_def)

lemma simultaneous_rollback_of_the_source_and_its_witness_can_reissue_an_opposite_decision:
  fixes first second :: bool and fresh run
  assumes "first \<noteq> second"
  defines "fresh \<equiv> \<lparr>source_journal = (\<lambda>_ :: unit. None), source_selection = (\<lambda>_. None),
      source_stage = Source_Selected\<rparr>"
    and "run \<equiv> \<lambda>d. reference_source_writes (\<lambda>_ _. True)
       [Reserve_Source (source_selection fresh) () d, Prepare_Source (source_selection fresh) () d,
        Select_Source (source_selection fresh) () d] fresh"
  shows "issue_at_source_selection (\<lambda>_ _. True) (Some (source_journal (run first)))
         (source_selected_observation (run first)) () = Some first"
    "issue_at_source_selection (\<lambda>_ _. True) (Some (source_journal (run second)))
         (source_selected_observation (run second)) () = Some second"
  by (simp_all add: fresh_def run_def issue_at_source_selection_def source_selected_observation_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms two_votes_for_one_origin_have_the_same_exact_decision_across_source_writes
    a_source_quorum_from_the_selected_journal_has_the_exact_authoritative_record
    source_rollback_alone_cannot_issue_or_replace_the_selected_decision
    removing_the_independent_readback_admits_the_same_stale_signed_record
    an_interrupted_append_holds_and_only_the_reserved_decision_can_be_selected
    exact_authorized_repair_restores_the_same_source_vote
    simultaneous_rollback_of_the_source_and_its_witness_can_reissue_an_opposite_decision})
  then () else error "Unexpected oracle in reference source freshness"
\<close>

end
