theory DOSP_Recovery_Defense_Cases
  imports DOSP_Recovery_Progress
begin

context integrated_dosp_authority
begin

lemma activation_uses_the_existing_grant_and_handoff:
  "offered_recovery_step sources head offers grants governance s (Activate change epoch boundary time) reply t
    \<longleftrightarrow> recovery_step grants governance s (Activate change epoch boundary time) reply t"
  by (simp add: offered_recovery_step_def)

lemma accepted_recovery_use_cannot_substitute_an_action_or_reopen_a_completed_job:
  assumes step: "offered_recovery_step sources head offers grants governance s action
    (transition_result.Accepted (Installed job d sequence)) t"
    and valid: "s \<in> recovery_carrier"
  shows "job \<notin> completion_log s \<and> job \<in> completion_log t \<and>
    job \<notin> pending_ids t \<and> irreversible_facts t = irreversible_facts s"
proof -
  have native: "recovery_step grants governance s action (transition_result.Accepted (Installed job d sequence)) t"
    using offered_recovery_uses_a_native_step_or_refuses_without_effect[OF step] by simp
  have owner: "work_owner s job = Some d" and complete: "job \<in> completion_log t"
    using actual_install_uses_primary_record[OF native] by auto
  have src: "job \<notin> completion_log s"
    using valid owner by (auto simp: recovery_carrier_def pending_ids_def)
  have dst: "job \<notin> pending_ids t"
    using recovery_carrier_closed[OF native valid] complete by (auto simp: recovery_carrier_def)
  show ?thesis using src dst complete sourced_repair_preserves_irreversibility[OF step] by blast
qed

lemma offered_recovery_cannot_install_an_unapproved_rollback:
  assumes "rollback_incomplete s" "approval \<notin> governance"
  shows "\<not> offered_recovery_step sources head offers grants governance s
    (Governance_Resync approval job sequence) (transition_result.Accepted (Installed job d sequence)) t"
proof
  assume step: "offered_recovery_step sources head offers grants governance s
    (Governance_Resync approval job sequence) (transition_result.Accepted (Installed job d sequence)) t"
  have native: "recovery_step grants governance s (Governance_Resync approval job sequence)
    (transition_result.Accepted (Installed job d sequence)) t"
    using offered_recovery_uses_a_native_step_or_refuses_without_effect[OF step] by simp
  from native assms show False by (cases rule: recovery_step.cases) auto
qed

lemma prepared_governance_repair_uses_the_verified_record:
  assumes selected: "select_current_publication sources head offers (route_epoch s) = Some (authority, receipt)"
    and matches: "primary_receipt_matches authority receipt s"
    and owner: "work_owner s job = Some d" and member: "d \<in> active_domains s"
    and ready: "source_ready s" and rollback: "rollback_incomplete s"
    and approval: "approval \<in> governance"
  shows "offered_recovery_step sources head offers grants governance s
    (Governance_Resync approval job (primary_sequence s))
    (transition_result.Accepted (Installed job d (primary_sequence s)))
    ((install_replica s job d)\<lparr>rollback_incomplete := pending_ids (install_replica s job d) \<noteq> {}\<rparr>)"
proof -
  have native: "recovery_step grants governance s
    (Governance_Resync approval job (primary_sequence s))
    (transition_result.Accepted (Installed job d (primary_sequence s)))
    ((install_replica s job d)\<lparr>rollback_incomplete := pending_ids (install_replica s job d) \<noteq> {}\<rparr>)"
    by (rule recovery_step.Authorized_Resync[OF owner member ready refl rollback approval])
  show ?thesis using selected matches native by (simp add: offered_recovery_step_def receipt_repair_step_def)
qed

end

abbreviation after_job_eight :: "nat recovery_state" where
  "after_job_eight \<equiv> install_replica handed_off_recovery 8 6"

abbreviation after_job_nine :: "nat recovery_state" where
  "after_job_nine \<equiv> install_replica after_job_eight 9 6"

lemma handoff_has_a_real_primary_and_current_epoch:
  "route_epoch handed_off_recovery = 3"
  "primary_receipt_matches (current_publication_authority actual_authority) issued_second_receipt handed_off_recovery"
  "joined_dosp.select_current_publication two_journals current_repair_head
    [(52, current_source_candidate other_publisher_journal)] 3 = None"
proof -
  show epoch: "route_epoch handed_off_recovery = 3" by (simp add: handed_off_recovery_def)
  show "primary_receipt_matches (current_publication_authority actual_authority) issued_second_receipt handed_off_recovery"
    using the_metered_publication_is_replayed_into_the_same_job_after_handoff
    by (auto simp: joined_dosp.install_from_current_integrated_replay_def receipt_repair_step_def
      replay_of_the_metered_journal actual_publication_fields(2) split: if_splits)
  have different: "current_source_candidate other_publisher_journal \<noteq> current_source_candidate actual_metering_journal"
  proof
    have older: "joined_dosp.journal.checked_current_replay other_publisher_journal
      (current_source_candidate other_publisher_journal) = Some (call_authority_state other_publisher_journal)"
      unfolding other_publisher_journal_def
      by (rule joined_dosp.journal.generated_source_supplies_recovery_without_a_truth_flag)
    assume same: "current_source_candidate other_publisher_journal = current_source_candidate actual_metering_journal"
    have "call_authority_state other_publisher_journal = call_authority_state actual_metering_journal"
      using older replay_of_the_metered_journal same
      by (auto simp: joined_dosp.journal.checked_current_replay_def split: if_splits)
    then show False
      using publishers_have_different_actual_histories(1,2) by simp
  qed
  have no_matching_replay: "joined_dosp.journal.checked_current_replay actual_metering_journal
    (current_source_candidate other_publisher_journal) = None"
  proof (cases "joined_dosp.journal.checked_current_replay actual_metering_journal
    (current_source_candidate other_publisher_journal)")
    case (Some replay)
    then have keys: "call_genesis other_publisher_journal = call_genesis actual_metering_journal"
      "call_authority_log other_publisher_journal = call_authority_log actual_metering_journal"
      by (auto simp: joined_dosp.journal.checked_current_replay_def current_source_candidate_def split: if_splits)
    then have "current_source_candidate other_publisher_journal = current_source_candidate actual_metering_journal"
      by (simp add: current_source_candidate_def)
    with different show ?thesis by contradiction
  qed simp
  show "joined_dosp.select_current_publication two_journals current_repair_head
    [(52, current_source_candidate other_publisher_journal)] 3 = None"
    by (simp add: joined_dosp.select_current_publication_def two_journals_def current_repair_head_def no_matching_replay Let_def)
qed

theorem current_publication_retry_completes_the_carried_job_and_restores_trading:
  "joined_dosp.offered_recovery_step two_journals current_repair_head [prior_offer] joined_recovery_grants {}
    handed_off_recovery (Apply_Repair 8 51) (transition_result.Operational_Failure Evidence_Unavailable) handed_off_recovery"
  "joined_dosp.offered_recovery_step two_journals (current_repair_head\<lparr>head_route_epoch := 2\<rparr>)
    [live_offer] joined_recovery_grants {} handed_off_recovery (Apply_Repair 8 51)
    (transition_result.Operational_Failure Evidence_Unavailable) handed_off_recovery"
  "joined_dosp.offered_recovery_step two_journals current_repair_head [prior_offer, live_offer]
    joined_recovery_grants {} handed_off_recovery (Apply_Repair 8 51) (transition_result.Accepted (Installed 8 6 51)) after_job_eight"
  "joined_dosp.offered_recovery_step two_journals current_repair_head [live_offer, prior_offer]
    joined_recovery_grants {} after_job_eight (Ordinary_Trade 23) (transition_result.Rejected Recovery_Blocks_Trade) after_job_eight"
  "joined_dosp.offered_recovery_step two_journals current_repair_head [live_offer, prior_offer]
    joined_recovery_grants {} after_job_eight (Apply_Repair 9 51) (transition_result.Accepted (Installed 9 6 51)) after_job_nine"
  "joined_dosp.offered_recovery_step two_journals current_repair_head [live_offer, prior_offer]
    joined_recovery_grants {} after_job_nine (Ordinary_Trade 23) (transition_result.Accepted (Traded 23)) after_job_nine"
  "completion_log after_job_nine = {8,9} \<and> irreversible_facts after_job_nine = irreversible_facts published_recovery_state"
proof -
  show "joined_dosp.offered_recovery_step two_journals current_repair_head [prior_offer] joined_recovery_grants {}
    handed_off_recovery (Apply_Repair 8 51) (transition_result.Operational_Failure Evidence_Unavailable) handed_off_recovery"
    by (simp add: joined_dosp.offered_recovery_step_def handoff_has_a_real_primary_and_current_epoch(1)
      current_source_chosen_from_two_actual_histories(3))
  show "joined_dosp.offered_recovery_step two_journals (current_repair_head\<lparr>head_route_epoch := 2\<rparr>)
    [live_offer] joined_recovery_grants {} handed_off_recovery (Apply_Repair 8 51)
    (transition_result.Operational_Failure Evidence_Unavailable) handed_off_recovery"
    by (rule joined_dosp.an_outdated_head_cannot_install(1))
      (simp add: handoff_has_a_real_primary_and_current_epoch(1))
  have first: "receipt_repair_step joined_recovery_grants {} (current_publication_authority actual_authority) issued_second_receipt
    handed_off_recovery (Apply_Repair 8 51) (transition_result.Accepted (Installed 8 6 51)) after_job_eight"
    using the_metered_publication_is_replayed_into_the_same_job_after_handoff
    by (simp add: joined_dosp.install_from_current_integrated_replay_def replay_of_the_metered_journal actual_publication_fields(2))
  then show "joined_dosp.offered_recovery_step two_journals current_repair_head [prior_offer, live_offer]
    joined_recovery_grants {} handed_off_recovery (Apply_Repair 8 51) (transition_result.Accepted (Installed 8 6 51)) after_job_eight"
    by (simp add: joined_dosp.offered_recovery_step_def handoff_has_a_real_primary_and_current_epoch(1)
      current_source_chosen_from_two_actual_histories(1))
  have pending_nine: "9 \<in> pending_ids after_job_eight"
    using the_joined_install_closes_only_its_own_job(3) by (auto simp: pending_ids_def)
  show "joined_dosp.offered_recovery_step two_journals current_repair_head [live_offer, prior_offer]
    joined_recovery_grants {} after_job_eight (Ordinary_Trade 23) (transition_result.Rejected Recovery_Blocks_Trade) after_job_eight"
    unfolding joined_dosp.offered_recovery_step_def replica_repair.simps if_False
    by (rule recovery_step.Refuse_Trade) (use pending_nine in auto)
  have matches: "primary_receipt_matches (current_publication_authority actual_authority) issued_second_receipt after_job_eight"
    using first handoff_has_a_real_primary_and_current_epoch(2)
    by (meson receipt_repair_step_def recovery_keeps_the_primary_receipt)
  have facts: "route_epoch after_job_eight = 3" "source_ready after_job_eight" "6 \<in> active_domains after_job_eight"
    "primary_sequence after_job_eight = 51" "\<not> rollback_incomplete after_job_eight"
    by (simp_all add: install_replica_def handed_off_recovery_def joined_recovery_def noticed_recovery_def
      published_recovery_state_def actual_publication_fields issued_second_receipt_def Let_def)
  have ready: "joined_dosp.verified_job_ready two_journals current_repair_head [live_offer, prior_offer]
    after_job_eight 9 6 51"
    using current_source_chosen_from_two_actual_histories(2) matches facts the_joined_install_closes_only_its_own_job(3)
    by (auto simp: joined_dosp.verified_job_ready_def)
  show "joined_dosp.offered_recovery_step two_journals current_repair_head [live_offer, prior_offer]
    joined_recovery_grants {} after_job_eight (Apply_Repair 9 51) (transition_result.Accepted (Installed 9 6 51)) after_job_nine"
    by (rule joined_dosp.ready_job_can_install[OF ready])
  show "joined_dosp.offered_recovery_step two_journals current_repair_head [live_offer, prior_offer]
    joined_recovery_grants {} after_job_nine (Ordinary_Trade 23) (transition_result.Accepted (Traded 23)) after_job_nine"
    unfolding joined_dosp.offered_recovery_step_def replica_repair.simps if_False
    by (rule recovery_step.Admit_Trade)
      (simp_all add: pending_ids_def install_replica_def handed_off_recovery_def joined_recovery_def noticed_recovery_def
        published_recovery_state_def dom_def carry_owner_def Let_def fun_eq_iff)
  show "completion_log after_job_nine = {8,9} \<and> irreversible_facts after_job_nine = irreversible_facts published_recovery_state"
    by (simp add: install_replica_def handed_off_recovery_def joined_recovery_def noticed_recovery_def
      published_recovery_state_def Let_def insert_commute)
qed

end
