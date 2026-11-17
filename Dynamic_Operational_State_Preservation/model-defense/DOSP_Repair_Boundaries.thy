theory DOSP_Repair_Boundaries
  imports DOSP_Recovery_Defense_Cases DOSP_Atomic_Comparison.Atomic_Comparison
begin

lemma membership_uses_the_consensus_boundary_and_current_grant:
  "joined_dosp.offered_recovery_step two_journals current_repair_head [] joined_recovery_grants {}
    noticed_recovery (Activate (Join_Domain 6 9) 2 86400 86399)
    (transition_result.Rejected Stale_Route) noticed_recovery"
  "joined_dosp.offered_recovery_step two_journals current_repair_head [] {} {}
    noticed_recovery (Activate (Join_Domain 6 9) 2 86400 86400)
    (transition_result.Rejected Stale_Route) noticed_recovery"
  "joined_dosp.offered_recovery_step two_journals current_repair_head [] joined_recovery_grants {}
    noticed_recovery (Activate (Join_Domain 6 9) 2 86400 86400)
    (transition_result.Accepted (Joined 6 9)) joined_recovery"
  "joined_dosp.offered_recovery_step two_journals current_repair_head [] joined_recovery_grants {}
    joined_recovery (Activate (Leave_Domain 2 6) 3 86400 86400)
    (transition_result.Accepted (Left 2 6)) handed_off_recovery"
  "joined_dosp.offered_recovery_step two_journals current_repair_head [] joined_recovery_grants {}
    handed_off_recovery (Activate (Leave_Domain 2 6) 3 86400 86400)
    (transition_result.Rejected Stale_Route) handed_off_recovery"
  unfolding joined_dosp.activation_uses_the_existing_grant_and_handoff
  by (rule this_publication_produces_a_job_that_moves_to_the_new_domain(2,3) recovery_step.Reject_Route |
      simp add: current_grant_def handed_off_recovery_def)+

lemma membership_keeps_the_handed_off_pending_ids_and_historical_facts:
  "work_owner joined_recovery 8 = Some 2" "work_owner handed_off_recovery 8 = Some 6"
  "work_owner handed_off_recovery 9 = Some 6"
  "pending_ids handed_off_recovery = pending_ids joined_recovery"
  "irreversible_facts handed_off_recovery = irreversible_facts published_recovery_state"
  "replica joined_recovery 6 \<noteq> primary_record joined_recovery"
  using leave_transports_work[OF this_publication_produces_a_job_that_moves_to_the_new_domain(3)]
  by (simp_all add: handed_off_recovery_def joined_recovery_def noticed_recovery_def published_recovery_state_def carry_owner_def Let_def)

lemma recovery_states_before_and_after_handoff_are_in_the_carrier:
  "published_recovery_state \<in> recovery_carrier"
  "handed_off_recovery \<in> recovery_carrier"
proof -
  show seed: "published_recovery_state \<in> recovery_carrier"
    by (auto simp: published_recovery_state_def recovery_carrier_def replica_covered_def pending_ids_def dom_def Let_def)
  note steps = this_publication_produces_a_job_that_moves_to_the_new_domain
  show "handed_off_recovery \<in> recovery_carrier"
    by (rule recovery_carrier_closed[OF steps(3) recovery_carrier_closed[OF steps(2) recovery_carrier_closed[OF steps(1) seed]]])
qed

abbreviation unavailable_publication_event where
  "unavailable_publication_event \<equiv> mk_event handed_off_recovery (Apply_Repair 8 51)
    (transition_result.Operational_Failure Evidence_Unavailable) handed_off_recovery"

theorem repeated_refusal_of_an_old_publisher_is_not_recovery_progress:
  "joined_dosp.authenticated_recovery_run (\<lambda>_. two_journals) (\<lambda>_. current_repair_head) (\<lambda>_. [prior_offer])
      joined_recovery_grants {} {handed_off_recovery} (\<lambda>_. unavailable_publication_event) \<and>
    (\<forall>i. \<not> joined_dosp.recovery_interference (\<lambda>_. current_repair_head) (\<lambda>_. unavailable_publication_event) i) \<and>
    8 \<in> pending_ids handed_off_recovery \<and> 8 \<notin> completion_log handed_off_recovery"
proof -
  have run: "joined_dosp.authenticated_recovery_run (\<lambda>_. two_journals) (\<lambda>_. current_repair_head) (\<lambda>_. [prior_offer])
      joined_recovery_grants {} {handed_off_recovery} (\<lambda>_. unavailable_publication_event)"
    by (simp add: joined_dosp.authenticated_recovery_run_def
      recovery_states_before_and_after_handoff_are_in_the_carrier(2)
      current_publication_retry_completes_the_carried_job_and_restores_trading(1)
      step_occurs_def mk_event_def)
  show ?thesis
    using run by (simp add: joined_dosp.recovery_interference_def pending_ids_def mk_event_def affects_recovery_def
      membership_keeps_the_handed_off_pending_ids_and_historical_facts(2)
      handed_off_recovery_def joined_recovery_def noticed_recovery_def published_recovery_state_def Let_def)
qed

definition with_a_second_divergence :: "nat recovery_state" where
  "with_a_second_divergence = handed_off_recovery\<lparr>
    replica := (replica handed_off_recovery)(4 := Suc (primary_record handed_off_recovery)),
    work_owner := (work_owner handed_off_recovery)(10 \<mapsto> 4)\<rparr>"

theorem a_real_nonfinal_install_has_a_raw_replica_counterexample:
  defines "t \<equiv> install_replica with_a_second_divergence 8 6"
  shows "joined_dosp.offered_recovery_step two_journals current_repair_head [prior_offer,live_offer]
    joined_recovery_grants {} with_a_second_divergence (Apply_Repair 8 51)
    (transition_result.Accepted (Installed 8 6 51)) t"
    "client_recovery_view t = client_recovery_view with_a_second_divergence"
    "replica t 6 \<noteq> replica with_a_second_divergence 6 \<and>
      replica t 4 \<noteq> primary_record t \<and> work_owner t 10 = Some 4"
proof -
  have opened: "recovery_step joined_recovery_grants {} handed_off_recovery
    (Notice_Divergence 10 4 (Suc (primary_record handed_off_recovery)))
    (transition_result.Accepted (Opened 10)) with_a_second_divergence"
    unfolding with_a_second_divergence_def
    by (rule recovery_step.Detect_Divergence)
      (simp_all add: handed_off_recovery_def joined_recovery_def noticed_recovery_def
        published_recovery_state_def fresh_work_def carry_owner_def Let_def)
  have receipt: "primary_receipt_matches (current_publication_authority actual_authority) issued_second_receipt with_a_second_divergence"
    using recovery_keeps_the_primary_receipt[OF opened] handoff_has_a_real_primary_and_current_epoch(2) by simp
  have ready: "joined_dosp.verified_job_ready two_journals current_repair_head [prior_offer,live_offer] with_a_second_divergence 8 6 51"
    using receipt current_source_chosen_from_two_actual_histories(1)
    by (simp add: joined_dosp.verified_job_ready_def with_a_second_divergence_def handed_off_recovery_def joined_recovery_def
      noticed_recovery_def published_recovery_state_def actual_publication_fields issued_second_receipt_def carry_owner_def Let_def)
  show step: "joined_dosp.offered_recovery_step two_journals current_repair_head [prior_offer,live_offer]
    joined_recovery_grants {} with_a_second_divergence (Apply_Repair 8 51)
    (transition_result.Accepted (Installed 8 6 51)) t"
    unfolding t_def by (rule joined_dosp.ready_job_can_install[OF ready])
  have debt: "work_owner with_a_second_divergence 10 = Some 4" "work_owner t 10 = Some 4"
    by (simp_all add: t_def with_a_second_divergence_def install_replica_def)
  then have blocked: "pending_ids with_a_second_divergence \<noteq> {}" "pending_ids t \<noteq> {}"
    by (auto simp: pending_ids_def)
  show "client_recovery_view t = client_recovery_view with_a_second_divergence"
    using blocked by (simp add: client_recovery_view_def t_def install_replica_def)
  show "replica t 6 \<noteq> replica with_a_second_divergence 6 \<and>
      replica t 4 \<noteq> primary_record t \<and> work_owner t 10 = Some 4"
    using debt(2) the_handed_off_install_repairs_a_stale_value(1)
    by (simp add: t_def with_a_second_divergence_def install_replica_def)
qed

end
