theory Scheduler_Proof_Inspection
  imports Scheduler_Lasso Request_Example
begin

ML \<open>
val thy = @{theory}
fun closure seen facts =
  fold (fn (_, name) => fn collected =>
    if Thm_Name.Set.member collected name then collected
    else closure (Thm_Name.Set.insert name collected)
      [Global_Theory.get_thm_name thy (name, Position.none)])
    (Thm_Deps.thm_deps thy facts) seen

val theorem_roots = @{thms
  rejection_cannot_occupy_a_priority_slot failed_signature_leaves_the_id_available
  new_epoch_removes_old_priority_eligibility a_regulatory_rollback_executes_the_assured_handler
  ordinary_service_records_the_head_packet waiting_persists_without_its_service
  waiting_rank_nonincreasing serving_an_earlier_ordinary_packet_decreases_rank
  finite_escalation_interference_bound priority_beyond_the_ceiling_needs_a_non_escalation
  cut_accounts_for_scheduler_step initial_ordinary_cohort_completes
  receipt_requires_an_ordinary_service queued_packet_is_served_under_finite_interference
  admitted_packet_is_served_under_finite_interference admitted_packet_is_served_under_fixed_case_escalation
  finite_interference_when_only_fixed_cases_escalate
  starvation_in_a_fixed_case_run_needs_infinitely_many_non_escalating_turns
  starvation_with_only_fixed_case_level_changes_requires_infinite_lowering
  rejected_spam_does_not_poison_the_real_id regulation_then_exact_ordinary_completion
  real_epoch_changes_remove_old_priority scheduled_regulatory_rollback_uses_the_exact_assured_intent
  after_a_rotation_with_no_eligible_regulation_the_next_honest_turn_serves_the_head
  rotated_fixtures_actually_service_the_waiting_ordinary_packet
  malformed_ordinary_input_is_a_nonservice_fault
  finite_interference_alone_cannot_force_service repeated_legal_de_escalation_starves_the_pending_ordinary_packet
  source_selected_ordinary_packet_is_really_served source_selected_packet_served_under_fixed_escalation
  deployment_execution_controls admitted_manifest_alone_cannot_unlock_deployment
  deployment_consumer_uses_the_request_completion_receipt
  deployment_application_publishes_only_the_observed_manifest same_id_wrong_manifest_exposes_the_other_digest}

val provider = @{thm Recovery_Progress.eventual_completion_under_finite_interference}
val verified_rollback = @{thm Rollback_Contracts.accepted_rollback}
val progress_closure = closure Thm_Name.Set.empty
  @{thms admitted_packet_is_served_under_finite_interference admitted_packet_is_served_under_fixed_case_escalation
    deployment_consumer_uses_the_request_completion_receipt deployment_application_publishes_only_the_observed_manifest}
val rollback_closure = closure Thm_Name.Set.empty
  @{thms a_regulatory_rollback_executes_the_assured_handler}
val _ = if null (Thm_Deps.all_oracles theorem_roots) then ()
  else error "An oracle occurs in the scheduler claim-root closure"
val _ = if Thm_Name.Set.member progress_closure (Thm.get_name_hint provider) then ()
  else error "The completion theorem is absent from the actual request progress proof"
val _ = if Thm_Name.Set.member rollback_closure (Thm.get_name_hint verified_rollback) then ()
  else error "The authorized rollback theorem is absent from the scheduled rollback proof"
val lines = cat_lines [
  "claim_fact_instances=" ^ string_of_int (length theorem_roots),
  "transitive_oracles=0",
  "provider_dependency=" ^ Thm_Name.print (Thm.get_name_hint provider),
  "rollback_dependency=" ^ Thm_Name.print (Thm.get_name_hint verified_rollback),
  "request_progress_named_dependency_count=" ^
    string_of_int (length (Thm_Name.Set.dest progress_closure)),
  "request_progress_named_dependencies",
  cat_lines (map Thm_Name.print (Thm_Name.Set.dest progress_closure))]
val _ = Export.export thy (Path.binding0 (Path.explode "reos/scheduler-trust.txt")) [XML.Text lines]
\<close>

end
