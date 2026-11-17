theory DOSP_Lifecycle_Defense_Cases
  imports DOSP_Lifecycle_Defense DOSP_Router_Defense_Cases
begin

definition episode_request :: cycle_request where
  "episode_request = \<lparr>cycle_attempt_id = (34,9), cycle_session_id = (17,7,3), cycle_binding_id = 1,
    cycle_ticket = soft_ticket, cycle_source = 1, cycle_target = 2, cycle_value = 10\<rparr>"

definition episode_initial :: lifecycle_state where
  "episode_initial = \<lparr>lifecycle_cutover = soft_start, lifecycle_phase = Idle_Cycle, lifecycle_clock = 86400,
    lifecycle_session = (17,7,3), lifecycle_tariff = 4, lifecycle_registry = soft_registry,
    cycle_custody = Local_Cells_Only, lifecycle_diagnostic_authorities = {41}, lifecycle_invoice = []\<rparr>"

abbreviation episode_bound :: lifecycle_state where
  "episode_bound \<equiv> episode_initial\<lparr>lifecycle_phase := Bound_Cycle episode_request\<rparr>"

abbreviation episode_verified :: lifecycle_state where
  "episode_verified \<equiv> episode_initial\<lparr>lifecycle_phase := Verified_Cycle episode_request\<rparr>"

definition client_observation :: commit_observation where
  "client_observation = \<lparr>observing_authority = 41, observed_request = episode_request, observed_clock = 86400,
    observed_failure = Partial_Write, observed_cause = Client_Regulation_Failure\<rparr>"

definition episode_partial :: lifecycle_state where
  "episode_partial = episode_verified\<lparr>lifecycle_cutover := partial_commit,
    lifecycle_phase := Partial_Cycle episode_request (binding_state soft_start),
    lifecycle_invoice := [observed_failure_row Client_Abort]\<rparr>"

definition exact_restoration :: restoration_evidence where
  "exact_restoration = \<lparr>restoration_attempt = (34,9), restoration_ticket = soft_ticket,
    restoration_values = binding_state soft_start\<rparr>"

abbreviation another_restoration :: restoration_evidence where
  "another_restoration \<equiv> exact_restoration\<lparr>restoration_attempt := (34,8)\<rparr>"

abbreviation wrong_ticket_restoration :: restoration_evidence where
  "wrong_ticket_restoration \<equiv> exact_restoration\<lparr>restoration_ticket := soft_ticket\<lparr>ticket_initiator := 2\<rparr>\<rparr>"

abbreviation episode_accounts :: "commit_observation list" where
  "episode_accounts \<equiv> [client_observation,client_observation\<lparr>observed_clock := 86399, observed_cause := Lock_Timeout\<rparr>]"

definition episode_measurement :: commit_measurement where
  "episode_measurement = \<lparr>measuring_authority = 41, measured_request = episode_request, measured_clock = 86400,
    measured_reply = transition_result.Operational_Failure Partial_Write, measured_write_domains = {1,2},
    measured_final_leaves = {1,2,3,4,5}\<rparr>"

abbreviation episode_evidence :: commit_evidence where
  "episode_evidence \<equiv> \<lparr>verified_observations = episode_accounts, verified_measurements = [episode_measurement]\<rparr>"

abbreviation episode_step where
  "episode_step locks \<equiv> lifecycle_step two_origin_policy {(9,5)} example_versions
     {exact_restoration,another_restoration} episode_evidence locks"

definition episode_restored :: lifecycle_state where
  "episode_restored = episode_initial\<lparr>lifecycle_invoice := [observed_failure_row Client_Abort]\<rparr>"

abbreviation episode_promoted :: lifecycle_state where
  "episode_promoted \<equiv> finish_promotion episode_restored
    (soft_start\<lparr>route_metadata := promoted_metadata 9 5\<rparr>) 5"

lemma episode_current_in_preparation:
  "binding_is_current two_origin_policy episode_initial episode_request"
  "binding_is_current two_origin_policy episode_verified episode_request"
  by (simp_all add: binding_is_current_def can_commit_def request_flow_def ticket_authorizes_def issue_route_ticket_def
      soft_registry_def joined_ticket_def episode_initial_def episode_request_def soft_ticket_def soft_start_def
      old_plan_def cutover_start_def two_origin_policy_def)

lemma episode_observations_are_scoped_to_the_actual_attempt:
  "reports_for_commit episode_accounts episode_verified episode_request
    (transition_result.Operational_Failure Partial_Write) = [Client_Regulation_Failure]"
  "reports_for_commit [client_observation\<lparr>observed_clock := 86399\<rparr>,
      client_observation\<lparr>observed_request := episode_request\<lparr>cycle_attempt_id := (34,8)\<rparr>\<rparr>]
    episode_verified episode_request (transition_result.Operational_Failure Partial_Write) = []"
  "reports_for_commit [client_observation] episode_verified episode_request
    (transition_result.Operational_Failure Rolled_Back) = []"
  "reports_for_commit [client_observation\<lparr>observing_authority := 52\<rparr>] episode_verified episode_request
    (transition_result.Operational_Failure Partial_Write) = []"
  by (simp_all add: reports_for_commit_def client_observation_def episode_initial_def episode_request_def)

lemma authoritative_leaf_count_rejects_wrong_domains_and_conflicting_final_sets:
  "checked_final_leaves episode_evidence episode_verified episode_request
    (transition_result.Operational_Failure Partial_Write) = Some 5"
  "checked_final_leaves (episode_evidence\<lparr>verified_measurements := [episode_measurement\<lparr>measured_write_domains := {1}\<rparr>]\<rparr>)
    episode_verified episode_request (transition_result.Operational_Failure Partial_Write) = None"
  "checked_final_leaves (episode_evidence\<lparr>verified_measurements :=
      [episode_measurement, episode_measurement\<lparr>measured_final_leaves := {1,2,3,4,6}\<rparr>]\<rparr>)
    episode_verified episode_request (transition_result.Operational_Failure Partial_Write) = None"
proof -
  have distinct: "{1,2,3,4,5::nat} \<noteq> {1,2,3,4,6}" by (intro notI) (drule arg_cong[where f="(\<in>) (5::nat)"], simp)
  then show "checked_final_leaves (episode_evidence\<lparr>verified_measurements :=
      [episode_measurement, episode_measurement\<lparr>measured_final_leaves := {1,2,3,4,6}\<rparr>]\<rparr>)
    episode_verified episode_request (transition_result.Operational_Failure Partial_Write) = None"
    by (simp add: checked_final_leaves_def episode_measurement_def request_flow_def episode_initial_def episode_request_def)
qed (simp_all add: checked_final_leaves_def episode_measurement_def request_flow_def episode_initial_def episode_request_def)

lemma a_restoration_cannot_be_reused_for_another_routing_ticket:
  "lifecycle_step two_origin_policy {(9,5)} example_versions {wrong_ticket_restoration} episode_evidence True
    episode_partial (Restore_Cycle wrong_ticket_restoration) Restoration_Refused episode_partial"
  by (rule lifecycle_step.Restore_Refused)
    (simp add: restoration_matches_def episode_partial_def exact_restoration_def episode_request_def soft_ticket_def joined_ticket_def)

theorem an_actual_partial_commit_blocks_promotion_until_the_exact_restoration:
  "episode_step True episode_initial (Bind_Cycle episode_request) Cycle_Bound episode_bound"
  "episode_step True episode_bound (Verify_Cycle []) Cycle_Verified episode_verified"
  "episode_step True episode_bound (Commit_Cycle False) Precommit_Refused episode_bound"
  "episode_step True episode_bound (Promote_Cycle 9 5) Lifecycle_Promotion_Refused episode_bound"
  "episode_step True episode_verified (Commit_Cycle False)
    (Cycle_Result (transition_result.Operational_Failure Partial_Write)) episode_partial"
  "episode_step True episode_partial (Promote_Cycle 9 5) Lifecycle_Promotion_Refused episode_partial"
  "episode_step True episode_partial (Restore_Cycle another_restoration) Restoration_Refused episode_partial"
  "episode_step True episode_partial (Restore_Cycle exact_restoration) Cycle_Restored episode_restored"
  "episode_step False episode_restored (Promote_Cycle 9 5) Lifecycle_Promotion_Refused episode_restored"
  "episode_step True episode_restored (Bind_Cycle episode_request) Precommit_Refused episode_restored"
  "episode_step True episode_restored (Promote_Cycle 9 5) Lifecycle_Promoted episode_promoted"
  "episode_step True episode_promoted (Bind_Cycle (episode_request\<lparr>cycle_attempt_id := (34,10)\<rparr>))
    Precommit_Refused episode_promoted"
proof -
  show "episode_step True episode_initial (Bind_Cycle episode_request) Cycle_Bound episode_bound"
    by (rule lifecycle_step.Bind[OF _ _ episode_current_in_preparation(1)])
      (simp_all add: episode_initial_def soft_start_def cutover_start_def)
  show "episode_step True episode_bound (Verify_Cycle []) Cycle_Verified episode_verified"
  proof -
    have "episode_step True episode_bound (Verify_Cycle []) Cycle_Verified
      (episode_bound\<lparr>lifecycle_phase := Verified_Cycle episode_request\<rparr>)"
      by (rule lifecycle_step.Verify) simp
    then show ?thesis by simp
  qed
  show "episode_step True episode_bound (Commit_Cycle False) Precommit_Refused episode_bound"
    by (rule lifecycle_step.Commit_Without_Verification) simp
  show "episode_step True episode_bound (Promote_Cycle 9 5) Lifecycle_Promotion_Refused episode_bound"
    by (rule lifecycle_step.Promote_Refused) (simp add: lifecycle_promotable_def)
  have bill: "metered_attempt two_origin_policy {(9,5)} example_versions episode_evidence
    episode_verified episode_request False (transition_result.Operational_Failure Partial_Write) partial_commit =
      Some (observed_failure_row Client_Abort)"
    using charge_from_the_actual_partial_write_path[of "[Client_Regulation_Failure]"]
    unfolding metered_attempt_def authoritative_leaf_count_rejects_wrong_domains_and_conflicting_final_sets(1)
      option.case commit_evidence.select_convs episode_observations_are_scoped_to_the_actual_attempt(1)
    by (simp add: episode_initial_def episode_request_def reports_for_commit_def client_observation_def)
  have phase: "lifecycle_phase episode_verified = Verified_Cycle episode_request" by simp
  note commit = lifecycle_step.Commit[OF phase episode_current_in_preparation(2) bill,
    where restoration_confirmed="{exact_restoration,another_restoration}" and locks_clear=True]
  show "episode_step True episode_verified (Commit_Cycle False)
    (Cycle_Result (transition_result.Operational_Failure Partial_Write)) episode_partial"
    using commit by (simp add: episode_partial_def episode_initial_def append_accounted_cycle_def)
  show "episode_step True episode_partial (Promote_Cycle 9 5) Lifecycle_Promotion_Refused episode_partial"
    by (rule lifecycle_step.Promote_Refused) (simp add: lifecycle_promotable_def episode_partial_def)
  show "episode_step True episode_partial (Restore_Cycle another_restoration) Restoration_Refused episode_partial"
    by (rule lifecycle_step.Restore_Refused)
      (simp add: restoration_matches_def episode_partial_def exact_restoration_def episode_request_def)
  have evidence: "restoration_matches {exact_restoration,another_restoration} episode_partial exact_restoration"
    by (simp add: restoration_matches_def episode_partial_def episode_initial_def exact_restoration_def episode_request_def)
  show "episode_step True episode_partial (Restore_Cycle exact_restoration) Cycle_Restored episode_restored"
    using lifecycle_step.Restore[OF evidence, where policy=two_origin_policy and grants="{(9,5)}"
      and versions=example_versions and verified=episode_evidence and locks_clear=True]
    by (simp add: episode_restored_def episode_partial_def episode_initial_def partial_commit_def
      exact_restoration_def soft_start_def cutover_start_def)
  show "episode_step False episode_restored (Promote_Cycle 9 5) Lifecycle_Promotion_Refused episode_restored"
    by (rule lifecycle_step.Promote_Refused) (simp add: lifecycle_promotable_def)
  show "episode_step True episode_restored (Bind_Cycle episode_request) Precommit_Refused episode_restored"
    by (rule lifecycle_step.Bind_Refused)
      (simp add: binding_is_current_def episode_restored_def episode_request_def observed_failure_row_def)
  have allowed: "promotion_allowed {(9,5)} (lifecycle_cutover episode_restored) 9 5"
    by (simp add: promotion_allowed_def episode_restored_def episode_initial_def soft_start_def cutover_start_def old_plan_def)
  show "episode_step True episode_restored (Promote_Cycle 9 5) Lifecycle_Promoted episode_promoted"
    using lifecycle_step.Promote[OF _ _ cutover_step.Promote[OF allowed], where locks_clear=True and policy=two_origin_policy
      and versions=example_versions and verified=episode_evidence
      and restoration_confirmed="{exact_restoration,another_restoration}"]
    by (simp add: lifecycle_promotable_def episode_restored_def episode_initial_def example_versions_def soft_registry_def)
  show "episode_step True episode_promoted (Bind_Cycle (episode_request\<lparr>cycle_attempt_id := (34,10)\<rparr>))
    Precommit_Refused episode_promoted"
    by (rule lifecycle_step.Bind_Refused)
      (simp add: binding_is_current_def finish_promotion_def episode_restored_def episode_initial_def episode_request_def soft_ticket_def joined_ticket_def
        soft_start_def cutover_start_def old_plan_def promoted_metadata_def)
qed

definition full_session_usage where
  "full_session_usage precision session history = precision * precision + invoice_usage precision session history"

lemma historical_failed_attempt_survives_cutover_without_repricing:
  "lifecycle_invoice episode_promoted = [observed_failure_row Client_Abort]"
  "full_session_usage 100 (17,7,3) (lifecycle_invoice episode_promoted) = 20000"
  "settlement_epoch (hd (lifecycle_invoice episode_promoted)) = 1"
proof -
  show rows: "lifecycle_invoice episode_promoted = [observed_failure_row Client_Abort]"
    by (simp add: episode_restored_def finish_promotion_def)
  have bill: "invoice_usage 100 (17,7,3) [observed_failure_row Client_Abort] = 10000"
    using failed_commit_price_requires_attribution_and_survives_replay(6)
    by (simp add: repeated_attempt_does_not_charge_twice append_accounted_cycle_def)
  show "full_session_usage 100 (17,7,3) (lifecycle_invoice episode_promoted) = 20000"
    using bill by (simp add: rows full_session_usage_def)
  show "settlement_epoch (hd (lifecycle_invoice episode_promoted)) = 1"
    by (simp add: rows failed_commit_price_requires_attribution_and_survives_replay(8))
qed

end
