theory DOSP_Repin_Cases
  imports DOSP_Billing_Public
begin

abbreviation repinned_ticket where "repinned_ticket \<equiv> joined_ticket 1 (promoted_metadata 9 5)"
abbreviation repinned_request where
  "repinned_request \<equiv> episode_request\<lparr>cycle_attempt_id := (34,10), cycle_ticket := repinned_ticket\<rparr>"
abbreviation repinned_bound where
  "repinned_bound \<equiv> episode_promoted\<lparr>lifecycle_phase := Bound_Cycle repinned_request\<rparr>"
abbreviation repinned_verified where
  "repinned_verified \<equiv> repinned_bound\<lparr>lifecycle_phase := Verified_Cycle repinned_request\<rparr>"
abbreviation repinned_evidence where
  "repinned_evidence \<equiv> episode_evidence\<lparr>verified_measurements :=
    [episode_measurement\<lparr>measured_request := repinned_request, measured_reply := transition_result.Accepted Binding_Committed\<rparr>]\<rparr>"
abbreviation repinned_step where
  "repinned_step \<equiv> lifecycle_step two_origin_policy {(9,5)} example_versions
    {exact_restoration,another_restoration} repinned_evidence True"

theorem the_next_commit_uses_the_repinned_registry_entry_and_rate:
  "repinned_step episode_promoted (Bind_Cycle repinned_request) Cycle_Bound repinned_bound"
  "repinned_step repinned_bound (Verify_Cycle []) Cycle_Verified repinned_verified"
  "\<exists>t. repinned_step repinned_verified (Commit_Cycle True)
    (Cycle_Result (transition_result.Accepted Binding_Committed)) t \<and>
    map (public_meter_version \<circ> usage_row_for_epoch) (lifecycle_invoice t) = [4,5] \<and>
    public_session_bill 100 example_versions (17,7,3) (map usage_row_for_epoch (lifecycle_invoice t)) = Some 100000"
proof -
  let ?s = "lifecycle_cutover episode_promoted"
  let ?a = "Commit_From (1::nat) 2 10"
  let ?meta = "promoted_metadata 9 5"
  let ?core = "?s\<lparr>binding_state := fst (evaluate_flow two_origin_policy Atomic True (binding_state ?s) ?a),
     billing_history := billing_history ?s @ [billing_record 1 ?meta ?a]\<rparr>"
  let ?price = "example_price\<lparr>failure_fraction := 50, degree_weight := level_rank(Atomic := 4)\<rparr>"
  let ?row = "(observed_failure_row Client_Abort)\<lparr>accounted_attempt := (34,10), accounted_ticket := repinned_ticket,
    accounted_abort := None, accounted_tariff := 5, accounted_schedule := ?price\<rparr>"
  note model = finish_promotion_def episode_restored_def episode_initial_def episode_request_def
  have current: "binding_is_current two_origin_policy episode_promoted repinned_request"
    "binding_is_current two_origin_policy repinned_verified repinned_request"
    by (simp_all add: binding_is_current_def model soft_start_def cutover_start_def ticket_authorizes_def issue_route_ticket_def
      joined_ticket_def request_flow_def can_commit_def observed_failure_row_def promoted_metadata_def two_origin_policy_def)
  show "repinned_step episode_promoted (Bind_Cycle repinned_request) Cycle_Bound repinned_bound"
    by (rule lifecycle_step.Bind[OF _ _ current(1)]) (simp_all add: model soft_start_def cutover_start_def)
  have held: "lifecycle_phase repinned_bound = Bound_Cycle repinned_request" by simp
  show "repinned_step repinned_bound (Verify_Cycle []) Cycle_Verified repinned_verified"
    by (rule lifecycle_step.Verify[OF held])
  have cutover: "cutover_step two_origin_policy {(9,5)} ?s (Commit_Binding 1 ?meta 1 2 10 True)
    (transition_result.Accepted Binding_Committed) ?core"
    by (rule cutover_step.Commit[where a="?a"])
      (simp_all add: model can_commit_def flow_step_def soft_start_def cutover_start_def
        promoted_metadata_def two_origin_policy_def)
  have measure: "checked_final_leaves repinned_evidence repinned_verified repinned_request
      (transition_result.Accepted Binding_Committed) = Some 5"
    by (simp add: checked_final_leaves_def episode_measurement_def request_flow_def model)
  have guard: "ticket_authorizes (lifecycle_registry episode_promoted) two_origin_policy 17 repinned_ticket ?a"
    using current(1) by (simp add: binding_is_current_def episode_request_def request_flow_def)
  have charge: "metered_attempt two_origin_policy {(9,5)} example_versions repinned_evidence repinned_verified repinned_request True
    (transition_result.Accepted Binding_Committed) ?core = Some ?row"
    unfolding metered_attempt_def measure option.case
    using cutover guard by (simp add: model observed_commit_charge_def observed_failure_row_def example_versions_def joined_ticket_def Let_def)
  have phase: "lifecycle_phase repinned_verified = Verified_Cycle repinned_request" by simp
  note actual = lifecycle_step.Commit[OF phase current(2) charge,
    where restoration_confirmed="{exact_restoration,another_restoration}" and locks_clear=True]
  let ?post = "repinned_verified\<lparr>lifecycle_cutover := ?core,
    lifecycle_invoice := append_accounted_cycle (lifecycle_invoice repinned_verified) ?row, lifecycle_phase := Idle_Cycle\<rparr>"
  have step: "repinned_step repinned_verified (Commit_Cycle True)
      (Cycle_Result (transition_result.Accepted Binding_Committed)) ?post"
    using actual by simp
  show "\<exists>t. repinned_step repinned_verified (Commit_Cycle True)
    (Cycle_Result (transition_result.Accepted Binding_Committed)) t \<and>
    map (public_meter_version \<circ> usage_row_for_epoch) (lifecycle_invoice t) = [4,5] \<and>
    public_session_bill 100 example_versions (17,7,3) (map usage_row_for_epoch (lifecycle_invoice t)) = Some 100000"
    using step by (intro exI[of _ ?post])
      (simp add: model append_accounted_cycle_def observed_failure_row_def public_session_bill_def charge_from_public_row_def
       usage_row_for_epoch_def example_versions_def example_price_def soft_ticket_def joined_ticket_def soft_start_def
       cutover_start_def old_plan_def promoted_metadata_def Let_def)
qed

end
