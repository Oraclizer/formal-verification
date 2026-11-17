theory DOSP_Soft_Retry_Cases
  imports DOSP_Lifecycle_Defense_Cases
begin

abbreviation retry_request where
  "retry_request \<equiv> episode_request\<lparr>cycle_attempt_id := (34,10)\<rparr>"

abbreviation retry_evidence where
  "retry_evidence \<equiv> episode_evidence\<lparr>verified_measurements :=
    [episode_measurement\<lparr>measured_request := retry_request, measured_reply := transition_result.Accepted Binding_Committed\<rparr>]\<rparr>"

lemma a_failed_soft_commit_can_retry_the_same_binding_forward:
  "\<exists>t. lifecycle_step two_origin_policy {(9,5)} example_versions
     {exact_restoration,another_restoration} retry_evidence True episode_partial
     (Retry_Cycle (34,10)) (Cycle_Result (transition_result.Accepted Binding_Committed)) t \<and>
    lifecycle_phase t = Idle_Cycle \<and> \<not> unreconciled_soft_write (lifecycle_cutover t) \<and>
    committed (binding_state (lifecycle_cutover t)) 1 = 10 \<and>
    committed (binding_state (lifecycle_cutover t)) 2 = 10 \<and>
    map accounted_binding (lifecycle_invoice t) = [1,1] \<and>
    map accounted_abort (lifecycle_invoice t) = [Some Client_Abort,None]"
proof -
  note fixture = episode_partial_def episode_initial_def episode_request_def soft_registry_def
    soft_ticket_def joined_ticket_def partial_commit_def soft_start_def cutover_start_def old_plan_def two_origin_policy_def
  let ?action = "Commit_From (1::nat) 2 10"
  let ?updated = "partial_commit\<lparr>
    binding_state := fst (evaluate_flow two_origin_policy Coupled True (binding_state partial_commit) ?action),
    billing_history := billing_history partial_commit @ [billing_record 1 (route_metadata partial_commit) ?action]\<rparr>"
  let ?row = "(observed_failure_row Client_Abort)\<lparr>accounted_attempt := (34,10), accounted_abort := None\<rparr>"
  have phase: "lifecycle_phase episode_partial = Partial_Cycle episode_request (binding_state soft_start)"
    by (simp add: episode_partial_def)
  have current: "binding_is_current two_origin_policy episode_partial retry_request"
    by (simp add: binding_is_current_def ticket_authorizes_def issue_route_ticket_def can_commit_def
      request_flow_def observed_failure_row_def fixture)
  have native: "cutover_step two_origin_policy {(9,5)} partial_commit
    (Commit_Binding 1 (route_metadata partial_commit) 1 2 10 True) (transition_result.Accepted Binding_Committed) ?updated"
    by (rule cutover_step.Commit[where a="?action"]) (simp_all add: can_commit_def flow_step_def fixture)
  have count: "checked_final_leaves retry_evidence episode_partial retry_request (transition_result.Accepted Binding_Committed) = Some 5"
    by (simp add: checked_final_leaves_def episode_measurement_def request_flow_def fixture)
  have bill: "metered_attempt two_origin_policy {(9,5)} example_versions retry_evidence episode_partial retry_request True
    (transition_result.Accepted Binding_Committed) ?updated = Some ?row"
    unfolding metered_attempt_def count option.case
    using native current by (simp add: observed_commit_charge_def binding_is_current_def request_flow_def
      ticket_authorizes_def issue_route_ticket_def observed_failure_row_def example_versions_def fixture Let_def)
  have local_only: "cycle_custody episode_partial = Local_Cells_Only" by (simp add: episode_partial_def episode_initial_def)
  note retry = lifecycle_step.Retry[OF phase refl current bill local_only,
    where restoration_confirmed="{exact_restoration,another_restoration}" and locks_clear=True]
  let ?t = "episode_partial\<lparr>lifecycle_cutover := ?updated\<lparr>unreconciled_soft_write := False\<rparr>,
    lifecycle_invoice := append_accounted_cycle (lifecycle_invoice episode_partial) ?row, lifecycle_phase := Idle_Cycle\<rparr>"
  show ?thesis
    using retry by (intro exI[of _ ?t])
      (simp add: fixture append_accounted_cycle_def observed_failure_row_def)
qed

end
