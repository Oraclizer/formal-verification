theory DOSP_Retained_Failure_Case
  imports DOSP_Retained_Settlement_Cases
begin

abbreviation rolled_back_measurement where
  "rolled_back_measurement \<equiv> \<lparr>measuring_authority = 41, measured_request = quoted_request, measured_clock = 86400,
    measured_reply = transition_result.Operational_Failure Rolled_Back, measured_write_domains = {0,2},
    measured_final_leaves = {}\<rparr>"

abbreviation rolled_back_input where
  "rolled_back_input \<equiv> \<lparr>verified_observations = [], verified_measurements = [rolled_back_measurement]\<rparr>"

theorem a_failed_retained_commit_is_publicly_pending_and_records_the_failure:
  "\<exists>q row. joined_dosp.product_source_step example_versions {} rolled_back_input {} {} two_journals current_repair_head []
      leave_origin_grant retired_before_settlement (Record_Native_Commit_Failure quoted_request (sample_request 23))
      (Native_Settlement_Pending (0,23)) q \<and>
    source_consensus q = before_second_meter \<and> cycle_custody (source_lifecycle q) = Native_Debit_Pending (0,23) \<and>
    lifecycle_phase (source_lifecycle q) = Partial_Cycle quoted_request (binding_state (degree_state pre_meter_operational)) \<and>
    product_public_usage q = product_public_usage retired_before_settlement @ [row] \<and>
    public_abort_cause row = Some Network_Abort \<and> public_billing_day row = 1"
proof -
  let ?p = "retired_before_settlement"
  let ?s = "stale_local_clock_view\<lparr>lifecycle_clock := 86400\<rparr>"
  let ?cut = "degree_state pre_meter_operational"
  let ?fault = "transition_result.Operational_Failure Rolled_Back :: cutover_result"
  let ?abort = "\<lparr>accounted_attempt = cycle_attempt_id quoted_request, accounted_binding = cycle_binding_id quoted_request,
    accounted_session = cycle_session_id quoted_request, accounted_ticket = cycle_ticket quoted_request,
    accounted_clock = 86400, accounted_footprint = {0,2}, accounted_payload = 0, accounted_abort = Some Network_Abort,
    accounted_tariff = 4, accounted_schedule = example_price\<rparr>"
  let ?state = "?s\<lparr>lifecycle_phase := Partial_Cycle quoted_request (binding_state ?cut),
    lifecycle_invoice := append_accounted_cycle (lifecycle_invoice ?s) ?abort\<rparr>"
  let ?q = "?p\<lparr>source_lifecycle := ?state\<rparr>"
  have same_native_context: "retained_credit_admission ?p quoted_request 0 (sample_request 23) =
    retained_credit_admission second_candidate_product quoted_request 0 (sample_request 23)"
    by (simp add: retained_credit_admission_def Let_def)
  have original: "retained_credit_admission ?p quoted_request 0 (sample_request 23)"
    by (simp only: same_native_context second_native_source_is_already_debited_and_confirmed)
  have held: "current_binding_holds_its_native_lock pre_meter_operational (sample_request 23)"
    using original unfolding retained_credit_admission_def by (simp add: Let_def)
  have bound_key: "binding_key (request_binding (sample_request 23)) \<notin> core_published (credit_core pre_meter_operational)"
    using original unfolding retained_credit_admission_def by (simp add: Let_def)
  have named: "cycle_names_native_binding quoted_request (sample_request 23)"
    by (simp add: cycle_names_native_binding_def second_request_fields request_flow_def Let_def)
  have current: "binding_is_current coupling_policy ?s quoted_request"
    by (simp add: binding_is_current_def authority_registry_def ticket_authorizes_def issue_route_ticket_def
      joined_ticket_def request_flow_def can_commit_def coupling_policy_def second_meter_operational_fields
      billing_record_def promoted_metadata_def prod_encode_eq first_accounted_usage_def)
  have on_current_cutover: "can_commit coupling_policy (lifecycle_cutover ?s) (cycle_binding_id quoted_request)
      (ticket_metadata (cycle_ticket quoted_request)) (request_flow quoted_request)"
    using current unfolding binding_is_current_def by blast
  have may_commit: "can_commit coupling_policy ?cut (cycle_binding_id quoted_request)
      (ticket_metadata (cycle_ticket quoted_request)) (request_flow quoted_request)"
    using on_current_cutover by simp
  have permitted: "ticket_authorizes (lifecycle_registry ?s) coupling_policy (fst (cycle_session_id quoted_request))
      (cycle_ticket quoted_request) (request_flow quoted_request)"
    using current unfolding binding_is_current_def by blast
  have flow: "flow_step coupling_policy Atomic False (binding_state ?cut) (request_flow quoted_request)
      (transition_result.Operational_Failure Rolled_Back) (binding_state ?cut)"
    by (simp add: flow_step_def request_flow_def coupling_policy_def)
  have native_failure: "cutover_step coupling_policy {(12,4)} ?cut
      (Commit_Binding (cycle_binding_id quoted_request) (ticket_metadata (cycle_ticket quoted_request)) 0 2 5 False)
      ?fault (?cut\<lparr>binding_state := binding_state ?cut,
        unreconciled_soft_write := unreconciled_soft_write ?cut \<or> Rolled_Back = Partial_Write\<rparr>)"
  proof (rule cutover_step.Binding_Failed[where a="request_flow quoted_request"])
    show "request_flow quoted_request = Commit_From 0 2 5" by (simp add: request_flow_def)
    show "can_commit coupling_policy ?cut (cycle_binding_id quoted_request)
      (ticket_metadata (cycle_ticket quoted_request)) (request_flow quoted_request)" by (rule may_commit)
    show "flow_step coupling_policy (chosen_path (ticket_metadata (cycle_ticket quoted_request))) False (binding_state ?cut)
      (request_flow quoted_request) (transition_result.Operational_Failure Rolled_Back) (binding_state ?cut)"
      using flow by (simp add: promoted_metadata_def joined_ticket_def)
  qed
  have failed: "cutover_step coupling_policy {(12,4)} ?cut (request_commit quoted_request False) ?fault ?cut"
    using native_failure by (simp add: request_commit_def)
  have booked: "metered_attempt coupling_policy {(12,4)} example_versions rolled_back_input ?s quoted_request False ?fault ?cut = Some ?abort"
    unfolding metered_attempt_def observed_commit_charge_def
    using failed permitted
    by (simp add: request_commit_def request_flow_def checked_final_leaves_def reports_for_commit_def example_versions_def Let_def)
  have lifecycle: "lifecycle_step coupling_policy {(12,4)} example_versions {} rolled_back_input
      (promotion_locks_clear coupling_policy pre_meter_operational)
      ?s (Commit_Cycle False) (Cycle_Result ?fault) ?state"
    using lifecycle_step.Commit[OF _ current booked] by simp
  have before_coherent: "recorded_success_history ?s = billing_history ?cut"
    by (simp add: recorded_success_history_def accounted_cutover_entry_def first_accounted_usage_def
      joined_ticket_def coupling_ticket_def second_meter_operational_fields billing_record_def fixture_binding)
  have a: "with_operational_state ((current_operational before_second_meter)\<lparr>degree_state := ?cut\<rparr>) before_second_meter =
    before_second_meter"
    by (simp add: with_operational_state_def)
  have result: "joint_failed_credit_step (coupling_policy,{(12,4)},(17,7,3)) (example_versions,{},rolled_back_input)
      (?p,quoted_request,sample_request 23,Cycle_Result ?fault,?q)"
    unfolding joint_failed_credit_step_def
    using lifecycle held bound_key named original before_coherent a
    by (auto simp: recovery_permits_existing_native_credit_def published_recovery_state_def pending_ids_def
      tariffs_cover_recorded_usage_def first_accounted_usage_def example_versions_def
      second_meter_operational_fields(6) Let_def intro: exI[of _ 0] exI[of _ Rolled_Back] exI[of _ ?state])
  have at_boundary: "joined_dosp.product_source_step example_versions {} rolled_back_input {} {} two_journals current_repair_head []
      leave_origin_grant ?p (Record_Native_Commit_Failure quoted_request (sample_request 23))
      (Native_Settlement_Pending (0,23)) ?q"
    using joined_dosp.a_required_pending_debit_is_reported_as_awaiting_settlement[OF result, where key="(0,23)"]
    by simp
  show ?thesis using at_boundary
    by (intro exI[of _ ?q] exI[of _ "usage_row_for_epoch ?abort"])
      (simp add: product_public_usage_def usage_row_for_epoch_def append_accounted_cycle_def
        first_accounted_usage_def settlement_epoch_def billing_day_def Let_def)
qed

end
