theory Reference_Completion_Trace_Bounds
  imports Reference_Trace_Consumers "OIP_Product.Promotion_Trace_Execution"
begin

context reference_trace_consumer
begin

theorem a_reopened_reference_retry_collects_the_exact_ready_outcome_without_another_effect:
  fixes before live submitted outcomes prefix initial connection entry actor expected call_id payload
  defines "before \<equiv> run_reference_word execute prefix initial"
    and "live \<equiv> reopen_retained_product connection (reference_product before)"
    and "submitted \<equiv> Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)"
    and "outcomes \<equiv> current_product_outcomes live"
  assumes step: "serve connection (Service_Execute route token session target submitted authorization) supplied before = (after,Some reply)"
    and admitted: "authorized_endpoint_action directory policy authenticate verify route token session target submitted live"
    and access: "retained_receipt_permission policy authenticate token session target payload"
      "result_access_bound verified actor call_id payload outcomes"
    and active: "call_local_status (product_calls (identity_source live)) = Endpoint_Up"
    and ordinary: "unclaimed_regulated_call live call_id"
    and saved: "retained_outcomes (reference_product before) call_id = Some recorded"
    and exact: "result_payload recorded = payload"
    and released: "result_completion_ready recorded outcomes"
  shows "reply = Scheduled_Endpoint (Service_Execution_Result
          (Durable_Execution_Reply (Observed_Ordinary_Result (Collected (result_outcome recorded)))))"
    "retained_source (reference_product after) = retained_source (reference_product before)"
    "call_id \<in> retained_completed_ids (reference_product after)"
proof -
  let ?collect = "Ordinary_Product_Action (Read_Authority_Action (Exact_Collect actor call_id payload))"
  let ?completed = "outcomes\<lparr>outcome_completed := insert call_id (outcome_completed outcomes)\<rparr>"
  let ?next = "replace_product_outcomes ?completed live"
  have entry: "outcome_entries outcomes call_id = Some recorded"
    using saved by (simp add: outcomes_def live_def current_product_outcomes_def legal_underlying_outcomes_def
      reopen_retained_product_def initial_product_reads_def Let_def)
  have up: "call_local_status (product_calls (outcome_source outcomes)) = Endpoint_Up"
    using active by (simp add: outcomes_def outcome_source_is_the_endpoint_source)
  have complete: "complete_authoritative_result verified actor call_id payload outcomes = (?completed, Some (result_outcome recorded))"
    using up exact_retry_reads_the_committed_outcome[OF access(2) entry exact released]
    by (simp add: complete_authoritative_result_def)
  have observed: "observe_collection verified actor call_id payload outcomes = Collected (result_outcome recorded)"
    using access(2) up entry exact released by (simp add: observe_collection_def)
  let ?reply = "Durable_Execution_Reply (Observed_Ordinary_Result (Collected (result_outcome recorded)))"
  have finish: "finish_durable_execution verified actor ?collect live = (?next, ?reply)"
    using ordinary complete observed by (simp add: outcomes_def Let_def)
  have exists: "authority_has_call_id call_id live" using entry by (simp add: authority_has_call_id_def outcomes_def)
  let ?run = "durable_execute directory policy authenticate verify endorse route token session target submitted authorization
      legal_grant order_verified spend_grant spend_verified read_permitted (reference_permitted_at (reference_inputs before))
      verified maintainers registered verified_ack live"
  have claim: "external_call_claim submitted = Some (Execute_Ordinary,actor,call_id,payload)"
    and request: "execution_receipt_request submitted = Some ?collect"
    by (simp_all add: submitted_def)
  have uses_completion: "?run = finish_durable_execution verified actor ?collect live"
    by (rule an_admitted_exact_retry_checks_the_retained_result_before_fresh_conditions
      [OF claim request admitted active exists access(1)])
  have retry: "?run = (?next, ?reply)" by (rule trans[OF uses_completion finish])
  note scheduled = a_reference_step_uses_the_actual_service_with_the_retained_grants
    [OF step[unfolded actual_execute reference_service_input.select_convs]]
  have after: "reference_product after = capture_retained_product ?next"
    and reply: "reply = Scheduled_Endpoint (Service_Execution_Result ?reply)"
    using scheduled retry by (simp_all add: schedule_at_retained_state_def schedule_service_step_def live_def Let_def)
  show "reply = Scheduled_Endpoint (Service_Execution_Result ?reply)" by (rule reply)
  have source: "outcome_source (current_product_outcomes ?next) = outcome_source (current_product_outcomes live)"
    using finish finishing_does_not_reapply_authority_effects[of verified actor ?collect live] by simp
  have project: "retained_source (capture_retained_product s) = capture_retained_source (outcome_source (current_product_outcomes s))"
    for s
    by (simp add: capture_retained_product_def current_product_outcomes_def legal_underlying_outcomes_def Let_def)
  have reopened: "capture_retained_product live = reference_product before"
    unfolding live_def by (rule product_round_trip_preserves_the_durable_projection)
  show "retained_source (reference_product after) = retained_source (reference_product before)"
    unfolding after reopened[symmetric] project using source by simp
  have completion: "retained_completed_ids (capture_retained_product s) = outcome_completed (current_product_outcomes s)"
    for s
    by (simp add: capture_retained_product_def current_product_outcomes_def legal_underlying_outcomes_def Let_def)
  show "call_id \<in> retained_completed_ids (reference_product after)"
    by (simp add: after completion)
qed

theorem an_actual_secondary_delivery_step_keeps_the_primary_and_pending_after_every_prefix:
  fixes before prefix initial
  defines "before \<equiv> run_reference_word execute prefix initial"
  assumes start: "reference_service_contract registered genesis initial"
    and delivery: "is_settlement_action action"
  shows "let step = serve connection (Service_Maintenance action) supplied before;
       retained = reference_product (fst step)
     in retained_decisions retained = retained_decisions (reference_product before) \<and>
       retained_source retained = retained_source (reference_product before)"
proof -
  have grants: "reference_grants_fit registered (reference_product before) (reference_inputs before)"
    unfolding before_def by (rule a_reference_prefix_consumes_the_current_grants[OF start])
  let ?service = "Service_Maintenance action"
  let ?live = "reopen_retained_product connection (reference_product before)"
  have nonserial: "classify_service_action ?service (service_settlement ?live) \<noteq> Service_Serial"
    using delivery by (simp split: option.splits)
  let ?schedule = "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
     legal_grant order_verified spend_grant spend_verified read_permitted (reference_permitted_at (reference_inputs before))
     verified maintainers registered verified_ack connection ?service (reference_product before)"
  have actual: "serve connection ?service supplied before =
      (before\<lparr>reference_product := fst ?schedule\<rparr>, Some (snd ?schedule))"
    unfolding actual_execute reference_service_input.select_convs
    by (rule a_nonserial_reference_step_keeps_the_live_grants[OF grants nonserial, unfolded Let_def])
  let ?result = "execute_settlement_action verified_ack action (service_settlement ?live)"
  have local_effect: "fst ?schedule = (reference_product before)\<lparr>retained_secondary := settlement_jobs (fst ?result)\<rparr>"
    using delivery by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def
      replacing_queue_keeps_the_retained_primary_fields product_round_trip_preserves_the_durable_projection)
  show ?thesis
    by (simp add: actual local_effect Let_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    reference_trace_consumer.a_reopened_reference_retry_collects_the_exact_ready_outcome_without_another_effect
    reference_trace_consumer.an_actual_secondary_delivery_step_keeps_the_primary_and_pending_after_every_prefix})
  then () else error "Unexpected oracle in reference completion and secondary delivery"
\<close>

end
