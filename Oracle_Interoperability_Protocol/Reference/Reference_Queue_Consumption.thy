theory Reference_Queue_Consumption
  imports Reference_Authority_Trace
begin

definition reference_queue_at where
  "reference_queue_at connection snapshot =
    service_settlement (reopen_retained_product connection (reference_product snapshot))"

lemma retained_queue_is_the_actual_scheduled_queue:
  "retained_secondary (capture_retained_product live) = settlement_jobs (service_settlement live)"
  by (simp add: capture_retained_product_def service_settlement_def regulated_read_world_def Let_def)

context source_attestation
begin

lemma the_reference_ack_consumes_the_exact_scheduled_queue_action:
  assumes service: "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
    authenticated connection (Service_Maintenance (Exact_Acknowledge ack)) supplied before = (after, Some reply)"
  shows "retained_secondary (reference_product after) =
      settlement_jobs (acknowledge_secondary verified_ack ack (reference_queue_at connection before))"
    "retained_source (reference_product after) = retained_source (reference_product before)"
    "reply = Scheduled_Settlement (snd (execute_settlement_action verified_ack
      (Exact_Acknowledge ack) (reference_queue_at connection before)))"
proof -
  let ?live = "reopen_retained_product connection (reference_product before)"
  let ?scheduled = "execute_settlement_action verified_ack (Exact_Acknowledge ack) (service_settlement ?live)"
  have actual: "reference_product after =
      capture_retained_product (replace_service_jobs (settlement_jobs (fst ?scheduled)) ?live)"
    using a_reference_step_uses_the_actual_service_with_the_retained_grants[OF service]
    by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def)
  show "retained_secondary (reference_product after) =
      settlement_jobs (acknowledge_secondary verified_ack ack (reference_queue_at connection before))"
    by (simp add: actual retained_queue_is_the_actual_scheduled_queue
        reference_queue_at_def exact_queue_effect_is_the_existing_endpoint_effect Let_def)
  show "retained_source (reference_product after) = retained_source (reference_product before)"
    unfolding actual retained_call_source_is_the_actual_product_source
    by (simp add: recovery_projection_supplies_the_exact_source source_round_trip_retains_every_durable_field)
  show "reply = Scheduled_Settlement (snd (execute_settlement_action verified_ack
      (Exact_Acknowledge ack) (reference_queue_at connection before)))"
    using a_reference_step_uses_the_actual_service_with_the_retained_grants[OF service]
    by (simp add: schedule_at_retained_state_def schedule_service_step_def reference_queue_at_def Let_def)
qed

theorem the_actual_reference_service_completes_only_the_verified_ack_job:
  assumes service: "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
    authenticated connection (Service_Maintenance (Exact_Acknowledge ack)) supplied before = (after, Some reply)"
    and "settlement_jobs (reference_queue_at connection before) (ack_settlement_key ack) = Some job"
    "exact_secondary_ack ack job" "verified_ack ack" "secondary_attempts job > 0"
  shows "retained_secondary (reference_product after) (ack_settlement_key ack) =
      Some (job\<lparr>secondary_state := Secondary_Completed\<rparr>)"
    "retained_source (reference_product after) = retained_source (reference_product before)"
proof -
  have completed: "settlement_jobs (acknowledge_secondary verified_ack ack (reference_queue_at connection before))
      (ack_settlement_key ack) = Some (job\<lparr>secondary_state := Secondary_Completed\<rparr>)"
    by (rule exact_verified_ack_completes_the_recorded_job[where verified=verified_ack, OF assms(2-5)])
  show "retained_secondary (reference_product after) (ack_settlement_key ack) =
      Some (job\<lparr>secondary_state := Secondary_Completed\<rparr>)"
    using completed by (simp add: the_reference_ack_consumes_the_exact_scheduled_queue_action(1)[OF service])
  show "retained_source (reference_product after) = retained_source (reference_product before)"
    by (rule the_reference_ack_consumes_the_exact_scheduled_queue_action(2)[OF service])
qed

lemma an_unverified_ack_cannot_advance_the_reference_queue:
  assumes service: "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
    authenticated connection (Service_Maintenance (Exact_Acknowledge ack)) supplied before = (after, Some reply)"
    and invalid: "\<not> verified_ack ack"
  shows "retained_secondary (reference_product after) = retained_secondary (reference_product before)"
    "reply = Scheduled_Settlement (Settlement_Changed False)"
  using the_reference_ack_consumes_the_exact_scheduled_queue_action[OF service] invalid
  by (simp_all add: acknowledge_secondary_def update_secondary_job_def reference_queue_at_def
    service_settlement_def regulated_read_world_def reopen_retained_product_def initial_product_reads_def
    execute_settlement_action_def step_settlement_slot_def fun_upd_idem Let_def split: option.splits)

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.the_reference_ack_consumes_the_exact_scheduled_queue_action
      source_attestation.the_actual_reference_service_completes_only_the_verified_ack_job
      source_attestation.an_unverified_ack_cannot_advance_the_reference_queue})
  then () else error "Unexpected oracle in actual reference ACK consumption"
\<close>

end
