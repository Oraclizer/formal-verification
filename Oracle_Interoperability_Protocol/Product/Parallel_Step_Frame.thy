theory Parallel_Step_Frame
  imports Parallel_Service
begin

lemma reopening_after_a_queue_write_keeps_the_exact_primary_view:
  "reopen_retained_product connection (retained\<lparr>retained_secondary := jobs\<rparr>) =
   replace_service_jobs jobs (reopen_retained_product connection retained)"
  by (simp add: reopen_retained_product_def replace_service_jobs_def replace_regulated_reads_def
       regulated_read_world_def initial_product_reads_def Let_def)

lemma reopened_queue_is_the_retained_queue [simp]:
  "settlement_jobs (service_settlement (reopen_retained_product connection retained)) = retained_secondary retained"
  by (simp add: service_settlement_def reopen_retained_product_def regulated_read_world_def initial_product_reads_def Let_def)

lemma queue_replacement_does_not_change_service_class:
  "classify_service_action action (s\<lparr>settlement_jobs := jobs\<rparr>) = classify_service_action action s"
  by (cases action) (simp_all add: queue_resolution_does_not_read_another_job)

context source_attestation
begin

lemma scheduled_observations_read_but_do_not_write:
  assumes "classify_service_action action (service_settlement s) = Service_Observation"
  shows "fst (schedule_service_step directory policy read_policy authenticate verify verify_read endorse approve
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action s) = s"
  using assms by (cases action)
    (auto simp: schedule_service_step_def execute_settlement_action_def Let_def split: option.splits if_splits)

lemma scheduled_observation_reply_is_independent_of_all_queue_writes:
  assumes "classify_service_action action (service_settlement s) = Service_Observation"
  shows "snd (schedule_service_step directory policy read_policy authenticate verify verify_read endorse approve
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
     action (replace_service_jobs jobs s)) =
    snd (schedule_service_step directory policy read_policy authenticate verify verify_read endorse approve
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action s)"
  using assms by (cases action)
    (auto simp: schedule_service_step_def execute_settlement_action_def Let_def queue_resolution_does_not_read_another_job
      authorized_receipt_observation_ignores_the_queue retained_current_or_historical_reply_ignores_the_queue
      capturing_the_observation_does_not_read_the_queue split: option.splits if_splits)

lemma slot_operation_is_the_actual_shared_endpoint_step:
  assumes "classify_service_action action (service_settlement s) = Service_Slot resolved"
  shows "let result = step_settlement_slot verified_ack resolved (settlement_jobs (service_settlement s)) in
    schedule_service_step directory policy read_policy authenticate verify verify_read endorse approve
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action s =
       (replace_service_jobs (fst result) s, Scheduled_Settlement (snd result))"
  using assms by (cases action)
    (auto simp: schedule_service_step_def execute_settlement_action_def Let_def split: option.splits if_splits)

lemma classified_settlement_action_updates_only_its_real_slot:
  assumes "classify_service_action action (service_settlement (reopen_retained_product connection retained)) = Service_Slot resolved"
  shows "let result = step_settlement_slot verified_ack resolved (retained_secondary retained) in
    schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
     connection action retained =
       (retained\<lparr>retained_secondary := fst result\<rparr>, Scheduled_Settlement (snd result))"
proof -
  let ?s = "reopen_retained_product connection retained"
  let ?result = "step_settlement_slot verified_ack resolved (settlement_jobs (service_settlement ?s))"
  have actual: "schedule_service_step directory policy read_policy authenticate verify verify_read endorse approve
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action ?s =
       (replace_service_jobs (fst ?result) ?s, Scheduled_Settlement (snd ?result))"
    by (rule slot_operation_is_the_actual_shared_endpoint_step[unfolded Let_def, OF assms])
  show ?thesis
    by (simp add: schedule_at_retained_state_def Let_def actual replacing_queue_keeps_the_retained_primary_fields
        product_round_trip_preserves_the_durable_projection)
qed

end

end
