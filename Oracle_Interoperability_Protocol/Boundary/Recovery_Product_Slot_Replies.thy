theory Recovery_Product_Slot_Replies
  imports "OIP_Product.Parallel_Step_Frame" Recovery_Queue_Reply_Binding
begin

text \<open>The same retained starting image may be reopened through different connections.
  Classification supplies the actual resolved slot on each side; equality of the connections or
  requested actions is not assumed.\<close>

context source_attestation
begin

lemma a_classified_observation_does_not_change_the_retained_image:
  assumes observation: "classify_service_action action (service_settlement (reopen_retained_product connection R)) =
    Service_Observation"
  shows "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection action R) = R"
proof -
  have unchanged: "fst (schedule_service_step directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    action (reopen_retained_product connection R)) = reopen_retained_product connection R"
    by (rule scheduled_observations_read_but_do_not_write[OF observation])
  show ?thesis by (simp add: schedule_at_retained_state_def Let_def unchanged
    product_round_trip_preserves_the_durable_projection)
qed

lemma two_changed_classified_slots_with_the_same_image_have_the_same_reply:
  assumes first: "classify_service_action a (service_settlement (reopen_retained_product c R)) = Service_Slot ra"
    and second: "classify_service_action b (service_settlement (reopen_retained_product c' R)) = Service_Slot rb"
    and changed: "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      c a R) \<noteq> R"
    and same: "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack c a R) =
      fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack c' b R)"
  shows "snd (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack c a R) =
    snd (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack c' b R)"
proof -
  let ?jobs = "retained_secondary R"
  let ?a = "step_settlement_slot verified_ack ra ?jobs"
  let ?b = "step_settlement_slot verified_ack rb ?jobs"
  have first_result: "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack c a R =
    (R\<lparr>retained_secondary := fst ?a\<rparr>, Scheduled_Settlement (snd ?a))"
    using classified_settlement_action_updates_only_its_real_slot[OF first] by (simp add: Let_def)
  have second_result: "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack c' b R =
    (R\<lparr>retained_secondary := fst ?b\<rparr>, Scheduled_Settlement (snd ?b))"
    using classified_settlement_action_updates_only_its_real_slot[OF second] by (simp add: Let_def)
  have changed_jobs: "fst ?a \<noteq> ?jobs"
    using changed first_result by auto
  have same_jobs: "fst ?a = fst ?b"
    using arg_cong[OF same, of retained_secondary] first_result second_result by simp
  have replies: "snd ?a = snd ?b"
    by (rule queue_slot_reply_is_determined_by_its_changed_map[OF changed_jobs same_jobs])
  show ?thesis using first_result second_result replies by simp
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.a_classified_observation_does_not_change_the_retained_image
      source_attestation.two_changed_classified_slots_with_the_same_image_have_the_same_reply})
  then () else error "Unexpected oracle in retained product slot replies"
\<close>

end
