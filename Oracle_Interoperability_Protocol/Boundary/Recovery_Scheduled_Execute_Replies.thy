theory Recovery_Scheduled_Execute_Replies
  imports Recovery_Durable_Execute_Reply_Pairs "OIP_Product.Parallel_Service"
begin

context source_attestation
begin

lemma equal_changed_scheduled_execute_images_determine_the_reply:
  assumes produced_a: "result_a = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_a (Service_Execute route_a token_a proof_a target_a action_a authorization_a) R"
    and produced_b: "result_b = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_b (Service_Execute route_b token_b proof_b target_b action_b authorization_b) R"
    and changed_a: "fst result_a \<noteq> R"
    and same_images: "fst result_a = fst result_b"
  shows "snd result_a = snd result_b"
proof -
  let ?before_a = "reopen_retained_product connection_a R"
  let ?before_b = "reopen_retained_product connection_b R"
  let ?raw_a = "durable_execute directory policy authenticate verify endorse route_a token_a proof_a target_a action_a authorization_a
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack ?before_a"
  let ?raw_b = "durable_execute directory policy authenticate verify endorse route_b token_b proof_b target_b action_b authorization_b
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack ?before_b"
  have shape_a: "result_a = (capture_retained_product (fst ?raw_a), Scheduled_Endpoint (Service_Execution_Result (snd ?raw_a)))"
    using produced_a by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def)
  have shape_b: "result_b = (capture_retained_product (fst ?raw_b), Scheduled_Endpoint (Service_Execution_Result (snd ?raw_b)))"
    using produced_b by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def)
  have before_images: "capture_retained_product ?before_a = capture_retained_product ?before_b"
    by (simp add: product_round_trip_preserves_the_durable_projection)
  have changed: "capture_retained_product (fst ?raw_a) \<noteq> capture_retained_product ?before_a"
    using shape_a changed_a by (simp add: product_round_trip_preserves_the_durable_projection)
  have same: "capture_retained_product (fst ?raw_a) = capture_retained_product (fst ?raw_b)"
    using shape_a shape_b same_images by simp
  have replies: "snd ?raw_a = snd ?raw_b"
    by (rule equal_changed_durable_execute_images_determine_the_reply[OF refl refl before_images changed same])
  show ?thesis using shape_a shape_b replies by simp
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.equal_changed_scheduled_execute_images_determine_the_reply})
  then () else error "Unexpected oracle in actual scheduled Execute reply pairs"
\<close>

end
