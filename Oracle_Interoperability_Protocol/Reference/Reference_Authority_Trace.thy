theory Reference_Authority_Trace
  imports Reference_Authority_Grants "OIP_Product.Promotion_Trace_Retention"
begin

context source_attestation
begin

lemma a_reference_step_uses_the_actual_service_with_the_retained_grants:
  assumes "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
    authenticated connection action supplied before = (after, Some reply)"
  shows "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted
    (reference_permitted_at (reference_inputs before)) verified maintainers registered verified_ack
    connection action (reference_product before) = (reference_product after, reply)"
  using assms by (auto simp: service_at_reference_snapshot_def Let_def split: if_splits option.splits)

theorem a_reference_step_keeps_replay_and_genesis_under_current_grants:
  assumes before: "retained_source_replay_valid (reference_product before)"
    and grants: "reference_grants_fit registered (reference_product before) (reference_inputs before)"
    and step: "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
      authenticated connection action supplied before = (after, response)"
  shows "retained_source_replay_valid (reference_product after) \<and>
    retained_genesis (retained_source (reference_product after)) =
      retained_genesis (retained_source (reference_product before)) \<and>
    reference_grants_fit registered (reference_product after) (reference_inputs after)"
proof (cases response)
  case None
  have unchanged: "after = before"
    by (rule reference_service_refusal_leaves_the_exact_snapshot[OF step[unfolded None]])
  show ?thesis using before grants by (simp add: unchanged)
next
  case (Some reply)
  have service: "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted
    (reference_permitted_at (reference_inputs before)) verified maintainers registered verified_ack
    connection action (reference_product before) = (reference_product after, reply)"
    by (rule a_reference_step_uses_the_actual_service_with_the_retained_grants[OF step[unfolded Some]])
  let ?action_result = "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted
    (reference_permitted_at (reference_inputs before)) verified maintainers registered verified_ack
    connection action (reference_product before)"
  have original_replay: "retained_source_replay_valid (fst ?action_result)"
    by (rule scheduled_product_step_preserves_exact_authority_replay[OF before])
  have replay: "retained_source_replay_valid (reference_product after)"
    using original_replay service by simp
  have original_genesis: "retained_genesis (retained_source (fst ?action_result)) =
      retained_genesis (retained_source (reference_product before))"
    by (rule scheduled_product_step_keeps_the_fixed_public_genesis)
  have genesis: "retained_genesis (retained_source (reference_product after)) =
      retained_genesis (retained_source (reference_product before))"
    using original_genesis service by simp
  have coherent: "reference_grants_fit registered (reference_product after) (reference_inputs after)"
    by (rule reference_service_success_preserves_epoch_and_grant_binding[OF step[unfolded Some]])
  show ?thesis using replay genesis coherent by blast
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.a_reference_step_uses_the_actual_service_with_the_retained_grants
      source_attestation.a_reference_step_keeps_replay_and_genesis_under_current_grants})
  then () else error "Unexpected oracle in reference authority trace"
\<close>

end
