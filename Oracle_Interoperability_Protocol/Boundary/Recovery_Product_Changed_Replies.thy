theory Recovery_Product_Changed_Replies
  imports "OIP_Product.Parallel_Service"
begin

text \<open>These changing constructors have fixed success reply tags. Execution-result reconstruction
  and separation of different changing constructors are separate proof interfaces.\<close>

context source_attestation
begin

lemma a_changed_owner_handover_has_the_true_handover_reply:
  assumes changed: "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection (Service_Handover owner_token successor_token maintainer proposal) R) \<noteq> R"
  shows "snd (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection (Service_Handover owner_token successor_token maintainer proposal) R) =
      Scheduled_Endpoint (Service_Handover_Result True)"
proof -
  let ?before = "reopen_retained_product connection R"
  let ?after = "handover_product_owner directory policy authenticate approve owner_token successor_token maintainer
    maintainers registered proposal ?before"
  have effect: "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection (Service_Handover owner_token successor_token maintainer proposal) R) = capture_retained_product ?after"
    by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def)
  have live_changed: "?after \<noteq> ?before"
  proof
    assume "?after = ?before"
    then have "capture_retained_product ?after = R"
      by (simp add: product_round_trip_preserves_the_durable_projection)
    then show False using changed effect by simp
  qed
  show ?thesis using live_changed
    by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def)
qed

lemma nonsettlement_maintenance_uses_the_boolean_reply:
  assumes "\<not> is_settlement_action action"
  shows "persistent_maintenance_reply action before after = Service_Maintenance_Result (after \<noteq> before)"
  using assms by (cases action) auto

lemma a_changed_nonsettlement_maintenance_has_the_true_maintenance_reply:
  assumes nonsettlement: "\<not> is_settlement_action action"
    and changed: "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection (Service_Maintenance action) R) \<noteq> R"
  shows "snd (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection (Service_Maintenance action) R) = Scheduled_Endpoint (Service_Maintenance_Result True)"
proof (cases "persistent_maintenance_allowed action")
  case False
  then show ?thesis using changed nonsettlement
    by (simp add: schedule_at_retained_state_def schedule_service_step_def
      product_round_trip_preserves_the_durable_projection Let_def)
next
  case allowed: True
  let ?before = "reopen_retained_product connection R"
  let ?reads = "regulated_read_world ?before"
  let ?after = "replace_regulated_reads (?reads\<lparr>read_authority := exact_step permitted verified maintainers
    registered verified_ack action (read_authority ?reads)\<rparr>) ?before"
  have effect: "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection (Service_Maintenance action) R) = capture_retained_product ?after"
    using nonsettlement allowed by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def)
  have live_changed: "?after \<noteq> ?before"
  proof
    assume "?after = ?before"
    then have "capture_retained_product ?after = R" by (simp add: product_round_trip_preserves_the_durable_projection)
    then show False using changed effect by simp
  qed
  have reply: "persistent_maintenance_reply action ?before ?after = Service_Maintenance_Result True"
    using nonsettlement_maintenance_uses_the_boolean_reply[OF nonsettlement, of ?before ?after] live_changed by simp
  show ?thesis using nonsettlement allowed reply
    by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.a_changed_owner_handover_has_the_true_handover_reply
      source_attestation.nonsettlement_maintenance_uses_the_boolean_reply
      source_attestation.a_changed_nonsettlement_maintenance_has_the_true_maintenance_reply})
  then () else error "Unexpected oracle in fixed-tag changing product replies"
\<close>

end
