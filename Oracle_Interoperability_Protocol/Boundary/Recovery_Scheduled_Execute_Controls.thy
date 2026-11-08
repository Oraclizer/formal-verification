theory Recovery_Scheduled_Execute_Controls
  imports Recovery_Ordinary_Execute_Control_Frames Recovery_Legal_Source_Control_Frames
    Recovery_Spend_Source_Control_Frames Recovery_Handover_Slot_Projections
begin

lemma captured_product_epoch_is_the_live_product_epoch:
  "product_authority_epoch (retained_authority (retained_source (capture_retained_product s))) =
    product_authority_epoch (product_durable (identity_source s))"
  by (simp add: ordinary_identity_source_is_the_outcome_source ordinary_capture_keeps_the_source_durable)

context source_attestation
begin

lemma every_scheduled_execute_keeps_the_captured_owner_map_and_epoch:
  assumes produced: "result = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection (Service_Execute route token proof target action authorization) R"
  shows "(product_owners (retained_authority (retained_source (fst result))),
      product_authority_epoch (retained_authority (retained_source (fst result)))) =
    (product_owners (retained_authority (retained_source R)), product_authority_epoch (retained_authority (retained_source R)))"
proof -
  let ?before = "reopen_retained_product connection R"
  have source_view: "retained_source (capture_retained_product ?before) = retained_source R"
    by (simp add: capture_retained_product_def reopen_retained_product_def initial_product_reads_def Let_def
      source_round_trip_retains_every_durable_field)
  have before_controls: "(product_owners (product_durable (outcome_source (current_product_outcomes ?before))),
      product_authority_epoch (product_durable (outcome_source (current_product_outcomes ?before)))) =
    (product_owners (retained_authority (retained_source R)), product_authority_epoch (retained_authority (retained_source R)))"
    using arg_cong[OF source_view, of "\<lambda>source.
      (product_owners (retained_authority source), product_authority_epoch (retained_authority source))"]
    by (simp add: captured_owner_map_is_the_live_owner_map captured_product_epoch_is_the_live_product_epoch
      owner_of_product_def ordinary_identity_source_is_the_outcome_source)
  show ?thesis
  proof (cases action)
    case Apply_Governed_Order
    then show ?thesis using produced before_controls
      by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def
        captured_owner_map_is_the_live_owner_map captured_product_epoch_is_the_live_product_epoch
        owner_of_product_def ordinary_identity_source_is_the_outcome_source legal_full_execute_keeps_source_controls[OF refl])
  next
    case Apply_Governed_Spend
    then show ?thesis using produced before_controls
      by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def
        captured_owner_map_is_the_live_owner_map captured_product_epoch_is_the_live_product_epoch
        owner_of_product_def ordinary_identity_source_is_the_outcome_source spend_full_execute_keeps_source_controls[OF refl])
  next
    case Collect_Governed_Order
    then show ?thesis using produced
      by (simp add: schedule_at_retained_state_def schedule_service_step_def durable_execute_def Let_def
        source_view split: option.splits prod.splits)
  next
    case Collect_Governed_Spend
    then show ?thesis using produced
      by (simp add: schedule_at_retained_state_def schedule_service_step_def durable_execute_def Let_def
        source_view split: option.splits prod.splits)
  next
    case (Ordinary_Product_Action read_action)
    show ?thesis
    proof (cases read_action)
      case Capture_Read
      then show ?thesis using Ordinary_Product_Action produced
        by (simp add: schedule_at_retained_state_def schedule_service_step_def durable_execute_def Let_def
          source_view split: option.splits prod.splits)
    next
      case Execute_Checked
      then show ?thesis using Ordinary_Product_Action produced before_controls
        by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def
          captured_owner_map_is_the_live_owner_map captured_product_epoch_is_the_live_product_epoch
          owner_of_product_def ordinary_identity_source_is_the_outcome_source ordinary_full_execute_keeps_source_controls[OF refl])
    next
      case Read_Authority_Action
      then show ?thesis using Ordinary_Product_Action produced
        by (simp add: schedule_at_retained_state_def schedule_service_step_def durable_execute_def Let_def
          source_view split: option.splits prod.splits)
    qed
  qed
qed

lemma a_changed_handover_cannot_share_any_execute_image:
  assumes handover: "result_a = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_a (Service_Handover owner_token successor_token maintainer proposal) R"
    and changed: "fst result_a \<noteq> R"
    and executed: "result_b = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_b (Service_Execute route token proof target action authorization) R"
  shows "fst result_a \<noteq> fst result_b"
proof
  assume same: "fst result_a = fst result_b"
  have owner_changed: "product_owners (retained_authority (retained_source (fst result_a))) \<noteq>
      product_owners (retained_authority (retained_source R))"
    by (rule a_changed_scheduled_handover_changes_the_captured_owner_map[OF handover changed])
  have controls: "(product_owners (retained_authority (retained_source (fst result_b))),
      product_authority_epoch (retained_authority (retained_source (fst result_b)))) =
    (product_owners (retained_authority (retained_source R)), product_authority_epoch (retained_authority (retained_source R)))"
    by (rule every_scheduled_execute_keeps_the_captured_owner_map_and_epoch[OF executed])
  have owner_frame: "product_owners (retained_authority (retained_source (fst result_b))) =
      product_owners (retained_authority (retained_source R))"
    using arg_cong[OF controls, of fst] by simp
  show False using owner_changed owner_frame same by simp
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms captured_product_epoch_is_the_live_product_epoch
      source_attestation.every_scheduled_execute_keeps_the_captured_owner_map_and_epoch
      source_attestation.a_changed_handover_cannot_share_any_execute_image})
  then () else error "Unexpected oracle in all scheduled Execute control projections"
\<close>

end
