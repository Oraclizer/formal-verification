theory Recovery_Handover_Slot_Projections
  imports Recovery_Ordinary_Projection "OIP_Product.Parallel_Step_Frame"
begin

lemma captured_owner_map_is_the_live_owner_map:
  "product_owners (retained_authority (retained_source (capture_retained_product s))) = owner_of_product (identity_source s)"
  by (simp add: owner_of_product_def ordinary_identity_source_is_the_outcome_source
    ordinary_capture_keeps_the_source_durable)

context source_attestation
begin

lemma a_changed_scheduled_handover_changes_the_captured_owner_map:
  assumes produced: "result = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection (Service_Handover owner_token successor_token maintainer proposal) R"
    and changed: "fst result \<noteq> R"
  shows "product_owners (retained_authority (retained_source (fst result))) \<noteq>
    product_owners (retained_authority (retained_source R))"
proof -
  let ?before = "reopen_retained_product connection R"
  let ?source = "identity_source ?before"
  let ?next_source = "apply_owner_handover directory policy authenticate approve owner_token successor_token maintainer
    maintainers registered proposal ?source"
  let ?after = "handover_product_owner directory policy authenticate approve owner_token successor_token maintainer
    maintainers registered proposal ?before"
  have round_trip: "capture_retained_product ?before = R"
    by (rule product_round_trip_preserves_the_durable_projection)
  have effect: "fst result = capture_retained_product ?after"
    using produced by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def)
  have admit: "handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer
      maintainers registered proposal ?source"
  proof (rule ccontr)
    assume denied: "\<not> handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer
      maintainers registered proposal ?source"
    have "?after = ?before" using denied by (simp add: handover_product_owner_def)
    then have "fst result = R" using effect round_trip by simp
    then show False using changed by simp
  qed
  have after_source: "identity_source ?after = ?next_source"
    using admit by (simp add: handover_product_owner_def replace_identity_source_consumes_the_same_authority)
  have owners: "owner_of_product ?next_source =
      (owner_of_product ?source)(transfer_asset proposal := Some (transfer_successor proposal))"
    by (rule handover_atomically_changes_owner_and_sessions_without_spending(1)[OF admit])
  have old_owner: "owner_of_product ?source (transfer_asset proposal) = Some (transfer_previous proposal)"
    and distinct_owners: "transfer_previous proposal \<noteq> transfer_successor proposal"
    using admit by (simp_all add: handover_is_authorized_def Let_def)
  have before_owners: "product_owners (retained_authority (retained_source R)) = owner_of_product ?source"
    using round_trip captured_owner_map_is_the_live_owner_map[of ?before] by simp
  have after_owners: "product_owners (retained_authority (retained_source (fst result))) = owner_of_product ?next_source"
    using effect after_source by (simp add: captured_owner_map_is_the_live_owner_map)
  show ?thesis
  proof
    assume same: "product_owners (retained_authority (retained_source (fst result))) =
      product_owners (retained_authority (retained_source R))"
    have same_at: "product_owners (retained_authority (retained_source (fst result))) (transfer_asset proposal) =
      product_owners (retained_authority (retained_source R)) (transfer_asset proposal)"
      using arg_cong[OF same, of "\<lambda>owner_map. owner_map (transfer_asset proposal)"] .
    have "transfer_successor proposal = transfer_previous proposal"
      using same_at before_owners after_owners owners old_owner by simp
    then show False using distinct_owners by simp
  qed
qed

lemma a_classified_slot_keeps_all_nonsecondary_reply_discriminants:
  assumes slot: "classify_service_action action (service_settlement (reopen_retained_product connection R)) = Service_Slot resolved"
    and produced: "result = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection action R"
  shows "retained_source (fst result) = retained_source R"
    and "retained_outcomes (fst result) = retained_outcomes R"
    and "retained_completed_ids (fst result) = retained_completed_ids R"
    and "retained_legal_receipts (fst result) = retained_legal_receipts R"
    and "retained_spend_receipts (fst result) = retained_spend_receipts R"
proof -
  let ?before = "reopen_retained_product connection R"
  let ?operation = "step_settlement_slot verified_ack resolved (settlement_jobs (service_settlement ?before))"
  have actual: "schedule_service_step directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      action ?before = (replace_service_jobs (fst ?operation) ?before, Scheduled_Settlement (snd ?operation))"
    by (rule slot_operation_is_the_actual_shared_endpoint_step[unfolded Let_def, OF slot])
  have source_view: "retained_source (capture_retained_product ?before) = retained_source R"
    and outcome_view: "retained_outcomes (capture_retained_product ?before) = retained_outcomes R"
    and completed_view: "retained_completed_ids (capture_retained_product ?before) = retained_completed_ids R"
    and legal_view: "retained_legal_receipts (capture_retained_product ?before) = retained_legal_receipts R"
    and spend_view: "retained_spend_receipts (capture_retained_product ?before) = retained_spend_receipts R"
    by (simp_all add: capture_retained_product_def reopen_retained_product_def initial_product_reads_def Let_def
      source_round_trip_retains_every_durable_field)
  show "retained_source (fst result) = retained_source R"
    and "retained_outcomes (fst result) = retained_outcomes R"
    and "retained_completed_ids (fst result) = retained_completed_ids R"
    and "retained_legal_receipts (fst result) = retained_legal_receipts R"
    and "retained_spend_receipts (fst result) = retained_spend_receipts R"
    using produced actual source_view outcome_view completed_view legal_view spend_view
    by (simp_all add: schedule_at_retained_state_def Let_def replacing_queue_keeps_the_retained_primary_fields)
qed

lemma a_changed_handover_cannot_share_the_image_of_a_classified_slot:
  assumes handover: "result_a = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_a (Service_Handover owner_token successor_token maintainer proposal) R"
    and changed: "fst result_a \<noteq> R"
    and slot: "classify_service_action action (service_settlement (reopen_retained_product connection_b R)) = Service_Slot resolved"
    and scheduled: "result_b = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_b action R"
  shows "fst result_a \<noteq> fst result_b"
proof
  assume same: "fst result_a = fst result_b"
  have owners_changed: "product_owners (retained_authority (retained_source (fst result_a))) \<noteq>
      product_owners (retained_authority (retained_source R))"
    by (rule a_changed_scheduled_handover_changes_the_captured_owner_map[OF handover changed])
  have source_frame: "retained_source (fst result_b) = retained_source R"
    by (rule a_classified_slot_keeps_all_nonsecondary_reply_discriminants(1)[OF slot scheduled])
  show False using owners_changed source_frame same by simp
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms captured_owner_map_is_the_live_owner_map
      source_attestation.a_changed_scheduled_handover_changes_the_captured_owner_map
      source_attestation.a_classified_slot_keeps_all_nonsecondary_reply_discriminants
      source_attestation.a_changed_handover_cannot_share_the_image_of_a_classified_slot})
  then () else error "Unexpected oracle in handover and actual slot projections"
\<close>

end
