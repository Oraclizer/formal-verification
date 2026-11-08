theory Recovery_Maintenance_Separation
  imports Recovery_Maintenance_Projections Recovery_Execute_Change_Discriminants
begin

context source_attestation
begin

lemma a_changed_scheduled_execute_changes_an_execute_reply_discriminant:
  assumes produced: "result = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection (Service_Execute route token proof target action authorization) R"
    and changed: "fst result \<noteq> R"
  shows "(retained_outcomes (fst result), retained_completed_ids (fst result),
      retained_legal_receipts (fst result), retained_spend_receipts (fst result)) \<noteq>
    (retained_outcomes R, retained_completed_ids R, retained_legal_receipts R, retained_spend_receipts R)"
proof -
  let ?before = "reopen_retained_product connection R"
  let ?raw = "durable_execute directory policy authenticate verify endorse route token proof target action authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack ?before"
  have round_trip: "capture_retained_product ?before = R" by (rule product_round_trip_preserves_the_durable_projection)
  have effect: "fst result = capture_retained_product (fst ?raw)"
    using produced by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def)
  have raw_changed: "capture_retained_product (fst ?raw) \<noteq> capture_retained_product ?before"
    using changed effect round_trip by simp
  show ?thesis using every_changed_durable_execute_changes_a_reply_discriminant[OF raw_changed] effect round_trip by simp
qed

lemma a_changed_nonsettlement_maintenance_cannot_share_any_execute_image:
  assumes maintained: "result_a = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_a (Service_Maintenance maintenance) R"
    and nonsettlement: "\<not> is_settlement_action maintenance"
    and changed: "fst result_a \<noteq> R"
    and executed: "result_b = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_b (Service_Execute route token proof target action authorization) R"
  shows "fst result_a \<noteq> fst result_b"
proof
  assume same: "fst result_a = fst result_b"
  have execute_changed: "fst result_b \<noteq> R" using changed same by simp
  have discriminant: "(retained_outcomes (fst result_b), retained_completed_ids (fst result_b),
      retained_legal_receipts (fst result_b), retained_spend_receipts (fst result_b)) \<noteq>
    (retained_outcomes R, retained_completed_ids R, retained_legal_receipts R, retained_spend_receipts R)"
    by (rule a_changed_scheduled_execute_changes_an_execute_reply_discriminant[OF executed execute_changed])
  have frame: "(retained_outcomes (fst result_a), retained_completed_ids (fst result_a),
      retained_legal_receipts (fst result_a), retained_spend_receipts (fst result_a)) =
    (retained_outcomes R, retained_completed_ids R, retained_legal_receipts R, retained_spend_receipts R)"
    by (rule every_scheduled_maintenance_keeps_all_execute_reply_discriminants[OF maintained])
  show False using discriminant frame same by simp
qed

lemma a_changed_nonsettlement_maintenance_cannot_share_a_classified_slot_image:
  assumes maintained: "result_a = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_a (Service_Maintenance maintenance) R"
    and nonsettlement: "\<not> is_settlement_action maintenance"
    and changed: "fst result_a \<noteq> R"
    and slot: "classify_service_action action (service_settlement (reopen_retained_product connection_b R)) = Service_Slot resolved"
    and scheduled: "result_b = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_b action R"
  shows "fst result_a \<noteq> fst result_b"
proof
  assume same: "fst result_a = fst result_b"
  have source_changed: "retained_source (fst result_a) \<noteq> retained_source R"
    by (rule a_changed_nonsettlement_maintenance_changes_the_captured_source[OF maintained nonsettlement changed])
  have source_frame: "retained_source (fst result_b) = retained_source R"
    by (rule a_classified_slot_keeps_all_nonsecondary_reply_discriminants(1)[OF slot scheduled])
  show False using source_changed source_frame same by simp
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.a_changed_scheduled_execute_changes_an_execute_reply_discriminant
      source_attestation.a_changed_nonsettlement_maintenance_cannot_share_any_execute_image
      source_attestation.a_changed_nonsettlement_maintenance_cannot_share_a_classified_slot_image})
  then () else error "Unexpected oracle in corrected maintenance/Execute/slot separation"
\<close>

end
