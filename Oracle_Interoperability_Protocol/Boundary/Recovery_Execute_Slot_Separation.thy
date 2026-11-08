theory Recovery_Execute_Slot_Separation
  imports Recovery_Execute_Change_Discriminants Recovery_Handover_Slot_Projections
begin

context source_attestation
begin

lemma a_changed_scheduled_execute_cannot_share_a_classified_slot_image:
  assumes executed: "result_a = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_a (Service_Execute route token proof target action authorization) R"
    and changed: "fst result_a \<noteq> R"
    and slot: "classify_service_action other (service_settlement (reopen_retained_product connection_b R)) = Service_Slot resolved"
    and scheduled: "result_b = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_b other R"
  shows "fst result_a \<noteq> fst result_b"
proof
  let ?before = "reopen_retained_product connection_a R"
  let ?raw = "durable_execute directory policy authenticate verify endorse route token proof target action authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack ?before"
  have round_trip: "capture_retained_product ?before = R"
    by (rule product_round_trip_preserves_the_durable_projection)
  have effect: "fst result_a = capture_retained_product (fst ?raw)"
    using executed by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def)
  have raw_changed: "capture_retained_product (fst ?raw) \<noteq> capture_retained_product ?before"
    using changed effect round_trip by simp
  have discriminant: "(retained_outcomes (fst result_a), retained_completed_ids (fst result_a),
      retained_legal_receipts (fst result_a), retained_spend_receipts (fst result_a)) \<noteq>
    (retained_outcomes R, retained_completed_ids R, retained_legal_receipts R, retained_spend_receipts R)"
    using every_changed_durable_execute_changes_a_reply_discriminant[OF raw_changed] effect round_trip by simp
  have slot_frame: "(retained_outcomes (fst result_b), retained_completed_ids (fst result_b),
      retained_legal_receipts (fst result_b), retained_spend_receipts (fst result_b)) =
    (retained_outcomes R, retained_completed_ids R, retained_legal_receipts R, retained_spend_receipts R)"
    using a_classified_slot_keeps_all_nonsecondary_reply_discriminants(2-5)[OF slot scheduled] by simp
  assume same: "fst result_a = fst result_b"
  show False using discriminant slot_frame same by simp
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.a_changed_scheduled_execute_cannot_share_a_classified_slot_image})
  then () else error "Unexpected oracle in actual scheduled Execute/slot separation"
\<close>

end
