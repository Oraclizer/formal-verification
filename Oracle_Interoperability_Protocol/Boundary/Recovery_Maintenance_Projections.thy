theory Recovery_Maintenance_Projections
  imports Recovery_Scheduled_Execute_Controls
begin

lemma capturing_an_exact_source_replacement_changes_only_retained_source:
  "capture_retained_product (replace_identity_source source s) =
    (capture_retained_product s)\<lparr>retained_source := capture_retained_source source\<rparr>"
  by (simp add: replace_identity_source_def capture_retained_product_def regulated_read_world_def
    replace_regulated_reads_def update_settlement_outcomes_def Let_def)

context source_attestation
begin

lemma every_lock_product_step_keeps_the_product_owner_map:
  "owner_of_product (lock_product_step permitted verified maintainers registered action source) = owner_of_product source"
  by (cases action)
    (simp_all add: owner_of_product_def product_apply_public_def
      ordinary_lock_submission_keeps_owner_epoch_sessions_and_local_status split: if_splits)

lemma maintenance_non_submit_is_an_exact_source_replacement:
  "replace_regulated_reads ((regulated_read_world s)
      \<lparr>read_authority := apply_non_submit_lock_action permitted maintainers registered action
        (read_authority (regulated_read_world s))\<rparr>) s =
    replace_identity_source (lock_product_step permitted (\<lambda>_ _ _ _. True) maintainers registered action (identity_source s)) s"
  by (simp add: apply_non_submit_lock_action_def replace_identity_source_def identity_source_def observed_product_source_def
    regulated_read_world_def update_settlement_outcomes_def Let_def)

lemma maintenance_non_submit_replacement_uses_its_exact_source_step:
  "identity_source (replace_regulated_reads ((regulated_read_world s)
      \<lparr>read_authority := apply_non_submit_lock_action permitted maintainers registered action
        (read_authority (regulated_read_world s))\<rparr>) s) =
    lock_product_step permitted (\<lambda>_ _ _ _. True) maintainers registered action (identity_source s)"
  by (simp only: maintenance_non_submit_is_an_exact_source_replacement replace_identity_source_consumes_the_same_authority)

lemma every_scheduled_maintenance_keeps_the_captured_owner_map:
  assumes produced: "result = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection (Service_Maintenance action) R"
  shows "product_owners (retained_authority (retained_source (fst result))) = product_owners (retained_authority (retained_source R))"
proof -
  let ?before = "reopen_retained_product connection R"
  have before_owner: "owner_of_product (identity_source ?before) = product_owners (retained_authority (retained_source R))"
    by (simp add: owner_of_product_def recovery_projection_supplies_the_exact_source reopen_retained_source_def)
  show ?thesis using produced
    by (cases action)
      (simp_all add: schedule_at_retained_state_def schedule_service_step_def Let_def
        captured_owner_map_is_the_live_owner_map maintenance_non_submit_replacement_uses_its_exact_source_step
        every_lock_product_step_keeps_the_product_owner_map before_owner
        del: lock_product_step.simps)
qed

lemma nonsettlement_maintenance_is_an_exact_captured_source_replacement:
  assumes produced: "result = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection (Service_Maintenance action) R"
    and nonsettlement: "\<not> is_settlement_action action"
  shows "\<exists>source. fst result = R\<lparr>retained_source := source\<rparr>"
proof -
  let ?before = "reopen_retained_product connection R"
  have round_trip: "capture_retained_product ?before = R" by (rule product_round_trip_preserves_the_durable_projection)
  have same_image: "\<exists>source. R = R\<lparr>retained_source := source\<rparr>"
    by (rule exI[of _ "retained_source R"]) simp
  show ?thesis
  proof (cases action)
    case (Exact_Install actor epoch changes sessions)
    let ?source = "capture_retained_source (lock_product_step permitted (\<lambda>_ _ _ _. True) maintainers registered
      (Lock_Install actor epoch changes sessions) (identity_source ?before))"
    have image: "fst result = R\<lparr>retained_source := ?source\<rparr>"
      using produced Exact_Install round_trip
      by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def
        maintenance_non_submit_is_an_exact_source_replacement capturing_an_exact_source_replacement_changes_only_retained_source)
    show ?thesis by (rule exI[of _ ?source], rule image)
  next
    case (Exact_Link link)
    let ?source = "capture_retained_source (lock_product_step permitted (\<lambda>_ _ _ _. True) maintainers registered
      (Lock_Driver_Connection link) (identity_source ?before))"
    have image: "fst result = R\<lparr>retained_source := ?source\<rparr>"
      using produced Exact_Link round_trip
      by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def
        maintenance_non_submit_is_an_exact_source_replacement capturing_an_exact_source_replacement_changes_only_retained_source)
    show ?thesis by (rule exI[of _ ?source], rule image)
  qed (use produced nonsettlement same_image in
    \<open>simp_all add: schedule_at_retained_state_def schedule_service_step_def Let_def
      product_round_trip_preserves_the_durable_projection\<close>)
qed

lemma a_changed_nonsettlement_maintenance_changes_the_captured_source:
  assumes produced: "result = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection (Service_Maintenance action) R"
    and nonsettlement: "\<not> is_settlement_action action"
    and changed: "fst result \<noteq> R"
  shows "retained_source (fst result) \<noteq> retained_source R"
proof
  obtain source where image: "fst result = R\<lparr>retained_source := source\<rparr>"
    using nonsettlement_maintenance_is_an_exact_captured_source_replacement[OF produced nonsettlement] by blast
  have projection: "retained_source (fst result) = source" using arg_cong[OF image, of retained_source] by simp
  assume same: "retained_source (fst result) = retained_source R"
  have restored: "source = retained_source R" using projection same by simp
  have "fst result = R" using image restored by simp
  then show False using changed by simp
qed

lemma every_scheduled_maintenance_keeps_all_execute_reply_discriminants:
  assumes produced: "result = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection (Service_Maintenance action) R"
  shows "(retained_outcomes (fst result), retained_completed_ids (fst result),
      retained_legal_receipts (fst result), retained_spend_receipts (fst result)) =
    (retained_outcomes R, retained_completed_ids R, retained_legal_receipts R, retained_spend_receipts R)"
proof -
  let ?before = "reopen_retained_product connection R"
  let ?base = "capture_retained_product ?before"
  have outcome_view: "retained_outcomes ?base = retained_outcomes R"
    and completed_view: "retained_completed_ids ?base = retained_completed_ids R"
    and legal_view: "retained_legal_receipts ?base = retained_legal_receipts R"
    and spend_view: "retained_spend_receipts ?base = retained_spend_receipts R"
    by (simp_all add: capture_retained_product_def reopen_retained_product_def initial_product_reads_def Let_def)
  show ?thesis
  proof (cases "is_settlement_action action")
    case True
    then show ?thesis using produced
      by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def
        replacing_queue_keeps_the_retained_primary_fields outcome_view completed_view legal_view spend_view)
  next
    case False
    have reopened_base: "reopen_retained_product connection ?base = ?before"
      by (simp add: capture_retained_product_def reopen_retained_product_def initial_product_reads_def Let_def
        source_round_trip_retains_every_durable_field)
    have produced_base: "result = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
        legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
        connection (Service_Maintenance action) ?base"
      using produced reopened_base by (simp only: schedule_at_retained_state_def Let_def)
    obtain source where image: "fst result = ?base\<lparr>retained_source := source\<rparr>"
      using nonsettlement_maintenance_is_an_exact_captured_source_replacement[OF produced_base False] by blast
    show ?thesis using image outcome_view completed_view legal_view spend_view by simp
  qed
qed

lemma a_changed_handover_cannot_share_any_maintenance_image:
  assumes handover: "result_a = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_a (Service_Handover owner_token successor_token maintainer proposal) R"
    and changed: "fst result_a \<noteq> R"
    and maintained: "result_b = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_b (Service_Maintenance action) R"
  shows "fst result_a \<noteq> fst result_b"
proof
  assume same: "fst result_a = fst result_b"
  have owner_changed: "product_owners (retained_authority (retained_source (fst result_a))) \<noteq>
      product_owners (retained_authority (retained_source R))"
    by (rule a_changed_scheduled_handover_changes_the_captured_owner_map[OF handover changed])
  have owner_frame: "product_owners (retained_authority (retained_source (fst result_b))) =
      product_owners (retained_authority (retained_source R))"
    by (rule every_scheduled_maintenance_keeps_the_captured_owner_map[OF maintained])
  show False using owner_changed owner_frame same by simp
qed

end

text \<open>The source replacement includes the retained call history. Exact_Link can change
  that history with unchanged epoch. No capture erasure or epoch-only change claim is made.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms capturing_an_exact_source_replacement_changes_only_retained_source
      source_attestation.every_lock_product_step_keeps_the_product_owner_map
      source_attestation.maintenance_non_submit_is_an_exact_source_replacement
      source_attestation.maintenance_non_submit_replacement_uses_its_exact_source_step
      source_attestation.every_scheduled_maintenance_keeps_the_captured_owner_map
      source_attestation.nonsettlement_maintenance_is_an_exact_captured_source_replacement
      source_attestation.a_changed_nonsettlement_maintenance_changes_the_captured_source
      source_attestation.every_scheduled_maintenance_keeps_all_execute_reply_discriminants
      source_attestation.a_changed_handover_cannot_share_any_maintenance_image})
  then () else error "Unexpected oracle in corrected actual maintenance source projections"
\<close>

end
