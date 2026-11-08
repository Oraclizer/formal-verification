theory Recovery_Maintenance_Link_Canary
  imports "OIP_Product.Parallel_Service"
begin

context source_attestation
begin

lemma a_driver_link_is_retained_as_a_source_history_event:
  "retained_call_history (capture_retained_source (product_apply_public [Set_Authority_Connection link] source)) =
    retained_call_history (capture_retained_source source) @ [Authority_Link_Changed link]"
  by (simp add: capture_retained_source_def product_apply_public_def Let_def)

lemma a_scheduled_driver_link_appends_its_retained_history:
  "retained_call_history (retained_source (fst
    (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection (Service_Maintenance (Exact_Link link)) R))) =
    retained_call_history (retained_source R) @ [Authority_Link_Changed link]"
  by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def
    capture_retained_product_def capture_retained_source_def reopen_retained_product_def reopen_retained_source_def
    initial_product_reads_def apply_non_submit_lock_action_def update_settlement_outcomes_def
    replace_regulated_reads_def regulated_read_world_def product_apply_public_def)

lemma a_scheduled_driver_link_keeps_the_product_epoch:
  "product_authority_epoch (retained_authority (retained_source (fst
    (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection (Service_Maintenance (Exact_Link link)) R)))) =
    product_authority_epoch (retained_authority (retained_source R))"
  by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def
    capture_retained_product_def capture_retained_source_def reopen_retained_product_def reopen_retained_source_def
    initial_product_reads_def apply_non_submit_lock_action_def update_settlement_outcomes_def
    replace_regulated_reads_def regulated_read_world_def product_apply_public_def)

lemma a_scheduled_driver_link_changes_the_retained_image:
  "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection (Service_Maintenance (Exact_Link link)) R) \<noteq> R"
proof
  let ?after = "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection (Service_Maintenance (Exact_Link link)) R)"
  assume same: "?after = R"
  have history_same: "retained_call_history (retained_source ?after) = retained_call_history (retained_source R)"
    using arg_cong[OF same, of "\<lambda>retained. retained_call_history (retained_source retained)"] .
  have appended: "retained_call_history (retained_source ?after) =
      retained_call_history (retained_source R) @ [Authority_Link_Changed link]"
    by (rule a_scheduled_driver_link_appends_its_retained_history)
  have lengths: "length (retained_call_history (retained_source R)) + 1 =
      length (retained_call_history (retained_source R))"
    using arg_cong[OF history_same, of length] appended by simp
  then show False by arith
qed

lemma the_link_control_is_nonsettlement:
  "\<not> is_settlement_action (Exact_Link link)"
  by simp

end

text \<open>A single internal driver action changes retained history while keeping the epoch.
  This refutes the proposed epoch-only maintenance discriminator and capture-erasure helper,
  not the original global product RFE. The frozen call history remains observable and retained.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.a_driver_link_is_retained_as_a_source_history_event
      source_attestation.a_scheduled_driver_link_appends_its_retained_history
      source_attestation.a_scheduled_driver_link_keeps_the_product_epoch
      source_attestation.a_scheduled_driver_link_changes_the_retained_image
      source_attestation.the_link_control_is_nonsettlement})
  then () else error "Unexpected oracle in actual driver-link history counterexample"
\<close>

end
