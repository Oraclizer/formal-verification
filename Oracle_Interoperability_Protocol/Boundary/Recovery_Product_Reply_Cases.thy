theory Recovery_Product_Reply_Cases
  imports "Recovery_Boundary_Invariant"
begin

text \<open>These source-bound lemmas eliminate nonchanging service constructors. The cross-action
  replies_follow_effects property for the remaining cases is proved by the separate product-reply development.\<close>

context source_attestation
begin

lemma product_receipt_queries_do_not_change_the_retained_image:
  "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection (Service_Receipt route token proof target action) R) = R"
  by (simp add: schedule_at_retained_state_def schedule_service_step_def
    product_round_trip_preserves_the_durable_projection Let_def)

lemma product_reads_do_not_change_the_retained_image:
  "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection (Service_Read token proof target query supplied) R) = R"
  by (simp add: schedule_at_retained_state_def schedule_service_step_def
    product_round_trip_preserves_the_durable_projection Let_def)

lemma product_cache_capture_does_not_change_the_retained_image:
  "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection (Service_Capture token proof target query) R) = R"
  by (simp add: schedule_at_retained_state_def schedule_service_step_def
    product_round_trip_preserves_the_durable_projection Let_def)

lemma product_source_probe_does_not_change_the_retained_image:
  "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection (Service_Source_Probe origin evidence) R) = R"
  by (simp add: schedule_at_retained_state_def schedule_service_step_def
    product_round_trip_preserves_the_durable_projection Let_def)

end

text \<open>The remaining constructors are Service_Execute, Service_Handover and Service_Maintenance.
  Their pairwise equal-effect cases, including different constructors and authority connections,
  remain an explicit obligation. No assertion of the full product reply property is made.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.product_receipt_queries_do_not_change_the_retained_image
      source_attestation.product_reads_do_not_change_the_retained_image
      source_attestation.product_cache_capture_does_not_change_the_retained_image
      source_attestation.product_source_probe_does_not_change_the_retained_image})
  then () else error "Unexpected oracle in product reply case elimination"
\<close>

end
