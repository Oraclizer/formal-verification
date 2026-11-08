theory Reference_Regulatory_Consumption
  imports Reference_Authority_Trace
begin

fun reference_regulatory_write where
  "reference_regulatory_write (Apply_Governed_Order stage entry who expected call_id order payload) = True"
| "reference_regulatory_write (Apply_Governed_Spend entry who expected call_id payload authorization) = True"
| "reference_regulatory_write action = False"

context source_attestation
begin

lemma a_fresh_regulatory_service_uses_the_actual_governed_product_step:
  assumes step: "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
    authenticated connection (Service_Execute route token proof target action authorization) supplied before = (after, Some reply)"
    and regulated: "reference_regulatory_write action"
    and admitted: "authorized_endpoint_action directory policy authenticate verify route token proof target action
      (reopen_retained_product connection (reference_product before))"
    and live: "call_local_status (product_calls
      (identity_source (reopen_retained_product connection (reference_product before)))) = Endpoint_Up"
    and claimed: "external_call_claim action = Some (operation, actor, call_id, payload)"
    and fresh: "\<not> authority_has_call_id call_id (reopen_retained_product connection (reference_product before))"
    and endorsed: "recovery_requirements directory policy authenticate endorse target action authorization
      (identity_source (reopen_retained_product connection (reference_product before)))"
  shows "reference_product after = capture_retained_product
    (regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted
      (reference_permitted_at (reference_inputs before)) verified maintainers registered verified_ack
      (canonical_consumer_action action) (reopen_retained_product connection (reference_product before)))"
proof -
  note selected = a_reference_step_uses_the_actual_service_with_the_retained_grants[OF step]
  show ?thesis using selected regulated admitted live claimed fresh endorsed
    by (cases action) (auto simp: schedule_at_retained_state_def schedule_service_step_def
        durable_execute_def Let_def split: if_splits)
qed

theorem a_blocked_reference_legal_order_preserves_the_source_and_financial_view:
  assumes step: "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
    authenticated connection
      (Service_Execute route token proof target (Apply_Governed_Order stage entry actor expected call_id order payload) authorization)
      supplied before = (after, Some reply)"
    and admitted: "authorized_endpoint_action directory policy authenticate verify route token proof target
      (Apply_Governed_Order stage entry actor expected call_id order payload)
      (reopen_retained_product connection (reference_product before))"
    and live: "call_local_status (product_calls
      (identity_source (reopen_retained_product connection (reference_product before)))) = Endpoint_Up"
    and fresh: "\<not> authority_has_call_id call_id (reopen_retained_product connection (reference_product before))"
    and endorsed: "recovery_requirements directory policy authenticate endorse target
      (Apply_Governed_Order stage entry actor expected call_id order payload) authorization
      (identity_source (reopen_retained_product connection (reference_product before)))"
    and blocked: "snd (submit_governed_order legal_grant order_verified (reference_permitted_at (reference_inputs before))
      verified maintainers registered verified_ack stage Regulatory_Normal actor expected call_id order payload
        (regulated_orders (reopen_retained_product connection (reference_product before)))) = Legal_Blocked reason"
  shows "retained_source (reference_product after) = retained_source (reference_product before)"
    "retained_debits (reference_product after) = retained_debits (reference_product before)"
    "retained_decisions (reference_product after) = retained_decisions (reference_product before)"
proof -
  let ?live = "reopen_retained_product connection (reference_product before)"
  let ?next = "regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted
     (reference_permitted_at (reference_inputs before)) verified maintainers registered verified_ack
     (Apply_Governed_Order stage Regulatory_Normal actor expected call_id order payload) ?live"
  have action: "reference_regulatory_write (Apply_Governed_Order stage entry actor expected call_id order payload)"
    by simp
  have claim: "\<exists>operation. external_call_claim (Apply_Governed_Order stage entry actor expected call_id order payload) =
      Some (operation, actor, call_id, payload)"
    by (cases stage) auto
  obtain operation where selected: "external_call_claim (Apply_Governed_Order stage entry actor expected call_id order payload) =
      Some (operation, actor, call_id, payload)" using claim by blast
  have actual: "reference_product after = capture_retained_product ?next"
    using a_fresh_regulatory_service_uses_the_actual_governed_product_step[OF step action admitted live selected fresh endorsed]
    by simp
  have same: "regulated_read_world ?next = regulated_read_world ?live"
    by (rule legally_refused_stage_keeps_primary_and_financial_view[OF blocked])
  have source: "identity_source ?next = identity_source ?live"
    using same by (simp add: identity_source_def)
  have original: "capture_retained_product ?live = reference_product before"
    by (rule product_round_trip_preserves_the_durable_projection)
  have source_result: "retained_source (reference_product after) = retained_source (capture_retained_product ?live)"
    using source by (simp add: actual retained_call_source_is_the_actual_product_source)
  have financial_result:
    "retained_debits (reference_product after) = retained_debits (capture_retained_product ?live)"
    "retained_decisions (reference_product after) = retained_decisions (capture_retained_product ?live)"
    using same by (simp_all add: actual capture_retained_product_def regulated_read_world_def Let_def)
  show "retained_source (reference_product after) = retained_source (reference_product before)"
    using source_result original by simp
  show "retained_debits (reference_product after) = retained_debits (reference_product before)"
    "retained_decisions (reference_product after) = retained_decisions (reference_product before)"
    using financial_result original by simp_all
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.a_fresh_regulatory_service_uses_the_actual_governed_product_step
      source_attestation.a_blocked_reference_legal_order_preserves_the_source_and_financial_view})
  then () else error "Unexpected oracle in actual reference legal consumption"
\<close>

end
