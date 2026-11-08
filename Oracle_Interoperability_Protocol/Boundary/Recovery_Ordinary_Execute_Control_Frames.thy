theory Recovery_Ordinary_Execute_Control_Frames
  imports Recovery_Ordinary_Source_Control_Frames
begin

lemma ordinary_origin_view_is_the_current_outcomes:
  "origin_outcomes (settlement_primary (read_authority (regulated_read_world s))) = current_product_outcomes s"
  by (simp add: current_product_outcomes_def legal_underlying_outcomes_def regulated_read_world_def)

lemma ordinary_credit_rerecording_keeps_the_exact_source:
  "outcome_source (origin_outcomes
      (fst (record_released_credit_receipt permitted verified registered entry actor call_id payload origins))) =
    outcome_source (origin_outcomes origins)"
  by (simp add: record_released_credit_receipt_def store_product_result_def Let_def split: option.splits prod.splits)

context source_attestation
begin

lemma ordinary_checked_consumer_keeps_source_controls:
  assumes produced: "after = regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted
    permitted verified maintainers registered verified_ack
    (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s"
  shows "product_owners (product_durable (outcome_source (current_product_outcomes after))) =
      product_owners (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_authority_epoch (product_durable (outcome_source (current_product_outcomes after))) =
      product_authority_epoch (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_sessions (product_durable (outcome_source (current_product_outcomes after))) =
      product_sessions (product_durable (outcome_source (current_product_outcomes s)))"
    and "call_local_status (product_calls (outcome_source (current_product_outcomes after))) =
      call_local_status (product_calls (outcome_source (current_product_outcomes s)))"
  using produced
  by (simp_all add: execute_at_checked_cut_def Let_def current_product_outcomes_def legal_underlying_outcomes_def
    regulated_read_world_def replace_regulated_reads_def
    ordinary_origin_submit_keeps_owner_epoch_sessions_and_local_status split: if_splits)

lemma ordinary_fresh_execute_keeps_source_controls:
  assumes produced: "after = run_fresh_durable_effect permitted verified maintainers registered verified_ack
    legal_grant order_verified spend_grant spend_verified read_permitted
    (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s"
  shows "product_owners (product_durable (outcome_source (current_product_outcomes after))) =
      product_owners (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_authority_epoch (product_durable (outcome_source (current_product_outcomes after))) =
      product_authority_epoch (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_sessions (product_durable (outcome_source (current_product_outcomes after))) =
      product_sessions (product_durable (outcome_source (current_product_outcomes s)))"
    and "call_local_status (product_calls (outcome_source (current_product_outcomes after))) =
      call_local_status (product_calls (outcome_source (current_product_outcomes s)))"
  by (simp_all only: produced run_fresh_durable_effect.simps canonical_consumer_action.simps Let_def
    replacement_supplies_exact_outcome_table checked_refusal_keeps_the_exact_underlying_source
    ordinary_credit_rerecording_keeps_the_exact_source ordinary_origin_view_is_the_current_outcomes
    ordinary_checked_consumer_keeps_source_controls[OF refl]
    if_True if_False simp_thms split: if_splits)

lemma ordinary_full_execute_keeps_source_controls:
  assumes produced: "result = durable_execute directory policy authenticate verify endorse route token proof target
    (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s"
  shows "product_owners (product_durable (outcome_source (current_product_outcomes (fst result)))) =
      product_owners (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_authority_epoch (product_durable (outcome_source (current_product_outcomes (fst result)))) =
      product_authority_epoch (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_sessions (product_durable (outcome_source (current_product_outcomes (fst result)))) =
      product_sessions (product_durable (outcome_source (current_product_outcomes s)))"
    and "call_local_status (product_calls (outcome_source (current_product_outcomes (fst result)))) =
      call_local_status (product_calls (outcome_source (current_product_outcomes s)))"
  by (simp_all only: produced durable_execute_def external_call_claim.simps execution_receipt_request.simps
    case_prod_conv option.simps Let_def fst_conv finishing_does_not_reapply_authority_effects
    ordinary_fresh_execute_keeps_source_controls[OF refl]
    if_True if_False simp_thms split: if_splits)

end

text \<open>The produced equations name exact frozen function results and are discharged by
  reflexivity at call sites. No owner, epoch, session or runtime frame is assumed as an environment
  contract. The full Execute result may still have changed authority logs, requests and outcomes.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ordinary_origin_view_is_the_current_outcomes
      ordinary_credit_rerecording_keeps_the_exact_source
      source_attestation.ordinary_checked_consumer_keeps_source_controls
      source_attestation.ordinary_fresh_execute_keeps_source_controls
      source_attestation.ordinary_full_execute_keeps_source_controls})
  then () else error "Unexpected oracle in ordinary actual Execute control frames"
\<close>

end
