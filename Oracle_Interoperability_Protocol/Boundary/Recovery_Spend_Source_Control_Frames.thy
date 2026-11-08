theory Recovery_Spend_Source_Control_Frames
  imports Recovery_Checked_Source_Control_Frames
begin

lemma spend_receipt_replacement_keeps_the_exact_outcomes:
  "current_product_outcomes (s\<lparr>spend_receipts := receipts\<rparr>) = current_product_outcomes s"
  by (simp add: current_product_outcomes_def)

context source_attestation
begin

lemma spend_effect_keeps_source_controls:
  assumes produced: "after = fst (run_spend_effect spend_grant spend_verified permitted verified maintainers registered verified_ack
    entry actor expected call_id payload authorization s)"
  shows "product_owners (product_durable (outcome_source (current_product_outcomes after))) =
      product_owners (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_authority_epoch (product_durable (outcome_source (current_product_outcomes after))) =
      product_authority_epoch (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_sessions (product_durable (outcome_source (current_product_outcomes after))) =
      product_sessions (product_durable (outcome_source (current_product_outcomes s)))"
    and "call_local_status (product_calls (outcome_source (current_product_outcomes after))) =
      call_local_status (product_calls (outcome_source (current_product_outcomes s)))"
  using produced
  by (simp_all add: run_spend_effect_def Let_def checked_current_outcome_source_is_the_observed_source
    checked_read_replacement_supplies_its_exact_source checked_product_read_selector_is_the_read_world
    checked_execution_keeps_owner_epoch_sessions_and_local_status[OF refl] split: if_splits)

lemma spend_submission_keeps_source_controls:
  assumes produced: "after = fst (submit_governed_spend spend_grant spend_verified permitted verified maintainers registered verified_ack
    entry actor expected call_id payload authorization s)"
  shows "product_owners (product_durable (outcome_source (current_product_outcomes after))) =
      product_owners (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_authority_epoch (product_durable (outcome_source (current_product_outcomes after))) =
      product_authority_epoch (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_sessions (product_durable (outcome_source (current_product_outcomes after))) =
      product_sessions (product_durable (outcome_source (current_product_outcomes s)))"
    and "call_local_status (product_calls (outcome_source (current_product_outcomes after))) =
      call_local_status (product_calls (outcome_source (current_product_outcomes s)))"
  using produced
  by (simp_all add: submit_governed_spend_def Let_def spend_receipt_replacement_keeps_the_exact_outcomes
    spend_effect_keeps_source_controls[OF refl] split: option.splits if_splits)

lemma spend_full_execute_keeps_source_controls:
  assumes produced: "result = durable_execute directory policy authenticate verify endorse route token proof target
    (Apply_Governed_Spend entry actor expected call_id payload spend_authorization) authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s"
  shows "product_owners (product_durable (outcome_source (current_product_outcomes (fst result)))) =
      product_owners (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_authority_epoch (product_durable (outcome_source (current_product_outcomes (fst result)))) =
      product_authority_epoch (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_sessions (product_durable (outcome_source (current_product_outcomes (fst result)))) =
      product_sessions (product_durable (outcome_source (current_product_outcomes s)))"
    and "call_local_status (product_calls (outcome_source (current_product_outcomes (fst result)))) =
      call_local_status (product_calls (outcome_source (current_product_outcomes s)))"
  using produced
  by (simp_all add: durable_execute_def Let_def spend_submission_keeps_source_controls[OF refl] split: if_splits)

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms spend_receipt_replacement_keeps_the_exact_outcomes
      source_attestation.spend_effect_keeps_source_controls
      source_attestation.spend_submission_keeps_source_controls
      source_attestation.spend_full_execute_keeps_source_controls})
  then () else error "Unexpected oracle in spend actual Execute control frames"
\<close>

end
