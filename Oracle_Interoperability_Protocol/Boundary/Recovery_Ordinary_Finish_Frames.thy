theory Recovery_Ordinary_Finish_Frames
  imports Recovery_Ordinary_Fresh_Rows
begin

context source_attestation
begin

lemma ordinary_finishing_keeps_the_entire_outcome_map:
  "outcome_entries (current_product_outcomes (fst (finish_durable_execution verified actor
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect claimed_actor call_id payload))) s))) =
    outcome_entries (current_product_outcomes s)"
  by (simp add: Let_def ordinary_completion_keeps_the_entire_outcome_map split: if_splits)

lemma ordinary_finishing_keeps_the_source_local_status:
  "call_local_status (product_calls (outcome_source (current_product_outcomes
      (fst (finish_durable_execution verified actor action s))))) =
    call_local_status (product_calls (outcome_source (current_product_outcomes s)))"
  using arg_cong[OF finishing_does_not_reapply_authority_effects[of verified actor action s],
    of "\<lambda>source. call_local_status (product_calls source)"] .

lemma ordinary_prior_durable_execute_keeps_the_entire_outcome_map:
  assumes prior: "authority_has_call_id call_id s"
  shows "outcome_entries (current_product_outcomes (fst (durable_execute directory policy authenticate verify endorse route token proof target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s))) =
    outcome_entries (current_product_outcomes s)"
  by (simp add: durable_execute_def Let_def prior ordinary_finishing_keeps_the_entire_outcome_map
    ordinary_completion_keeps_the_entire_outcome_map split: if_splits)

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.ordinary_finishing_keeps_the_entire_outcome_map
      source_attestation.ordinary_finishing_keeps_the_source_local_status
      source_attestation.ordinary_prior_durable_execute_keeps_the_entire_outcome_map})
  then () else error "Unexpected oracle in ordinary finishing map and status frames"
\<close>

end
