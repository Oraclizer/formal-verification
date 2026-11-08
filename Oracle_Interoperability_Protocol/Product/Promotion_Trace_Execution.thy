theory Promotion_Trace_Execution
  imports Promotion_Trace_Legal Durable_Execution
begin

definition actual_product_calls where
  "actual_product_calls s = product_calls (identity_source s)"

lemma outcome_source_is_the_endpoint_source:
  "outcome_source (current_product_outcomes s) = identity_source s"
  by (simp add: identity_source_def current_product_outcomes_def legal_underlying_outcomes_def
      regulated_read_world_def observed_product_source_def)

lemma exact_read_calls_are_the_product_calls:
  "exact_calls (read_authority (regulated_read_world s)) = actual_product_calls s"
  by (simp add: actual_product_calls_def identity_source_def exact_calls_def outcome_calls_def observed_product_source_def)

context source_attestation
begin

lemma regulated_entry_uses_a_public_segment:
  "source_segment (actual_product_calls s)
    (actual_product_calls (regulated_product_step legal_grant order_verified spend_grant spend_verified
      read_permitted permitted verified maintainers registered verified_ack action s))"
proof -
  have segment: "read_source_segment (regulated_read_world s) (regulated_read_world
    (regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers
      registered verified_ack action s))"
    by (rule regulated_step_has_an_actual_source_segment)
  show ?thesis using segment
    by (simp add: read_source_segment_def exact_read_calls_are_the_product_calls)
qed

lemma finishing_is_a_source_stutter:
  "actual_product_calls (fst (finish_durable_execution verified actor action s)) = actual_product_calls s"
  using finishing_does_not_reapply_authority_effects[of verified actor action s]
  by (simp add: actual_product_calls_def outcome_source_is_the_endpoint_source)

lemma checked_refusal_is_a_source_stutter:
  "actual_product_calls (record_checked_refusal call_id payload refusal s) = actual_product_calls s"
  using checked_refusal_keeps_the_exact_underlying_source[of call_id payload refusal s]
  by (simp add: actual_product_calls_def outcome_source_is_the_endpoint_source)

lemma released_credit_replacement_is_source_stutter:
  assumes "snd (record_released_credit_receipt permitted verified registered Normal_Lock_Entry actor call_id payload
    (settlement_primary (read_authority (regulated_read_world s)))) \<noteq> None"
  shows "actual_product_calls (replace_product_outcomes (origin_outcomes
    (fst (record_released_credit_receipt permitted verified registered Normal_Lock_Entry actor call_id payload
      (settlement_primary (read_authority (regulated_read_world s)))))) s) = actual_product_calls s"
proof -
  let ?origins = "settlement_primary (read_authority (regulated_read_world s))"
  let ?result = "record_released_credit_receipt permitted verified registered Normal_Lock_Entry actor call_id payload ?origins"
  have source: "identity_source (replace_product_outcomes (origin_outcomes (fst ?result)) s) = identity_source s"
    using released_credit_result_keeps_the_underlying_source[OF assms]
    by (simp only: outcome_source_is_the_endpoint_source)
  show ?thesis by (simp only: actual_product_calls_def source)
qed

lemma fresh_service_execution_has_a_public_segment:
  "source_segment (actual_product_calls s)
    (actual_product_calls (run_fresh_durable_effect permitted verified maintainers registered verified_ack legal_grant order_verified
       spend_grant spend_verified read_permitted action s))"
  by (induction permitted verified maintainers registered verified_ack legal_grant order_verified
      spend_grant spend_verified read_permitted action s rule: run_fresh_durable_effect.induct)
    (simp_all del: regulated_product_step.simps add: Let_def checked_refusal_is_a_source_stutter
      regulated_entry_uses_a_public_segment released_credit_replacement_is_source_stutter split: if_splits)

lemma durable_endpoint_execution_has_a_public_segment:
  "source_segment (actual_product_calls s)
    (actual_product_calls (fst (durable_execute directory policy authenticate verify endorse route token proof target action authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s)))"
proof (cases "external_call_claim action")
  case None
  then show ?thesis by (simp add: durable_execute_def)
next
  case (Some claimed)
  obtain operation actor call_id payload where tuple: "claimed = (operation, actor, call_id, payload)"
    by (cases claimed) auto
  from Some tuple show ?thesis
    by (cases "execution_receipt_request action")
      (simp_all add: durable_execute_def Let_def finishing_is_a_source_stutter
        fresh_service_execution_has_a_public_segment split: if_splits)
qed

end

end
