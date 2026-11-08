theory Durable_Execution
  imports Released_Credit_Receipt
begin

definition retained_receipt_permission where
  "retained_receipt_permission policy authenticate token proof target payload \<longleftrightarrow>
    (\<exists>identity. authenticate token = Some identity \<and>
       policy identity target (envelope_asset (payload_envelope payload)) Read_Receipt (proof_epoch proof))"

context source_attestation
begin

fun run_fresh_durable_effect where
  "run_fresh_durable_effect permitted verified maintainers registered verified_ack legal_grant order_verified
    spend_grant spend_verified read_permitted (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s =
    (let source = identity_source s; actual = current_product_cut source; envelope = payload_envelope payload in
      if governed_command (envelope_command envelope) \<or> expected \<noteq> envelope_cut envelope then s
      else if call_connection (product_calls source) \<noteq> Authority_Connected
        then record_checked_refusal call_id payload Authority_Unavailable s
      else if expected \<noteq> actual then record_checked_refusal call_id payload Authority_Busy s
      else let origins = settlement_primary (read_authority (regulated_read_world s));
               recorded = record_released_credit_receipt permitted verified registered Normal_Lock_Entry actor call_id payload origins
           in if authority_has_call_id call_id s \<or> snd recorded = None
              then regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified
                maintainers registered verified_ack (canonical_consumer_action
                  (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload))) s
              else replace_product_outcomes (origin_outcomes (fst recorded)) s)"
| "run_fresh_durable_effect permitted verified maintainers registered verified_ack legal_grant order_verified
    spend_grant spend_verified read_permitted action s =
    regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified
       maintainers registered verified_ack (canonical_consumer_action action) s"

definition durable_execute where
  "durable_execute directory policy authenticate verify endorse route token proof target action authorization
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s =
    (case (external_call_claim action, execution_receipt_request action) of
       (Some (operation, actor, call_id, payload), Some collect) \<Rightarrow>
       if \<not> authorized_endpoint_action directory policy authenticate verify route token proof target action s
       then (s, Durable_Execution_Reject)
       else if call_local_status (product_calls (identity_source s)) \<noteq> Endpoint_Up
       then (s, Durable_Execution_Wait)
       else if authority_has_call_id call_id s then
         if retained_receipt_permission policy authenticate token proof target payload
         then finish_durable_execution verified actor collect s else (s, Durable_Execution_Reject)
       else if \<not> recovery_requirements directory policy authenticate endorse target action authorization (identity_source s)
       then (s, Durable_Execution_Reject)
       else let executed = run_fresh_durable_effect permitted verified maintainers registered verified_ack
          legal_grant order_verified spend_grant spend_verified read_permitted action s
        in if authority_has_call_id call_id executed then finish_durable_execution verified actor collect executed
           else (executed, Durable_Execution_Reject)
     | _ \<Rightarrow> (s, Durable_Execution_Reject))"

theorem an_admitted_exact_retry_checks_the_retained_result_before_fresh_conditions:
  assumes "external_call_claim action = Some (operation, actor, call_id, payload)"
    "execution_receipt_request action = Some collect"
    "authorized_endpoint_action directory policy authenticate verify route token proof target action s"
    "call_local_status (product_calls (identity_source s)) = Endpoint_Up"
    "authority_has_call_id call_id s"
    "retained_receipt_permission policy authenticate token proof target payload"
  shows "durable_execute directory policy authenticate verify endorse route token proof target action authorization
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s =
     finish_durable_execution verified actor collect s"
  using assms by (simp add: durable_execute_def)

lemma prior_call_on_any_route_cannot_repeat_an_authority_effect:
  assumes "external_call_claim action = Some (operation, actor, call_id, payload)"
    "authority_has_call_id call_id s"
  shows "outcome_source (current_product_outcomes (fst (durable_execute directory policy authenticate verify endorse
     route token proof target action authorization legal_grant order_verified spend_grant spend_verified read_permitted permitted verified
     maintainers registered verified_ack s))) = outcome_source (current_product_outcomes s)"
  using assms by (cases "execution_receipt_request action")
    (simp_all add: durable_execute_def finishing_does_not_reapply_authority_effects split: if_splits)

lemma disconnected_admitted_call_retains_unavailable_without_source_effect:
  fixes s payload actor expected call_id entry
  assumes "expected = envelope_cut (payload_envelope payload)"
    "\<not> governed_command (envelope_command (payload_envelope payload))"
    "call_connection (product_calls (identity_source s)) \<noteq> Authority_Connected"
    "\<not> authority_has_call_id call_id s"
  shows "let after = run_fresh_durable_effect permitted verified maintainers registered verified_ack legal_grant order_verified
       spend_grant spend_verified read_permitted (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s in
    outcome_source (current_product_outcomes after) = outcome_source (current_product_outcomes s) \<and>
    outcome_entries (current_product_outcomes after) call_id =
      Some \<lparr>result_payload = payload, result_outcome = Authority_Unavailable\<rparr>"
  using assms by (simp add: Let_def checked_refusal_keeps_the_exact_underlying_source fresh_checked_refusal_records_the_exact_request)

end

end
