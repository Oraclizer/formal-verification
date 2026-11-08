theory Recovery_Execute_Change_Discriminants
  imports Recovery_Ordinary_Durable_Shape Recovery_Ordinary_Projection "Recovery_Execute_Receipt_Frames"
begin

context source_attestation
begin

lemma a_changed_ordinary_execute_changes_its_outcomes_or_completed_set:
  assumes produced: "result = durable_execute directory policy authenticate verify endorse route token proof target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s"
    and changed: "capture_retained_product (fst result) \<noteq> capture_retained_product s"
  shows "outcome_entries (current_product_outcomes (fst result)) \<noteq> outcome_entries (current_product_outcomes s) \<or>
    outcome_completed (current_product_outcomes (fst result)) \<noteq> outcome_completed (current_product_outcomes s)"
proof (cases "authority_has_call_id call_id s")
  case prior: True
  have finish: "result = finish_durable_execution verified actor
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect actor call_id payload))) s"
    by (rule ordinary_a_changed_prior_execute_is_its_exact_finish[OF produced changed prior])
  obtain outcome where fresh_completed: "call_id \<notin> outcome_completed (current_product_outcomes s)"
    and shape: "result = (replace_product_outcomes ((current_product_outcomes s)
      \<lparr>outcome_completed := insert call_id (outcome_completed (current_product_outcomes s))\<rparr>) s,
      Durable_Execution_Reply (Observed_Ordinary_Result (Collected outcome)))"
    using a_changed_ordinary_completion_has_a_fresh_completed_key_and_the_stored_reply[OF finish changed] by blast
  show ?thesis using fresh_completed shape by auto
next
  case fresh: False
  have rows: "\<exists>reply. outcome_entries (current_product_outcomes (fst result)) =
      (outcome_entries (current_product_outcomes s))
        (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>)"
    by (rule ordinary_a_changed_fresh_execute_finishes_and_inserts_the_exact_request_row(3)[OF produced changed fresh])
  obtain reply where inserted: "outcome_entries (current_product_outcomes (fst result)) =
      (outcome_entries (current_product_outcomes s))
        (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>)" using rows by blast
  have absent: "outcome_entries (current_product_outcomes s) call_id = None"
    using fresh by (simp add: authority_has_call_id_def)
  have different: "outcome_entries (current_product_outcomes (fst result)) \<noteq> outcome_entries (current_product_outcomes s)"
    by (rule ordinary_a_fresh_result_changes_the_outcome_map[OF absent inserted])
  show ?thesis by (rule disjI1[OF different])
qed

lemma every_changed_durable_execute_changes_a_reply_discriminant:
  assumes changed: "capture_retained_product (fst (durable_execute directory policy authenticate verify endorse route token proof target action authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s)) \<noteq>
    capture_retained_product s"
  shows "(retained_outcomes (capture_retained_product (fst (durable_execute directory policy authenticate verify endorse route token proof target action authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s))),
    retained_completed_ids (capture_retained_product (fst (durable_execute directory policy authenticate verify endorse route token proof target action authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s))),
    retained_legal_receipts (capture_retained_product (fst (durable_execute directory policy authenticate verify endorse route token proof target action authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s))),
    retained_spend_receipts (capture_retained_product (fst (durable_execute directory policy authenticate verify endorse route token proof target action authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s)))) \<noteq>
    (retained_outcomes (capture_retained_product s), retained_completed_ids (capture_retained_product s),
      retained_legal_receipts (capture_retained_product s), retained_spend_receipts (capture_retained_product s))"
proof (cases action)
  case (Apply_Governed_Order stage entry actor expected call_id order payload)
  have different: "legal_receipts (regulated_orders (fst (durable_execute directory policy authenticate verify endorse route token proof target
      (Apply_Governed_Order stage entry actor expected call_id order payload) authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s))) \<noteq>
    legal_receipts (regulated_orders s)"
    by (rule a_changed_durable_legal_execute_changes_the_legal_receipt_map[OF changed[unfolded Apply_Governed_Order]])
  show ?thesis using different Apply_Governed_Order
    by (auto simp: capture_retains_the_exact_legal_receipt_map)
next
  case (Apply_Governed_Spend entry actor expected call_id payload spend_authorization)
  have different: "spend_receipts (fst (durable_execute directory policy authenticate verify endorse route token proof target
      (Apply_Governed_Spend entry actor expected call_id payload spend_authorization) authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s)) \<noteq> spend_receipts s"
    by (rule a_changed_durable_spend_execute_changes_the_spend_receipt_map[OF changed[unfolded Apply_Governed_Spend]])
  show ?thesis using different Apply_Governed_Spend
    by (auto simp: capture_retains_the_exact_spend_receipt_map)
next
  case Collect_Governed_Order
  then show ?thesis using changed by (simp add: durable_execute_def)
next
  case Collect_Governed_Spend
  then show ?thesis using changed by (simp add: durable_execute_def)
next
  case (Ordinary_Product_Action read_action)
  show ?thesis
  proof (cases read_action)
    case Capture_Read
    then show ?thesis using Ordinary_Product_Action changed by (simp add: durable_execute_def)
  next
    case (Execute_Checked entry actor expected call_id payload)
    have changed_ordinary: "capture_retained_product (fst (durable_execute directory policy authenticate verify endorse route token proof target
        (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) authorization
        legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s)) \<noteq>
      capture_retained_product s" using changed Ordinary_Product_Action Execute_Checked by simp
    have different: "outcome_entries (current_product_outcomes (fst (durable_execute directory policy authenticate verify endorse route token proof target
        (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) authorization
        legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s))) \<noteq>
      outcome_entries (current_product_outcomes s) \<or>
      outcome_completed (current_product_outcomes (fst (durable_execute directory policy authenticate verify endorse route token proof target
        (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) authorization
        legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s))) \<noteq>
      outcome_completed (current_product_outcomes s)"
      by (rule a_changed_ordinary_execute_changes_its_outcomes_or_completed_set[OF refl changed_ordinary])
    show ?thesis using different Ordinary_Product_Action Execute_Checked
      by (auto simp: ordinary_capture_keeps_the_outcome_map capture_retains_the_exact_completed_set)
  next
    case Read_Authority_Action
    then show ?thesis using Ordinary_Product_Action changed
      by (simp add: durable_execute_def split: option.splits prod.splits)
  qed
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.a_changed_ordinary_execute_changes_its_outcomes_or_completed_set
      source_attestation.every_changed_durable_execute_changes_a_reply_discriminant})
  then () else error "Unexpected oracle in actual Execute change discriminants"
\<close>

end
