theory Recovery_Execute_Receipt_Frames
  imports Recovery_Execute_Spend_Shape
begin

context source_attestation
begin

lemma spend_effect_keeps_the_legal_receipt_map:
  "legal_receipts (regulated_orders (fst (run_spend_effect grant spend_verified permitted verified maintainers registered verified_ack
    entry who expected call_id payload authorization before))) = legal_receipts (regulated_orders before)"
  by (simp add: run_spend_effect_def replace_regulated_reads_def Let_def split: if_splits)

lemma spend_submission_keeps_the_legal_receipt_map:
  "legal_receipts (regulated_orders (fst (submit_governed_spend grant spend_verified permitted verified maintainers registered verified_ack
    entry who expected call_id payload authorization before))) = legal_receipts (regulated_orders before)"
  by (auto simp: submit_governed_spend_def Let_def spend_effect_keeps_the_legal_receipt_map
    split: option.splits if_splits)

lemma durable_legal_execute_keeps_the_spend_receipt_map:
  "spend_receipts (fst (durable_execute directory policy authenticate verify endorse route token proof target
    (Apply_Governed_Order stage entry who expected call_id order payload) authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before)) =
    spend_receipts before"
  by (cases stage) (auto simp: durable_execute_def Let_def split: if_splits)

lemma durable_spend_execute_keeps_the_legal_receipt_map:
  "legal_receipts (regulated_orders (fst (durable_execute directory policy authenticate verify endorse route token proof target
    (Apply_Governed_Spend entry who expected call_id payload spend_authorization) authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before))) =
    legal_receipts (regulated_orders before)"
  by (auto simp: durable_execute_def Let_def spend_submission_keeps_the_legal_receipt_map split: if_splits)

lemma a_changed_durable_legal_execute_changes_the_legal_receipt_map:
  assumes changed: "capture_retained_product (fst (durable_execute directory policy authenticate verify endorse
    route token proof target (Apply_Governed_Order stage entry who expected call_id order payload) authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before))
    \<noteq> capture_retained_product before"
  shows "legal_receipts (regulated_orders (fst (durable_execute directory policy authenticate verify endorse
    route token proof target (Apply_Governed_Order stage entry who expected call_id order payload) authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before)))
    \<noteq> legal_receipts (regulated_orders before)"
proof -
  let ?result = "durable_execute directory policy authenticate verify endorse route token proof target
    (Apply_Governed_Order stage entry who expected call_id order payload) authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before"
  let ?producer = "submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
    stage Regulatory_Normal who expected call_id order payload (regulated_orders before)"
  have shape: "?result = (before\<lparr>regulated_orders := fst ?producer\<rparr>,
      Durable_Execution_Reply (Observed_Legal_Result (snd ?producer)))"
    by (rule a_changed_durable_legal_execute_uses_the_new_receipt_reply[OF changed])
  have producer_changed: "fst ?producer \<noteq> regulated_orders before" using changed shape by auto
  note stored = a_changed_legal_submission_inserts_its_exact_returned_reply[OF refl producer_changed]
  have post: "legal_receipts (regulated_orders (fst ?result)) call_id \<noteq> legal_receipts (regulated_orders before) call_id"
    using shape stored by simp
  show ?thesis using post by auto
qed

lemma a_changed_durable_spend_execute_changes_the_spend_receipt_map:
  assumes changed: "capture_retained_product (fst (durable_execute directory policy authenticate verify endorse
    route token proof target (Apply_Governed_Spend entry who expected call_id payload spend_authorization) authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before))
    \<noteq> capture_retained_product before"
  shows "spend_receipts (fst (durable_execute directory policy authenticate verify endorse
    route token proof target (Apply_Governed_Spend entry who expected call_id payload spend_authorization) authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before))
    \<noteq> spend_receipts before"
proof -
  let ?result = "durable_execute directory policy authenticate verify endorse route token proof target
    (Apply_Governed_Spend entry who expected call_id payload spend_authorization) authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before"
  let ?producer = "submit_governed_spend spend_grant spend_verified permitted verified maintainers registered verified_ack
    Regulatory_Normal who expected call_id payload spend_authorization before"
  have shape: "?result = (fst ?producer, Durable_Execution_Reply (Observed_Spend_Result (snd ?producer)))"
    by (rule a_changed_durable_spend_execute_uses_the_new_receipt_reply[OF changed])
  have producer_changed: "fst ?producer \<noteq> before" using changed shape by auto
  note stored = a_changed_spend_submission_inserts_its_exact_returned_reply[OF refl producer_changed]
  have post: "spend_receipts (fst ?result) call_id \<noteq> spend_receipts before call_id"
    using shape stored by simp
  show ?thesis using post by auto
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.spend_effect_keeps_the_legal_receipt_map
      source_attestation.spend_submission_keeps_the_legal_receipt_map
      source_attestation.durable_legal_execute_keeps_the_spend_receipt_map
      source_attestation.durable_spend_execute_keeps_the_legal_receipt_map
      source_attestation.a_changed_durable_legal_execute_changes_the_legal_receipt_map
      source_attestation.a_changed_durable_spend_execute_changes_the_spend_receipt_map})
  then () else error "Unexpected oracle in Execute receipt field frames"
\<close>

end
