theory Recovery_Execute_Legal_Shape
  imports Recovery_Legal_Spend_Reply_Records
begin

lemma capture_retains_the_exact_legal_receipt_map:
  "retained_legal_receipts (capture_retained_product s) = legal_receipts (regulated_orders s)"
  by (simp add: capture_retained_product_def Let_def)

lemma capture_retains_the_exact_spend_receipt_map:
  "retained_spend_receipts (capture_retained_product s) = spend_receipts s"
  by (simp add: capture_retained_product_def Let_def)

context source_attestation
begin

lemma a_changed_durable_legal_execute_uses_the_new_receipt_reply:
  assumes changed: "capture_retained_product (fst (durable_execute directory policy authenticate verify endorse
    route token proof target (Apply_Governed_Order stage entry who expected call_id order payload) authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before))
    \<noteq> capture_retained_product before"
  shows "durable_execute directory policy authenticate verify endorse route token proof target
    (Apply_Governed_Order stage entry who expected call_id order payload) authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before =
    (before\<lparr>regulated_orders := fst (submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
       stage Regulatory_Normal who expected call_id order payload (regulated_orders before))\<rparr>,
     Durable_Execution_Reply (Observed_Legal_Result (snd (submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
       stage Regulatory_Normal who expected call_id order payload (regulated_orders before)))))"
proof -
  let ?action = "Apply_Governed_Order stage entry who expected call_id order payload"
  let ?result = "durable_execute directory policy authenticate verify endorse route token proof target ?action authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before"
  let ?producer = "submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
    stage Regulatory_Normal who expected call_id order payload (regulated_orders before)"
  let ?after = "before\<lparr>regulated_orders := fst ?producer\<rparr>"
  let ?collect = "Collect_Governed_Order stage entry who call_id order payload"
  have fresh: "\<not> authority_has_call_id call_id before"
  proof
    assume old: "authority_has_call_id call_id before"
    have "fst ?result = before"
      using old by (cases stage) (auto simp: durable_execute_def Let_def split: if_splits)
    then show False using changed by simp
  qed
  have no_spend: "spend_receipts before call_id = None"
    using fresh by (auto simp: authority_has_call_id_def unclaimed_regulated_call_def)
  have effect: "run_fresh_durable_effect permitted verified maintainers registered verified_ack
      legal_grant order_verified spend_grant spend_verified read_permitted ?action before = ?after"
    using no_spend by simp
  have effect_changed: "capture_retained_product ?after \<noteq> capture_retained_product before"
  proof
    assume equal: "capture_retained_product ?after = capture_retained_product before"
    have "capture_retained_product (fst ?result) = capture_retained_product before"
      using fresh effect equal by (cases stage) (auto simp: durable_execute_def Let_def split: if_splits)
    then show False using changed by simp
  qed
  have producer_changed: "fst ?producer \<noteq> regulated_orders before"
    using effect_changed by auto
  note stored = a_changed_legal_submission_inserts_its_exact_returned_reply[OF refl producer_changed]
  have receipt: "legal_receipts (regulated_orders ?after) call_id = Some
      \<lparr>receipt_stage = stage, receipt_order = order, receipt_payload = payload, legal_result = snd ?producer\<rparr>"
    using stored(2) by simp
  have has_after: "authority_has_call_id call_id ?after"
    using receipt by (simp add: authority_has_call_id_def unclaimed_regulated_call_def)
  have finish: "finish_durable_execution verified who ?collect ?after =
      (?after, Durable_Execution_Reply (Observed_Legal_Result (snd ?producer)))"
    using receipt by (simp add: legal_receipt_matches_def)
  show ?thesis using changed fresh effect has_after finish
    by (cases stage) (auto simp: durable_execute_def Let_def split: if_splits)
qed

end

text \<open>The changed-image premise excludes old-result lookup and unsigned/authorization
  no-effect branches. This lemma reconstructs the legal result from the actual new receipt and
  does not assert the ordinary Execute case or whole-product cross-constructor theorem.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms capture_retains_the_exact_legal_receipt_map
      capture_retains_the_exact_spend_receipt_map
      source_attestation.a_changed_durable_legal_execute_uses_the_new_receipt_reply})
  then () else error "Unexpected oracle in durable legal Execute reply target"
\<close>

end
