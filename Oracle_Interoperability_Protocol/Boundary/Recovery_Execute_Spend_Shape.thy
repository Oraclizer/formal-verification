theory Recovery_Execute_Spend_Shape
  imports Recovery_Execute_Legal_Shape
begin

context source_attestation
begin

lemma a_changed_durable_spend_execute_uses_the_new_receipt_reply:
  assumes changed: "capture_retained_product (fst (durable_execute directory policy authenticate verify endorse
    route token proof target (Apply_Governed_Spend entry who expected call_id payload spend_authorization) authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before))
    \<noteq> capture_retained_product before"
  shows "durable_execute directory policy authenticate verify endorse route token proof target
    (Apply_Governed_Spend entry who expected call_id payload spend_authorization) authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before =
    (fst (submit_governed_spend spend_grant spend_verified permitted verified maintainers registered verified_ack
       Regulatory_Normal who expected call_id payload spend_authorization before),
     Durable_Execution_Reply (Observed_Spend_Result (snd (submit_governed_spend spend_grant spend_verified
       permitted verified maintainers registered verified_ack Regulatory_Normal who expected call_id payload spend_authorization before))))"
proof -
  let ?action = "Apply_Governed_Spend entry who expected call_id payload spend_authorization"
  let ?result = "durable_execute directory policy authenticate verify endorse route token proof target ?action authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before"
  let ?producer = "submit_governed_spend spend_grant spend_verified permitted verified maintainers registered verified_ack
    Regulatory_Normal who expected call_id payload spend_authorization before"
  let ?after = "fst ?producer"
  let ?collect = "Collect_Governed_Spend who call_id payload spend_authorization"
  have fresh: "\<not> authority_has_call_id call_id before"
  proof
    assume old: "authority_has_call_id call_id before"
    have "fst ?result = before"
      using old by (auto simp: durable_execute_def Let_def split: if_splits)
    then show False using changed by simp
  qed
  have effect: "run_fresh_durable_effect permitted verified maintainers registered verified_ack
      legal_grant order_verified spend_grant spend_verified read_permitted ?action before = ?after"
    by simp
  have effect_changed: "capture_retained_product ?after \<noteq> capture_retained_product before"
  proof
    assume equal: "capture_retained_product ?after = capture_retained_product before"
    have "capture_retained_product (fst ?result) = capture_retained_product before"
      using fresh effect equal by (auto simp: durable_execute_def Let_def split: if_splits)
    then show False using changed by simp
  qed
  have producer_changed: "fst ?producer \<noteq> before" using effect_changed by auto
  note stored = a_changed_spend_submission_inserts_its_exact_returned_reply[OF refl producer_changed]
  have receipt: "spend_receipts ?after call_id = Some
      \<lparr>spend_receipt_payload = payload, spend_receipt_order = spend_authorization, spend_receipt_reply = snd ?producer\<rparr>"
    using stored(2) by simp
  have has_after: "authority_has_call_id call_id ?after"
    using receipt by (simp add: authority_has_call_id_def unclaimed_regulated_call_def)
  have finish: "finish_durable_execution verified who ?collect ?after =
      (?after, Durable_Execution_Reply (Observed_Spend_Result (snd ?producer)))"
    using receipt by simp
  show ?thesis using changed fresh effect has_after finish
    by (auto simp: durable_execute_def Let_def split: if_splits)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.a_changed_durable_spend_execute_uses_the_new_receipt_reply})
  then () else error "Unexpected oracle in durable spend Execute reply target"
\<close>

end
