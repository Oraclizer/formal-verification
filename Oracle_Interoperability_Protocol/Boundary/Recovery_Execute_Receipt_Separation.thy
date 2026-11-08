theory Recovery_Execute_Receipt_Separation
  imports Recovery_Ordinary_Completion_Pairs
begin

context source_attestation
begin

lemma a_changed_legal_execute_cannot_share_its_image_with_a_spend_execute:
  assumes produced_a: "result_a = durable_execute directory policy authenticate verify endorse route_a token_a proof_a target_a
      (Apply_Governed_Order stage_a entry_a who_a expected_a id_a order_a payload_a) authorization_a
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_a"
    and produced_b: "result_b = durable_execute directory policy authenticate verify endorse route_b token_b proof_b target_b
      (Apply_Governed_Spend entry_b who_b expected_b id_b payload_b spend_authorization_b) authorization_b
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_b"
    and before_images: "capture_retained_product before_a = capture_retained_product before_b"
    and changed_a: "capture_retained_product (fst result_a) \<noteq> capture_retained_product before_a"
  shows "capture_retained_product (fst result_a) \<noteq> capture_retained_product (fst result_b)"
proof
  assume equal_images: "capture_retained_product (fst result_a) = capture_retained_product (fst result_b)"
  have changed_actual: "capture_retained_product (fst (durable_execute directory policy authenticate verify endorse route_a token_a proof_a target_a
      (Apply_Governed_Order stage_a entry_a who_a expected_a id_a order_a payload_a) authorization_a
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_a))
      \<noteq> capture_retained_product before_a" using produced_a changed_a by simp
  have changed_map: "legal_receipts (regulated_orders (fst result_a)) \<noteq> legal_receipts (regulated_orders before_a)"
    using a_changed_durable_legal_execute_changes_the_legal_receipt_map[OF changed_actual] produced_a by simp
  have framed_map: "legal_receipts (regulated_orders (fst result_b)) = legal_receipts (regulated_orders before_b)"
    using produced_b durable_spend_execute_keeps_the_legal_receipt_map by simp
  have same_before: "legal_receipts (regulated_orders before_a) = legal_receipts (regulated_orders before_b)"
    using arg_cong[OF before_images, of retained_legal_receipts]
    by (simp add: capture_retains_the_exact_legal_receipt_map)
  have same_after: "legal_receipts (regulated_orders (fst result_a)) = legal_receipts (regulated_orders (fst result_b))"
    using arg_cong[OF equal_images, of retained_legal_receipts]
    by (simp add: capture_retains_the_exact_legal_receipt_map)
  show False using changed_map framed_map same_before same_after by simp
qed

end

text \<open>This separates two concrete Execute constructors by a retained receipt field. It
  does not assume that unequal reply constructors force unequal states, and does not close the
  remaining ordinary-execution or owner/maintenance cross-constructor cases.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.a_changed_legal_execute_cannot_share_its_image_with_a_spend_execute})
  then () else error "Unexpected oracle in typed Execute effect separation"
\<close>

end
