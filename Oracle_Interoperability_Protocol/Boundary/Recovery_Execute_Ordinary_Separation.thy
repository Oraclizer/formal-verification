theory Recovery_Execute_Ordinary_Separation
  imports Recovery_Ordinary_Receipt_Frames "Recovery_Execute_Receipt_Frames"
begin

context source_attestation
begin

lemma a_changed_legal_execute_cannot_share_its_image_with_an_ordinary_execute:
  assumes produced_a: "result_a = durable_execute directory policy authenticate verify endorse route_a token_a proof_a target_a
      (Apply_Governed_Order stage_a entry_a who_a expected_a id_a order_a payload_a) authorization_a
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_a"
    and produced_b: "result_b = durable_execute directory policy authenticate verify endorse route_b token_b proof_b target_b
      (Ordinary_Product_Action (Execute_Checked entry_b who_b expected_b id_b payload_b)) authorization_b
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
    using produced_b ordinary_durable_execute_keeps_both_regulated_receipt_maps(1) by simp
  have same_before: "legal_receipts (regulated_orders before_a) = legal_receipts (regulated_orders before_b)"
    using arg_cong[OF before_images, of retained_legal_receipts]
    by (simp add: capture_retains_the_exact_legal_receipt_map)
  have same_after: "legal_receipts (regulated_orders (fst result_a)) = legal_receipts (regulated_orders (fst result_b))"
    using arg_cong[OF equal_images, of retained_legal_receipts]
    by (simp add: capture_retains_the_exact_legal_receipt_map)
  show False using changed_map framed_map same_before same_after by simp
qed

lemma a_changed_spend_execute_cannot_share_its_image_with_an_ordinary_execute:
  assumes produced_a: "result_a = durable_execute directory policy authenticate verify endorse route_a token_a proof_a target_a
      (Apply_Governed_Spend entry_a who_a expected_a id_a payload_a spend_authorization_a) authorization_a
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_a"
    and produced_b: "result_b = durable_execute directory policy authenticate verify endorse route_b token_b proof_b target_b
      (Ordinary_Product_Action (Execute_Checked entry_b who_b expected_b id_b payload_b)) authorization_b
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_b"
    and before_images: "capture_retained_product before_a = capture_retained_product before_b"
    and changed_a: "capture_retained_product (fst result_a) \<noteq> capture_retained_product before_a"
  shows "capture_retained_product (fst result_a) \<noteq> capture_retained_product (fst result_b)"
proof
  assume equal_images: "capture_retained_product (fst result_a) = capture_retained_product (fst result_b)"
  have changed_actual: "capture_retained_product (fst (durable_execute directory policy authenticate verify endorse route_a token_a proof_a target_a
      (Apply_Governed_Spend entry_a who_a expected_a id_a payload_a spend_authorization_a) authorization_a
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_a))
      \<noteq> capture_retained_product before_a" using produced_a changed_a by simp
  have changed_map: "spend_receipts (fst result_a) \<noteq> spend_receipts before_a"
    using a_changed_durable_spend_execute_changes_the_spend_receipt_map[OF changed_actual] produced_a by simp
  have framed_map: "spend_receipts (fst result_b) = spend_receipts before_b"
    using produced_b ordinary_durable_execute_keeps_both_regulated_receipt_maps(2) by simp
  have same_before: "spend_receipts before_a = spend_receipts before_b"
    using arg_cong[OF before_images, of retained_spend_receipts]
    by (simp add: capture_retains_the_exact_spend_receipt_map)
  have same_after: "spend_receipts (fst result_a) = spend_receipts (fst result_b)"
    using arg_cong[OF equal_images, of retained_spend_receipts]
    by (simp add: capture_retains_the_exact_spend_receipt_map)
  show False using changed_map framed_map same_before same_after by simp
qed

end

text \<open>The inequalities use actual receipt-map changes and frames. Distinct reply datatype
  constructors are not used to infer distinct states. Full scheduler-level RFE remains to assemble.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.a_changed_legal_execute_cannot_share_its_image_with_an_ordinary_execute
      source_attestation.a_changed_spend_execute_cannot_share_its_image_with_an_ordinary_execute})
  then () else error "Unexpected oracle in ordinary/legal/spend Execute separation"
\<close>

end
