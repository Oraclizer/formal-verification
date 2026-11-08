theory Recovery_Execute_Typed_Reply_Pairs
  imports Recovery_Execute_Receipt_Frames
begin

context source_attestation
begin

lemma two_changed_legal_executes_with_equal_captured_images_have_equal_replies:
  assumes produced_a: "result_a = durable_execute directory policy authenticate verify endorse route_a token_a proof_a target_a
      (Apply_Governed_Order stage_a entry_a who_a expected_a id_a order_a payload_a) authorization_a
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_a"
    and produced_b: "result_b = durable_execute directory policy authenticate verify endorse route_b token_b proof_b target_b
      (Apply_Governed_Order stage_b entry_b who_b expected_b id_b order_b payload_b) authorization_b
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_b"
    and before_images: "capture_retained_product before_a = capture_retained_product before_b"
    and changed_a: "capture_retained_product (fst result_a) \<noteq> capture_retained_product before_a"
    and same_images: "capture_retained_product (fst result_a) = capture_retained_product (fst result_b)"
  shows "snd result_a = snd result_b"
proof -
  let ?producer_a = "submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
    stage_a Regulatory_Normal who_a expected_a id_a order_a payload_a (regulated_orders before_a)"
  let ?producer_b = "submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
    stage_b Regulatory_Normal who_b expected_b id_b order_b payload_b (regulated_orders before_b)"
  have changed_b: "capture_retained_product (fst result_b) \<noteq> capture_retained_product before_b"
    using before_images changed_a same_images by auto
  have changed_actual_a: "capture_retained_product (fst (durable_execute directory policy authenticate verify endorse route_a token_a proof_a target_a
      (Apply_Governed_Order stage_a entry_a who_a expected_a id_a order_a payload_a) authorization_a
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_a))
      \<noteq> capture_retained_product before_a" using changed_a produced_a by simp
  have changed_actual_b: "capture_retained_product (fst (durable_execute directory policy authenticate verify endorse route_b token_b proof_b target_b
      (Apply_Governed_Order stage_b entry_b who_b expected_b id_b order_b payload_b) authorization_b
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_b))
      \<noteq> capture_retained_product before_b" using changed_b produced_b by simp
  have shape_a: "result_a = (before_a\<lparr>regulated_orders := fst ?producer_a\<rparr>,
      Durable_Execution_Reply (Observed_Legal_Result (snd ?producer_a)))"
    using produced_a a_changed_durable_legal_execute_uses_the_new_receipt_reply[OF changed_actual_a] by simp
  have shape_b: "result_b = (before_b\<lparr>regulated_orders := fst ?producer_b\<rparr>,
      Durable_Execution_Reply (Observed_Legal_Result (snd ?producer_b)))"
    using produced_b a_changed_durable_legal_execute_uses_the_new_receipt_reply[OF changed_actual_b] by simp
  have producer_changed_a: "fst ?producer_a \<noteq> regulated_orders before_a" using changed_a shape_a by auto
  have producer_changed_b: "fst ?producer_b \<noteq> regulated_orders before_b" using changed_b shape_b by auto
  have base_maps: "legal_receipts (regulated_orders before_a) = legal_receipts (regulated_orders before_b)"
    using arg_cong[OF before_images, of retained_legal_receipts]
    by (simp add: capture_retains_the_exact_legal_receipt_map)
  have result_maps: "legal_receipts (fst ?producer_a) = legal_receipts (fst ?producer_b)"
    using arg_cong[OF same_images, of retained_legal_receipts] shape_a shape_b
    by (simp add: capture_retains_the_exact_legal_receipt_map)
  have replies: "snd ?producer_a = snd ?producer_b"
    by (rule equal_changed_legal_receipt_maps_determine_the_returned_reply
      [OF refl refl producer_changed_a producer_changed_b base_maps result_maps])
  show ?thesis using shape_a shape_b replies by simp
qed

lemma two_changed_spend_executes_with_equal_captured_images_have_equal_replies:
  assumes produced_a: "result_a = durable_execute directory policy authenticate verify endorse route_a token_a proof_a target_a
      (Apply_Governed_Spend entry_a who_a expected_a id_a payload_a spend_authorization_a) authorization_a
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_a"
    and produced_b: "result_b = durable_execute directory policy authenticate verify endorse route_b token_b proof_b target_b
      (Apply_Governed_Spend entry_b who_b expected_b id_b payload_b spend_authorization_b) authorization_b
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_b"
    and before_images: "capture_retained_product before_a = capture_retained_product before_b"
    and changed_a: "capture_retained_product (fst result_a) \<noteq> capture_retained_product before_a"
    and same_images: "capture_retained_product (fst result_a) = capture_retained_product (fst result_b)"
  shows "snd result_a = snd result_b"
proof -
  let ?producer_a = "submit_governed_spend spend_grant spend_verified permitted verified maintainers registered verified_ack
    Regulatory_Normal who_a expected_a id_a payload_a spend_authorization_a before_a"
  let ?producer_b = "submit_governed_spend spend_grant spend_verified permitted verified maintainers registered verified_ack
    Regulatory_Normal who_b expected_b id_b payload_b spend_authorization_b before_b"
  have changed_b: "capture_retained_product (fst result_b) \<noteq> capture_retained_product before_b"
    using before_images changed_a same_images by auto
  have changed_actual_a: "capture_retained_product (fst (durable_execute directory policy authenticate verify endorse route_a token_a proof_a target_a
      (Apply_Governed_Spend entry_a who_a expected_a id_a payload_a spend_authorization_a) authorization_a
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_a))
      \<noteq> capture_retained_product before_a" using changed_a produced_a by simp
  have changed_actual_b: "capture_retained_product (fst (durable_execute directory policy authenticate verify endorse route_b token_b proof_b target_b
      (Apply_Governed_Spend entry_b who_b expected_b id_b payload_b spend_authorization_b) authorization_b
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_b))
      \<noteq> capture_retained_product before_b" using changed_b produced_b by simp
  have shape_a: "result_a = (fst ?producer_a, Durable_Execution_Reply (Observed_Spend_Result (snd ?producer_a)))"
    using produced_a a_changed_durable_spend_execute_uses_the_new_receipt_reply[OF changed_actual_a] by simp
  have shape_b: "result_b = (fst ?producer_b, Durable_Execution_Reply (Observed_Spend_Result (snd ?producer_b)))"
    using produced_b a_changed_durable_spend_execute_uses_the_new_receipt_reply[OF changed_actual_b] by simp
  have producer_changed_a: "fst ?producer_a \<noteq> before_a" using changed_a shape_a by auto
  have producer_changed_b: "fst ?producer_b \<noteq> before_b" using changed_b shape_b by auto
  have base_maps: "spend_receipts before_a = spend_receipts before_b"
    using arg_cong[OF before_images, of retained_spend_receipts]
    by (simp add: capture_retains_the_exact_spend_receipt_map)
  have result_maps: "spend_receipts (fst ?producer_a) = spend_receipts (fst ?producer_b)"
    using arg_cong[OF same_images, of retained_spend_receipts] shape_a shape_b
    by (simp add: capture_retains_the_exact_spend_receipt_map)
  have replies: "snd ?producer_a = snd ?producer_b"
    by (rule equal_changed_spend_receipt_maps_determine_the_returned_reply
      [OF refl refl producer_changed_a producer_changed_b base_maps result_maps])
  show ?thesis using shape_a shape_b replies by simp
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.two_changed_legal_executes_with_equal_captured_images_have_equal_replies
      source_attestation.two_changed_spend_executes_with_equal_captured_images_have_equal_replies})
  then () else error "Unexpected oracle in typed Execute reply pairs"
\<close>

end
