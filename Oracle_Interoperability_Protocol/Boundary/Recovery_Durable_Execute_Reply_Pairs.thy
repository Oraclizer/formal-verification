theory Recovery_Durable_Execute_Reply_Pairs
  imports Recovery_Ordinary_Fresh_Pairs Recovery_Execute_Ordinary_Separation "Recovery_Execute_Receipt_Separation"
begin

context source_attestation
begin

lemma a_changed_durable_execute_has_one_of_the_three_actual_producers:
  assumes produced: "result = durable_execute directory policy authenticate verify endorse route token proof target action authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s"
    and changed: "capture_retained_product (fst result) \<noteq> capture_retained_product s"
  shows "(\<exists>stage entry actor expected call_id order payload. action = Apply_Governed_Order stage entry actor expected call_id order payload) \<or>
    (\<exists>entry actor expected call_id payload spend_authorization. action = Apply_Governed_Spend entry actor expected call_id payload spend_authorization) \<or>
    (\<exists>entry actor expected call_id payload. action = Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload))"
proof -
  have receipt: "execution_receipt_request action \<noteq> None"
  proof
    assume missing: "execution_receipt_request action = None"
    have "fst result = s" using produced missing by (simp add: durable_execute_def split: option.splits)
    then show False using changed by simp
  qed
  show ?thesis
  proof (cases action)
    case Apply_Governed_Order
    then show ?thesis by blast
  next
    case Apply_Governed_Spend
    then show ?thesis by blast
  next
    case Collect_Governed_Order
    then show ?thesis using receipt by simp
  next
    case Collect_Governed_Spend
    then show ?thesis using receipt by simp
  next
    case (Ordinary_Product_Action read_action)
    show ?thesis
    proof (cases read_action)
      case Capture_Read
      then show ?thesis using Ordinary_Product_Action receipt by simp
    next
      case Execute_Checked
      then show ?thesis using Ordinary_Product_Action by blast
    next
      case Read_Authority_Action
      then show ?thesis using Ordinary_Product_Action receipt by simp
    qed
  qed
qed

lemma equal_changed_durable_execute_images_determine_the_reply:
  assumes produced_a: "result_a = durable_execute directory policy authenticate verify endorse route_a token_a proof_a target_a action_a authorization_a
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_a"
    and produced_b: "result_b = durable_execute directory policy authenticate verify endorse route_b token_b proof_b target_b action_b authorization_b
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_b"
    and before_images: "capture_retained_product before_a = capture_retained_product before_b"
    and changed_a: "capture_retained_product (fst result_a) \<noteq> capture_retained_product before_a"
    and same_images: "capture_retained_product (fst result_a) = capture_retained_product (fst result_b)"
  shows "snd result_a = snd result_b"
proof -
  have changed_b: "capture_retained_product (fst result_b) \<noteq> capture_retained_product before_b"
    using before_images changed_a same_images by auto
  have reverse_before: "capture_retained_product before_b = capture_retained_product before_a" by (rule sym[OF before_images])
  have family_a:
    "(\<exists>stage entry actor expected call_id order payload. action_a = Apply_Governed_Order stage entry actor expected call_id order payload) \<or>
     (\<exists>entry actor expected call_id payload spend_authorization. action_a = Apply_Governed_Spend entry actor expected call_id payload spend_authorization) \<or>
     (\<exists>entry actor expected call_id payload. action_a = Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload))"
    by (rule a_changed_durable_execute_has_one_of_the_three_actual_producers[OF produced_a changed_a])
  have family_b:
    "(\<exists>stage entry actor expected call_id order payload. action_b = Apply_Governed_Order stage entry actor expected call_id order payload) \<or>
     (\<exists>entry actor expected call_id payload spend_authorization. action_b = Apply_Governed_Spend entry actor expected call_id payload spend_authorization) \<or>
     (\<exists>entry actor expected call_id payload. action_b = Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload))"
    by (rule a_changed_durable_execute_has_one_of_the_three_actual_producers[OF produced_b changed_b])
  from family_a consider
      (legal_a) stage entry actor expected call_id order payload where "action_a = Apply_Governed_Order stage entry actor expected call_id order payload"
    | (spend_a) entry actor expected call_id payload spend_authorization where "action_a = Apply_Governed_Spend entry actor expected call_id payload spend_authorization"
    | (ordinary_a) entry actor expected call_id payload where "action_a = Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)" by blast
  then show ?thesis
  proof cases
    case legal_a
    from family_b consider
        (legal_b) stage entry actor expected call_id order payload where "action_b = Apply_Governed_Order stage entry actor expected call_id order payload"
      | (spend_b) entry actor expected call_id payload spend_authorization where "action_b = Apply_Governed_Spend entry actor expected call_id payload spend_authorization"
      | (ordinary_b) entry actor expected call_id payload where "action_b = Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)" by blast
    then show ?thesis
    proof cases
      case legal_b
      show ?thesis by (rule two_changed_legal_executes_with_equal_captured_images_have_equal_replies
        [OF produced_a[unfolded legal_a] produced_b[unfolded legal_b] before_images changed_a same_images])
    next
      case spend_b
      have different: "capture_retained_product (fst result_a) \<noteq> capture_retained_product (fst result_b)"
        by (rule a_changed_legal_execute_cannot_share_its_image_with_a_spend_execute
          [OF produced_a[unfolded legal_a] produced_b[unfolded spend_b] before_images changed_a])
      then show ?thesis using same_images by simp
    next
      case ordinary_b
      have different: "capture_retained_product (fst result_a) \<noteq> capture_retained_product (fst result_b)"
        by (rule a_changed_legal_execute_cannot_share_its_image_with_an_ordinary_execute
          [OF produced_a[unfolded legal_a] produced_b[unfolded ordinary_b] before_images changed_a])
      then show ?thesis using same_images by simp
    qed
  next
    case spend_a
    from family_b consider
        (legal_b) stage entry actor expected call_id order payload where "action_b = Apply_Governed_Order stage entry actor expected call_id order payload"
      | (spend_b) entry actor expected call_id payload spend_authorization where "action_b = Apply_Governed_Spend entry actor expected call_id payload spend_authorization"
      | (ordinary_b) entry actor expected call_id payload where "action_b = Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)" by blast
    then show ?thesis
    proof cases
      case legal_b
      have different: "capture_retained_product (fst result_b) \<noteq> capture_retained_product (fst result_a)"
        by (rule a_changed_legal_execute_cannot_share_its_image_with_a_spend_execute
          [OF produced_b[unfolded legal_b] produced_a[unfolded spend_a] reverse_before changed_b])
      then show ?thesis using same_images by simp
    next
      case spend_b
      show ?thesis by (rule two_changed_spend_executes_with_equal_captured_images_have_equal_replies
        [OF produced_a[unfolded spend_a] produced_b[unfolded spend_b] before_images changed_a same_images])
    next
      case ordinary_b
      have different: "capture_retained_product (fst result_a) \<noteq> capture_retained_product (fst result_b)"
        by (rule a_changed_spend_execute_cannot_share_its_image_with_an_ordinary_execute
          [OF produced_a[unfolded spend_a] produced_b[unfolded ordinary_b] before_images changed_a])
      then show ?thesis using same_images by simp
    qed
  next
    case ordinary_a
    from family_b consider
        (legal_b) stage entry actor expected call_id order payload where "action_b = Apply_Governed_Order stage entry actor expected call_id order payload"
      | (spend_b) entry actor expected call_id payload spend_authorization where "action_b = Apply_Governed_Spend entry actor expected call_id payload spend_authorization"
      | (ordinary_b) entry actor expected call_id payload where "action_b = Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)" by blast
    then show ?thesis
    proof cases
      case legal_b
      have different: "capture_retained_product (fst result_b) \<noteq> capture_retained_product (fst result_a)"
        by (rule a_changed_legal_execute_cannot_share_its_image_with_an_ordinary_execute
          [OF produced_b[unfolded legal_b] produced_a[unfolded ordinary_a] reverse_before changed_b])
      then show ?thesis using same_images by simp
    next
      case spend_b
      have different: "capture_retained_product (fst result_b) \<noteq> capture_retained_product (fst result_a)"
        by (rule a_changed_spend_execute_cannot_share_its_image_with_an_ordinary_execute
          [OF produced_b[unfolded spend_b] produced_a[unfolded ordinary_a] reverse_before changed_b])
      then show ?thesis using same_images by simp
    next
      case ordinary_b
      show ?thesis by (rule two_changed_ordinary_executes_with_equal_images_have_equal_replies
        [OF produced_a[unfolded ordinary_a] produced_b[unfolded ordinary_b] before_images changed_a same_images])
    qed
  qed
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.a_changed_durable_execute_has_one_of_the_three_actual_producers
      source_attestation.equal_changed_durable_execute_images_determine_the_reply})
  then () else error "Unexpected oracle in all actual durable Execute reply pairs"
\<close>

end
