theory Recovery_Scheduled_Product_Reply_Pairs
  imports Recovery_Changed_Service_Cases Recovery_Fixed_Tag_Reply_Pairs Recovery_Scheduled_Execute_Replies
    Recovery_Maintenance_Separation Recovery_Execute_Slot_Separation
begin

context source_attestation
begin

lemma equal_changed_scheduled_product_images_determine_the_reply:
  assumes produced_a: "result_a = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_a action_a R"
    and produced_b: "result_b = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_b action_b R"
    and changed_a: "fst result_a \<noteq> R"
    and same_images: "fst result_a = fst result_b"
  shows "snd result_a = snd result_b"
proof -
  let ?step = "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack"
  have changed_b: "fst result_b \<noteq> R" using changed_a same_images by simp
  have actual_changed: "fst (?step connection_a action_a R) \<noteq> R" using produced_a changed_a by simp
  have actual_same: "fst (?step connection_a action_a R) = fst (?step connection_b action_b R)"
    using produced_a produced_b same_images by simp
  have family_a:
    "(\<exists>route token proof target inner authorization. action_a = Service_Execute route token proof target inner authorization) \<or>
     (\<exists>owner successor maintainer proposal. action_a = Service_Handover owner successor maintainer proposal) \<or>
     (\<exists>maintenance. action_a = Service_Maintenance maintenance \<and> \<not> is_settlement_action maintenance) \<or>
     (\<exists>resolved. classify_service_action action_a (service_settlement (reopen_retained_product connection_a R)) = Service_Slot resolved)"
    by (rule a_changing_scheduled_action_has_an_actual_changing_family[OF produced_a changed_a])
  have family_b:
    "(\<exists>route token proof target inner authorization. action_b = Service_Execute route token proof target inner authorization) \<or>
     (\<exists>owner successor maintainer proposal. action_b = Service_Handover owner successor maintainer proposal) \<or>
     (\<exists>maintenance. action_b = Service_Maintenance maintenance \<and> \<not> is_settlement_action maintenance) \<or>
     (\<exists>resolved. classify_service_action action_b (service_settlement (reopen_retained_product connection_b R)) = Service_Slot resolved)"
    by (rule a_changing_scheduled_action_has_an_actual_changing_family[OF produced_b changed_b])
  from family_a consider
      (execute_a) route_a token_a proof_a target_a inner_a authorization_a where "action_a = Service_Execute route_a token_a proof_a target_a inner_a authorization_a"
    | (handover_a) owner_a successor_a maintainer_a proposal_a where "action_a = Service_Handover owner_a successor_a maintainer_a proposal_a"
    | (maintenance_a) maintenance_a where "action_a = Service_Maintenance maintenance_a" "\<not> is_settlement_action maintenance_a"
    | (slot_a) resolved_a where "classify_service_action action_a (service_settlement (reopen_retained_product connection_a R)) = Service_Slot resolved_a" by blast
  then show ?thesis
  proof cases
    case execute_a
    from family_b consider
        (execute_b) route_b token_b proof_b target_b inner_b authorization_b where "action_b = Service_Execute route_b token_b proof_b target_b inner_b authorization_b"
      | (handover_b) owner_b successor_b maintainer_b proposal_b where "action_b = Service_Handover owner_b successor_b maintainer_b proposal_b"
      | (maintenance_b) maintenance_b where "action_b = Service_Maintenance maintenance_b" "\<not> is_settlement_action maintenance_b"
      | (slot_b) resolved_b where "classify_service_action action_b (service_settlement (reopen_retained_product connection_b R)) = Service_Slot resolved_b" by blast
    then show ?thesis
    proof cases
      case execute_b
      show ?thesis by (rule equal_changed_scheduled_execute_images_determine_the_reply
        [OF produced_a[unfolded execute_a] produced_b[unfolded execute_b] changed_a same_images])
    next
      case handover_b
      have different: "fst result_b \<noteq> fst result_a"
        by (rule a_changed_handover_cannot_share_any_execute_image
          [OF produced_b[unfolded handover_b] changed_b produced_a[unfolded execute_a]])
      then show ?thesis using same_images by simp
    next
      case maintenance_b
      have different: "fst result_b \<noteq> fst result_a"
        by (rule a_changed_nonsettlement_maintenance_cannot_share_any_execute_image
          [OF produced_b[unfolded maintenance_b(1)] maintenance_b(2) changed_b produced_a[unfolded execute_a]])
      then show ?thesis using same_images by simp
    next
      case slot_b
      have different: "fst result_a \<noteq> fst result_b"
        by (rule a_changed_scheduled_execute_cannot_share_a_classified_slot_image
          [OF produced_a[unfolded execute_a] changed_a slot_b produced_b])
      then show ?thesis using same_images by simp
    qed
  next
    case handover_a
    from family_b consider
        (execute_b) route_b token_b proof_b target_b inner_b authorization_b where "action_b = Service_Execute route_b token_b proof_b target_b inner_b authorization_b"
      | (handover_b) owner_b successor_b maintainer_b proposal_b where "action_b = Service_Handover owner_b successor_b maintainer_b proposal_b"
      | (maintenance_b) maintenance_b where "action_b = Service_Maintenance maintenance_b" "\<not> is_settlement_action maintenance_b"
      | (slot_b) resolved_b where "classify_service_action action_b (service_settlement (reopen_retained_product connection_b R)) = Service_Slot resolved_b" by blast
    then show ?thesis
    proof cases
      case execute_b
      have different: "fst result_a \<noteq> fst result_b"
        by (rule a_changed_handover_cannot_share_any_execute_image
          [OF produced_a[unfolded handover_a] changed_a produced_b[unfolded execute_b]])
      then show ?thesis using same_images by simp
    next
      case handover_b
      show ?thesis by (rule two_changed_scheduled_handovers_have_equal_replies
        [OF produced_a[unfolded handover_a] produced_b[unfolded handover_b] changed_a changed_b])
    next
      case maintenance_b
      have different: "fst result_a \<noteq> fst result_b"
        by (rule a_changed_handover_cannot_share_any_maintenance_image
          [OF produced_a[unfolded handover_a] changed_a produced_b[unfolded maintenance_b(1)]])
      then show ?thesis using same_images by simp
    next
      case slot_b
      have different: "fst result_a \<noteq> fst result_b"
        by (rule a_changed_handover_cannot_share_the_image_of_a_classified_slot
          [OF produced_a[unfolded handover_a] changed_a slot_b produced_b])
      then show ?thesis using same_images by simp
    qed
  next
    case maintenance_a
    from family_b consider
        (execute_b) route_b token_b proof_b target_b inner_b authorization_b where "action_b = Service_Execute route_b token_b proof_b target_b inner_b authorization_b"
      | (handover_b) owner_b successor_b maintainer_b proposal_b where "action_b = Service_Handover owner_b successor_b maintainer_b proposal_b"
      | (maintenance_b) maintenance_b where "action_b = Service_Maintenance maintenance_b" "\<not> is_settlement_action maintenance_b"
      | (slot_b) resolved_b where "classify_service_action action_b (service_settlement (reopen_retained_product connection_b R)) = Service_Slot resolved_b" by blast
    then show ?thesis
    proof cases
      case execute_b
      have different: "fst result_a \<noteq> fst result_b"
        by (rule a_changed_nonsettlement_maintenance_cannot_share_any_execute_image
          [OF produced_a[unfolded maintenance_a(1)] maintenance_a(2) changed_a produced_b[unfolded execute_b]])
      then show ?thesis using same_images by simp
    next
      case handover_b
      have different: "fst result_b \<noteq> fst result_a"
        by (rule a_changed_handover_cannot_share_any_maintenance_image
          [OF produced_b[unfolded handover_b] changed_b produced_a[unfolded maintenance_a(1)]])
      then show ?thesis using same_images by simp
    next
      case maintenance_b
      show ?thesis by (rule two_changed_nonsettlement_maintenances_have_equal_replies
        [OF produced_a[unfolded maintenance_a(1)] produced_b[unfolded maintenance_b(1)] maintenance_a(2) maintenance_b(2) changed_a changed_b])
    next
      case slot_b
      have different: "fst result_a \<noteq> fst result_b"
        by (rule a_changed_nonsettlement_maintenance_cannot_share_a_classified_slot_image
          [OF produced_a[unfolded maintenance_a(1)] maintenance_a(2) changed_a slot_b produced_b])
      then show ?thesis using same_images by simp
    qed
  next
    case slot_a
    from family_b consider
        (execute_b) route_b token_b proof_b target_b inner_b authorization_b where "action_b = Service_Execute route_b token_b proof_b target_b inner_b authorization_b"
      | (handover_b) owner_b successor_b maintainer_b proposal_b where "action_b = Service_Handover owner_b successor_b maintainer_b proposal_b"
      | (maintenance_b) maintenance_b where "action_b = Service_Maintenance maintenance_b" "\<not> is_settlement_action maintenance_b"
      | (slot_b) resolved_b where "classify_service_action action_b (service_settlement (reopen_retained_product connection_b R)) = Service_Slot resolved_b" by blast
    then show ?thesis
    proof cases
      case execute_b
      have different: "fst result_b \<noteq> fst result_a"
        by (rule a_changed_scheduled_execute_cannot_share_a_classified_slot_image
          [OF produced_b[unfolded execute_b] changed_b slot_a produced_a])
      then show ?thesis using same_images by simp
    next
      case handover_b
      have different: "fst result_b \<noteq> fst result_a"
        by (rule a_changed_handover_cannot_share_the_image_of_a_classified_slot
          [OF produced_b[unfolded handover_b] changed_b slot_a produced_a])
      then show ?thesis using same_images by simp
    next
      case maintenance_b
      have different: "fst result_b \<noteq> fst result_a"
        by (rule a_changed_nonsettlement_maintenance_cannot_share_a_classified_slot_image
          [OF produced_b[unfolded maintenance_b(1)] maintenance_b(2) changed_b slot_a produced_a])
      then show ?thesis using same_images by simp
    next
      case slot_b
      have actual_replies: "snd (?step connection_a action_a R) = snd (?step connection_b action_b R)"
        by (rule two_changed_classified_slots_with_the_same_image_have_the_same_reply
          [OF slot_a slot_b actual_changed actual_same])
      show ?thesis using actual_replies produced_a produced_b by simp
    qed
  qed
qed

end

text \<open>Every changing constructor family and both orientations of each cross-family pair
  are consumed. The same retained starting image is reopened independently at each connection.
  This remains a source draft until the entire dependency closure passes the kernel.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.equal_changed_scheduled_product_images_determine_the_reply})
  then () else error "Unexpected oracle in actual scheduled product reply pair coverage"
\<close>

end
