theory Recovery_Changed_Service_Cases
  imports "Recovery_Product_Reply_Cases" "Recovery_Product_Slot_Replies"
begin

context source_attestation
begin

lemma a_changing_scheduled_action_has_an_actual_changing_family:
  assumes produced: "result = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection action R"
    and changed: "fst result \<noteq> R"
  shows "(\<exists>route token proof target inner authorization. action = Service_Execute route token proof target inner authorization) \<or>
    (\<exists>owner successor maintainer proposal. action = Service_Handover owner successor maintainer proposal) \<or>
    (\<exists>maintenance. action = Service_Maintenance maintenance \<and> \<not> is_settlement_action maintenance) \<or>
    (\<exists>resolved. classify_service_action action (service_settlement (reopen_retained_product connection R)) = Service_Slot resolved)"
proof (cases action)
  case Service_Execute
  then show ?thesis by auto
next
  case Service_Receipt
  have "fst result = R" using produced Service_Receipt
    by (simp add: product_receipt_queries_do_not_change_the_retained_image)
  then show ?thesis using changed by simp
next
  case Service_Read
  have "fst result = R" using produced Service_Read
    by (simp add: product_reads_do_not_change_the_retained_image)
  then show ?thesis using changed by simp
next
  case Service_Capture
  have "fst result = R" using produced Service_Capture
    by (simp add: product_cache_capture_does_not_change_the_retained_image)
  then show ?thesis using changed by simp
next
  case Service_Handover
  then show ?thesis by auto
next
  case (Service_Maintenance maintenance)
  show ?thesis
  proof (cases "is_settlement_action maintenance")
    case False
    then show ?thesis using Service_Maintenance by auto
  next
    case settlement: True
    show ?thesis
    proof (cases "queue_action_at maintenance (service_settlement (reopen_retained_product connection R))")
      case None
      have observation: "classify_service_action action (service_settlement (reopen_retained_product connection R)) = Service_Observation"
        using Service_Maintenance settlement None by simp
      have unchanged: "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
          legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
          connection action R) = R"
        by (rule a_classified_observation_does_not_change_the_retained_image[OF observation])
      show ?thesis using produced changed unchanged by simp
    next
      case (Some resolved)
      then show ?thesis using Service_Maintenance settlement by auto
    qed
  qed
next
  case Service_Source_Probe
  have "fst result = R" using produced Service_Source_Probe
    by (simp add: product_source_probe_does_not_change_the_retained_image)
  then show ?thesis using changed by simp
qed

end

text \<open>The disjunction is an exhaustive proof case split over the frozen classifier.
  It is not a new field or an admissibility restriction, and the slot is resolved at its actual
  connection-specific reopened world.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.a_changing_scheduled_action_has_an_actual_changing_family})
  then () else error "Unexpected oracle in actual changing service case coverage"
\<close>

end
