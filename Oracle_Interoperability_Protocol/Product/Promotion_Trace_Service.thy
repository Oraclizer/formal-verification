theory Promotion_Trace_Service
  imports Promotion_Trace_Execution Parallel_Service
begin

context source_attestation
begin

lemma product_handover_has_a_real_public_context_segment:
  "source_segment (actual_product_calls s)
    (actual_product_calls (handover_product_owner directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal s))"
proof -
  let ?old = "identity_source s"
  let ?action = "Lock_Install maintainer (transfer_epoch proposal) (transfer_contexts proposal)
      (handover_sessions proposal (product_sessions (product_durable ?old)))"
  have lift: "source_segment (product_calls ?old)
    (product_calls (lock_product_step (\<lambda>_ _ _. False) (\<lambda>_ _ _ _. False) maintainers registered ?action ?old))"
    unfolding source_segment_def by (rule lock_product_step_is_public_segment)
  show ?thesis using lift
    by (simp del: lock_product_step.simps add: handover_product_owner_def apply_owner_handover_def actual_product_calls_def
         replace_identity_source_consumes_the_same_authority Let_def split: if_splits)
qed

lemma service_reads_preserve_the_actual_source_for_any_selected_read_state:
  "actual_product_calls (replace_regulated_reads reads s) = exact_calls (read_authority reads)"
  by (simp add: exact_read_calls_are_the_product_calls[symmetric])

lemma replacing_queue_keeps_the_actual_source_calls [simp]:
  "actual_product_calls (replace_service_jobs jobs s) = actual_product_calls s"
  by (simp add: actual_product_calls_def)

lemma every_service_action_has_a_public_source_segment:
  "source_segment (actual_product_calls s)
    (actual_product_calls (fst (live_product_service_step directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action s)))"
proof (cases action)
  case (Service_Execute route token session_value target submitted endorsement)
  then show ?thesis by (simp add: Let_def durable_endpoint_execution_has_a_public_segment)
next
  case (Service_Handover former successor maintainer proposal)
  then show ?thesis by (simp add: Let_def product_handover_has_a_real_public_context_segment)
next
  case (Service_Maintenance maintenance)
  have public: "source_segment (actual_product_calls s)
     (exact_calls (exact_step permitted verified maintainers registered verified_ack maintenance (read_authority (regulated_read_world s))))"
    unfolding source_segment_def exact_read_calls_are_the_product_calls[symmetric]
    by (rule exact_step_has_a_public_segment)
  then show ?thesis using Service_Maintenance
    by (simp add: Let_def service_reads_preserve_the_actual_source_for_any_selected_read_state split: if_splits)
qed simp_all

lemma every_scheduled_service_action_has_a_public_source_segment:
  "source_segment (actual_product_calls s)
    (actual_product_calls (fst (schedule_service_step directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action s)))"
  by (cases action)
    (simp_all del: live_product_service_step.simps add: schedule_service_step_def Let_def
      every_service_action_has_a_public_source_segment split: if_splits)

end

end
