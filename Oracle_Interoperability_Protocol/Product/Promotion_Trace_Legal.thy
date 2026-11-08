theory Promotion_Trace_Legal
  imports Promotion_Trace_Read
begin

lemma recording_an_issued_order_preserves_the_read_authority [simp]:
  "legal_reads (retain_issued_legal_order order s) = legal_reads s"
  by (simp add: retain_issued_legal_order_def split: if_splits)

lemma recording_a_legal_event_preserves_the_read_authority [simp]:
  "legal_reads (retain_committed_legal_event order observed s) = legal_reads s"
  by (cases "legal_action order") (simp_all add: retain_committed_legal_event_def Let_def split: if_splits)

lemma legal_metadata_retention_preserves_the_read_authority [simp]:
  "legal_reads (retain_actual_legal_result stage order call_id payload observed before after) = legal_reads after"
  unfolding retain_actual_legal_result_def
  by (simp split: option.splits if_splits prod.splits legal_stage.splits product_outcome.splits finality_reply.splits)

context source_attestation
begin

lemma legal_effect_has_a_source_segment:
  "read_source_segment (legal_reads s)
     (legal_reads (fst (run_legal_effect legal_grant order_verified permitted verified maintainers registered verified_ack
       stage entry actor expected call_id order payload s)))"
  by (simp add: run_legal_effect_def Let_def checked_execution_is_a_source_segment
      split: legal_admission.splits if_splits)

lemma legal_receipt_admission_has_a_source_segment:
  "read_source_segment (legal_reads (governed_legal s))
    (legal_reads (governed_legal (fst (submit_governed_order legal_grant order_verified permitted verified maintainers
      registered verified_ack stage entry actor expected call_id order payload s))))"
proof -
  let ?legal = "governed_legal s"
  let ?run = "run_legal_effect legal_grant order_verified permitted verified maintainers registered verified_ack
    stage entry actor expected call_id order payload ?legal"
  have forwarded: "read_source_segment (legal_reads ?legal) (legal_reads (fst ?run))"
    by (rule legal_effect_has_a_source_segment)
  show ?thesis
    using forwarded by (simp add: submit_governed_order_def Let_def split: option.splits if_splits)
qed

lemma replace_reads_projects_the_selected_reads [simp]:
  "regulated_read_world (replace_regulated_reads reads s) = reads"
  by (simp add: regulated_read_world_def replace_regulated_reads_def)

lemma spend_effect_has_a_source_segment:
  "read_source_segment (regulated_read_world s)
     (regulated_read_world (fst (run_spend_effect spend_grant spend_verified permitted verified maintainers registered verified_ack
      entry actor expected call_id payload authorization s)))"
  by (simp add: run_spend_effect_def regulated_read_world_def Let_def replace_regulated_reads_def
       checked_execution_is_a_source_segment split: if_splits)

lemma spend_receipt_admission_has_a_source_segment:
  "read_source_segment (regulated_read_world s)
     (regulated_read_world (fst (submit_governed_spend spend_grant spend_verified permitted verified maintainers registered verified_ack
      entry actor expected call_id payload authorization s)))"
proof -
  let ?run = "run_spend_effect spend_grant spend_verified permitted verified maintainers registered verified_ack
    entry actor expected call_id payload authorization s"
  have forwarded: "read_source_segment (regulated_read_world s) (regulated_read_world (fst ?run))"
    by (rule spend_effect_has_a_source_segment)
  show ?thesis
    using forwarded by (simp add: submit_governed_spend_def Let_def regulated_read_world_def split: if_splits option.splits)
qed

lemma regulated_step_has_an_actual_source_segment:
  "read_source_segment (regulated_read_world s) (regulated_read_world
    (regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers
       registered verified_ack action s))"
proof (cases action)
  case (Apply_Governed_Order stage entry actor expected call_id order payload)
  then show ?thesis by (simp add: regulated_read_world_def legal_receipt_admission_has_a_source_segment split: if_splits)
next
  case (Apply_Governed_Spend entry actor expected call_id payload authorization)
  then show ?thesis by (simp add: spend_receipt_admission_has_a_source_segment)
next
  case (Collect_Governed_Order stage entry actor call_id order payload)
  then show ?thesis by (simp del: product_read_step.simps add: product_read_step_has_a_source_segment split: if_splits)
next
  case (Collect_Governed_Spend actor call_id payload authorization)
  then show ?thesis by (simp del: product_read_step.simps add: product_read_step_has_a_source_segment split: if_splits)
next
  case (Ordinary_Product_Action request)
  then show ?thesis by (simp del: product_read_step.simps add: product_read_step_has_a_source_segment split: if_splits)
qed

end

end
