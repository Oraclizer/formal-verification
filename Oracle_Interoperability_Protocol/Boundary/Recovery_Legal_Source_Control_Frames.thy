theory Recovery_Legal_Source_Control_Frames
  imports Recovery_Checked_Source_Control_Frames
begin

lemma legal_issued_metadata_keeps_the_read_world:
  "legal_reads (retain_issued_legal_order order legal) = legal_reads legal"
  by (simp add: retain_issued_legal_order_def split: if_splits)

lemma legal_committed_metadata_keeps_the_read_world:
  fixes cut :: product_cut
  shows
  "legal_reads (retain_committed_legal_event order cut legal) = legal_reads legal"
  by (cases "legal_action order") (simp_all add: retain_committed_legal_event_def Let_def split: if_splits)

lemma legal_actual_metadata_keeps_the_read_world:
  fixes cut :: product_cut
  shows
  "legal_reads (retain_actual_legal_result stage order call_id payload cut previous after) = legal_reads after"
  by (simp add: retain_actual_legal_result_def legal_issued_metadata_keeps_the_read_world
    legal_committed_metadata_keeps_the_read_world
    split: option.splits legal_stage.splits product_outcome.splits finality_reply.splits if_splits)

context source_attestation
begin

lemma legal_effect_keeps_owner_epoch_sessions_and_local_status:
  assumes produced: "after = fst (run_legal_effect legal_grant order_verified permitted verified maintainers registered verified_ack
    stage entry actor expected call_id order payload legal)"
  shows "product_owners (product_durable (observed_product_source (read_authority (legal_reads after)))) =
      product_owners (product_durable (observed_product_source (read_authority (legal_reads legal))))"
    and "product_authority_epoch (product_durable (observed_product_source (read_authority (legal_reads after)))) =
      product_authority_epoch (product_durable (observed_product_source (read_authority (legal_reads legal))))"
    and "product_sessions (product_durable (observed_product_source (read_authority (legal_reads after)))) =
      product_sessions (product_durable (observed_product_source (read_authority (legal_reads legal))))"
    and "call_local_status (product_calls (observed_product_source (read_authority (legal_reads after)))) =
      call_local_status (product_calls (observed_product_source (read_authority (legal_reads legal))))"
  using produced
  by (simp_all add: run_legal_effect_def Let_def legal_actual_metadata_keeps_the_read_world
    checked_execution_keeps_owner_epoch_sessions_and_local_status[OF refl]
    split: legal_admission.splits if_splits)

lemma legal_submission_keeps_owner_epoch_sessions_and_local_status:
  assumes produced: "after = fst (submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
    stage entry actor expected call_id order payload governed)"
  shows "product_owners (product_durable (observed_product_source (read_authority (legal_reads (governed_legal after))))) =
      product_owners (product_durable (observed_product_source (read_authority (legal_reads (governed_legal governed)))))"
    and "product_authority_epoch (product_durable (observed_product_source (read_authority (legal_reads (governed_legal after))))) =
      product_authority_epoch (product_durable (observed_product_source (read_authority (legal_reads (governed_legal governed)))))"
    and "product_sessions (product_durable (observed_product_source (read_authority (legal_reads (governed_legal after))))) =
      product_sessions (product_durable (observed_product_source (read_authority (legal_reads (governed_legal governed)))))"
    and "call_local_status (product_calls (observed_product_source (read_authority (legal_reads (governed_legal after))))) =
      call_local_status (product_calls (observed_product_source (read_authority (legal_reads (governed_legal governed)))))"
  using produced
  by (simp_all add: submit_governed_order_def Let_def legal_effect_keeps_owner_epoch_sessions_and_local_status[OF refl]
    split: option.splits if_splits)

lemma legal_full_execute_keeps_source_controls:
  assumes produced: "result = durable_execute directory policy authenticate verify endorse route token proof target
    (Apply_Governed_Order stage entry actor expected call_id order payload) authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s"
  shows "product_owners (product_durable (outcome_source (current_product_outcomes (fst result)))) =
      product_owners (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_authority_epoch (product_durable (outcome_source (current_product_outcomes (fst result)))) =
      product_authority_epoch (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_sessions (product_durable (outcome_source (current_product_outcomes (fst result)))) =
      product_sessions (product_durable (outcome_source (current_product_outcomes s)))"
    and "call_local_status (product_calls (outcome_source (current_product_outcomes (fst result)))) =
      call_local_status (product_calls (outcome_source (current_product_outcomes s)))"
proof -
  have classified: "external_call_claim (Apply_Governed_Order stage entry actor expected call_id order payload) =
      Some ((case stage of Legal_Source_Emission \<Rightarrow> Emit_Legal_Order
        | Legal_Receiving_Commit \<Rightarrow> Receive_Legal_Order), actor, call_id, payload)"
    by (cases stage) simp_all
  show "product_owners (product_durable (outcome_source (current_product_outcomes (fst result)))) =
      product_owners (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_authority_epoch (product_durable (outcome_source (current_product_outcomes (fst result)))) =
      product_authority_epoch (product_durable (outcome_source (current_product_outcomes s)))"
    and "product_sessions (product_durable (outcome_source (current_product_outcomes (fst result)))) =
      product_sessions (product_durable (outcome_source (current_product_outcomes s)))"
    and "call_local_status (product_calls (outcome_source (current_product_outcomes (fst result)))) =
      call_local_status (product_calls (outcome_source (current_product_outcomes s)))"
    by (simp_all add: produced durable_execute_def classified Let_def current_product_outcomes_def
      checked_legal_outcome_source_is_the_observed_source legal_submission_keeps_owner_epoch_sessions_and_local_status[OF refl]
      split: if_splits)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms legal_issued_metadata_keeps_the_read_world
      legal_committed_metadata_keeps_the_read_world legal_actual_metadata_keeps_the_read_world
      source_attestation.legal_effect_keeps_owner_epoch_sessions_and_local_status
      source_attestation.legal_submission_keeps_owner_epoch_sessions_and_local_status
      source_attestation.legal_full_execute_keeps_source_controls})
  then () else error "Unexpected oracle in legal actual Execute control frames"
\<close>

end
