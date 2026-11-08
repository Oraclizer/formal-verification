theory Reference_Handover_Consumption
  imports Reference_Authority_Trace
begin

context source_attestation
begin

lemma the_reference_handover_uses_the_actual_owner_and_session_transition:
  assumes executed: "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
    authenticated connection (Service_Handover owner_token successor_token maintainer proposal) supplied before =
      (after, Some (Scheduled_Endpoint (Service_Handover_Result True)))"
  shows "let live = reopen_retained_product connection (reference_product before);
       updated = handover_product_owner directory policy authenticate approve owner_token successor_token
         maintainer maintainers registered proposal live
    in reference_product after = capture_retained_product updated \<and>
       handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer
         maintainers registered proposal (identity_source live)"
proof -
  let ?live = "reopen_retained_product connection (reference_product before)"
  let ?updated = "handover_product_owner directory policy authenticate approve owner_token successor_token
      maintainer maintainers registered proposal ?live"
  have actual: "reference_product after = capture_retained_product ?updated" "?updated \<noteq> ?live"
    using a_reference_step_uses_the_actual_service_with_the_retained_grants[OF executed]
    by (simp_all add: schedule_at_retained_state_def schedule_service_step_def Let_def)
  then show ?thesis by (auto simp: handover_product_owner_def Let_def split: if_splits)
qed

theorem the_actual_reference_handover_updates_owner_sessions_and_grants_at_one_epoch:
  assumes executed: "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
    authenticated connection (Service_Handover owner_token successor_token maintainer proposal) supplied before =
      (after, Some (Scheduled_Endpoint (Service_Handover_Result True)))"
  shows "product_owners (retained_authority (retained_source (reference_product after))) (transfer_asset proposal) =
      Some (transfer_successor proposal)"
    "product_sessions (retained_authority (retained_source (reference_product after))) (transfer_old_session proposal) = None"
    "product_sessions (retained_authority (retained_source (reference_product after))) (transfer_new_session proposal) =
      Some \<lparr>session_principal = transfer_successor proposal, session_epoch = transfer_epoch proposal\<rparr>"
    "reference_epoch (reference_inputs after) = transfer_epoch proposal"
    "core_parent (retained_core (retained_source (reference_product after))) =
      core_parent (retained_core (retained_source (reference_product before)))"
proof -
  let ?live = "reopen_retained_product connection (reference_product before)"
  let ?updated = "handover_product_owner directory policy authenticate approve owner_token successor_token
      maintainer maintainers registered proposal ?live"
  let ?source = "identity_source ?live"
  let ?next = "apply_owner_handover directory policy authenticate approve owner_token successor_token
      maintainer maintainers registered proposal ?source"
  have actual: "reference_product after = capture_retained_product ?updated"
    and authorized: "handover_is_authorized directory policy authenticate approve owner_token successor_token
      maintainer maintainers registered proposal ?source"
    using the_reference_handover_uses_the_actual_owner_and_session_transition[OF executed]
    by (simp_all add: Let_def)
  have source: "identity_source ?updated = ?next"
    using authorized by (simp add: handover_product_owner_def replace_identity_source_consumes_the_same_authority)
  have retained: "retained_source (reference_product after) = capture_retained_source ?next"
    by (simp add: actual retained_call_source_is_the_actual_product_source source)
  note exact = handover_atomically_changes_owner_and_sessions_without_spending[OF authorized]
  show "product_owners (retained_authority (retained_source (reference_product after))) (transfer_asset proposal) =
      Some (transfer_successor proposal)"
    using exact(1) by (simp add: retained capture_retained_source_def owner_of_product_def Let_def)
  show "product_sessions (retained_authority (retained_source (reference_product after))) (transfer_old_session proposal) = None"
    using exact(2) by (simp add: retained capture_retained_source_def Let_def)
  show "product_sessions (retained_authority (retained_source (reference_product after))) (transfer_new_session proposal) =
      Some \<lparr>session_principal = transfer_successor proposal, session_epoch = transfer_epoch proposal\<rparr>"
    using exact(3) by (simp add: retained capture_retained_source_def Let_def)
  show "reference_epoch (reference_inputs after) = transfer_epoch proposal"
    using reference_service_success_preserves_epoch_and_grant_binding[OF executed] exact(4)
    by (simp add: reference_grants_fit_def reference_records_epoch_def retained capture_retained_source_def
        current_product_cut_def Let_def)
  show "core_parent (retained_core (retained_source (reference_product after))) =
      core_parent (retained_core (retained_source (reference_product before)))"
    using installing_contexts_keeps_the_entire_reservation_machine authorized
    by (simp add: retained capture_retained_source_def apply_owner_handover_def product_apply_public_def
        recovery_projection_supplies_the_exact_source reopen_retained_source_def Let_def)
qed

lemma an_old_epoch_cannot_use_the_new_reference_owner_session:
  assumes "cut_authority_epoch (envelope_cut (payload_envelope payload)) \<noteq>
    cut_authority_epoch (current_product_cut (identity_source (reopen_retained_product connection (reference_product snapshot))))"
  shows "\<not> endpoint_call_allowed directory policy authenticate verify token proof target operation actor call_id payload
      (identity_source (reopen_retained_product connection (reference_product snapshot)))"
  by (rule an_older_signed_request_cannot_use_a_reopened_session[OF assms])

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.the_reference_handover_uses_the_actual_owner_and_session_transition
      source_attestation.the_actual_reference_handover_updates_owner_sessions_and_grants_at_one_epoch
      source_attestation.an_old_epoch_cannot_use_the_new_reference_owner_session})
  then () else error "Unexpected oracle in actual reference handover consumption"
\<close>

end
