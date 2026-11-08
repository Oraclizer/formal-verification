theory Lock_Release
  imports Lock_Settlement
begin

context source_attestation
begin

lemma actual_fence_requires_source_dispatch:
  assumes "phase_at (machine_state (core_parent s)) (binding_key (request_binding r)) = Some Reservation_Held"
  shows "let result = invoke_protocol endpoint (core_epoch s) index (Fence_Intent r g versions) s
    in snd result = Protocol_Response Request_Rejected \<and>
       machine_state (core_parent (fst result)) = machine_state (core_parent s)"
  using assms by (simp add: Let_def invoke_protocol_def lift_protocol_result_def fence_unexecuted_source_def record_observation_def)

lemma actual_destination_credit_does_not_release_the_lock:
  "let result = invoke_protocol endpoint (core_epoch s) index (Deliver_Intent route r) s;
       before = machine_state (core_parent s); after = machine_state (core_parent (fst result))
    in reservation_at after = reservation_at before \<and> asset_owner after = asset_owner before"
  by (auto simp: Let_def invoke_protocol_def reject_protocol_intent_def lift_protocol_result_def
      deliver_reserved_credit_def record_observation_def commit_reservation_event_def
      split: if_splits message_reply.splits)

lemma actual_reconcile_requires_prior_exact_credit:
  assumes "request_binding r \<notin> set (credit_history (received_messages (machine_state (core_parent s))))"
  shows "machine_state (core_parent (fst (invoke_protocol endpoint (core_epoch s) index
    (Reconcile_Intent r g versions) s))) = machine_state (core_parent s)"
  using assms by (simp add: Let_def invoke_protocol_def reject_protocol_intent_def lift_protocol_result_def
      reconcile_recorded_credit_def record_observation_def)

lemma actual_reconcile_does_not_move_funds:
  "let result = invoke_protocol endpoint (core_epoch s) index (Reconcile_Intent r g versions) s;
       before = machine_state (core_parent s); after = machine_state (core_parent (fst result))
    in source_units after = source_units before \<and> destination_units after = destination_units before"
  by (auto simp: Let_def invoke_protocol_def reject_protocol_intent_def lift_protocol_result_def
      reconcile_recorded_credit_def record_observation_def commit_reservation_event_def finish_reservation_def set_phase_def
      split: if_splits option.splits)

lemma expired_lease_cannot_refund_or_reconcile:
  assumes "reservation_at (machine_state (core_parent s)) (binding_key (request_binding r)) = Some res"
    and "reservation_deadline res \<le> reservation_clock (machine_state (core_parent s))"
  shows "machine_state (core_parent (fst (invoke_protocol endpoint (core_epoch s) index
       (Return_Intent r g versions) s))) = machine_state (core_parent s) \<and>
    machine_state (core_parent (fst (invoke_protocol endpoint (core_epoch s) index
       (Reconcile_Intent r g versions) s))) = machine_state (core_parent s)"
  using assms by (auto simp: invoke_protocol_def reject_protocol_intent_def lift_protocol_result_def
      release_to_source_def reconcile_recorded_credit_def owns_recorded_reservation_def record_observation_def
      Let_def split: if_splits)

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    source_attestation.actual_fence_requires_source_dispatch
    source_attestation.actual_destination_credit_does_not_release_the_lock
    source_attestation.actual_reconcile_requires_prior_exact_credit
    source_attestation.actual_reconcile_does_not_move_funds
    source_attestation.expired_lease_cannot_refund_or_reconcile})
  then () else error "Unexpected oracle in product lock release proofs"
\<close>

end
