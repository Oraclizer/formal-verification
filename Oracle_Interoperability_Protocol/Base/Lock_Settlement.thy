theory Lock_Settlement
  imports Lock_Finality
begin

section \<open>Pending source effects have only evidence-based exits\<close>

context source_attestation
begin

lemma actual_cancel_cannot_release_a_pending_source:
  assumes "phase_at (machine_state (core_parent s)) (binding_key (request_binding r)) = Some Source_Pending"
  shows "let result = invoke_protocol endpoint (core_epoch s) index (Cancel_Intent r g versions) s
    in snd result = Protocol_Response Request_Rejected \<and>
      machine_state (core_parent (fst result)) = machine_state (core_parent s)"
  using assms by (simp add: Let_def invoke_protocol_def lift_protocol_result_def cancel_before_dispatch_def record_observation_def)

lemma actual_fence_cannot_release_a_debited_source:
  assumes "source_was_debited (machine_state (core_parent s)) (binding_key (request_binding r))"
  shows "let result = invoke_protocol endpoint (core_epoch s) index (Fence_Intent r g versions) s
    in snd result = Protocol_Response Request_Rejected \<and>
      machine_state (core_parent (fst result)) = machine_state (core_parent s)"
  using assms by (simp add: Let_def invoke_protocol_def lift_protocol_result_def fence_unexecuted_source_def record_observation_def)

lemma actual_source_retry_cannot_debit_again:
  assumes "source_was_debited (machine_state (core_parent s)) (binding_key (request_binding r))"
  shows "machine_state (core_parent (fst (invoke_protocol endpoint (core_epoch s) index (Source_Intent r g versions) s))) =
    machine_state (core_parent s)"
  using source_retry_cannot_debit_again[OF assms, where c="current_lock_view s endpoint" and g=g and versions="vector_lookup versions"]
  by (simp add: invoke_protocol_def lift_protocol_result_def Let_def)

lemma actual_reassignment_preserves_pending_and_source_evidence:
  "let result = invoke_protocol endpoint (core_epoch s) index (Reassign_Intent r duration) s;
       before = machine_state (core_parent s); after = machine_state (core_parent (fst result))
    in unresolved_source_obligations after = unresolved_source_obligations before \<and>
       issued_certificates after = issued_certificates before"
proof -
  let ?old = "machine_state (core_parent s)"
  let ?new = "machine_state (fst (reassign_worker (current_lock_view s endpoint) r duration (core_parent s)))"
  have frame: "phase_at ?new key = phase_at ?old key \<and> source_effects ?new = source_effects ?old \<and>
    issued_certificates ?new = issued_certificates ?old \<and> received_messages ?new = received_messages ?old" for key
    by (rule reassignment_preserves_phase_and_evidence)
  have pending: "unresolved_source_obligations ?new = unresolved_source_obligations ?old"
    using frame by (auto simp: unresolved_source_obligations_def)
  show ?thesis
    using pending frame[of "(0,0)"] by (simp add: Let_def invoke_protocol_def lift_protocol_result_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    source_attestation.actual_cancel_cannot_release_a_pending_source
    source_attestation.actual_fence_cannot_release_a_debited_source
    source_attestation.actual_source_retry_cannot_debit_again
    source_attestation.actual_reassignment_preserves_pending_and_source_evidence})
  then () else error "Unexpected oracle in pending source proofs"
\<close>

end
