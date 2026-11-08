theory Lock_Settlement_Examples
  imports "../Lock_Settlement" "Preemptive_Lock_Correctness.Reservation_Boundaries"
    "Evidence_Atomic_Binding.Finality_Scenarios"
begin

context source_attestation
begin

lemma source_debit_puts_five_into_pending:
  "source_units (machine_state (core_parent (finality_sample_source 17))) (0,17) = 5 \<and>
   sample_binding 17 \<in> unresolved_source_obligations (machine_state (core_parent (finality_sample_source 17))) \<and>
   destination_units (machine_state (core_parent (finality_sample_source 17))) (2,17,3) = 0"
  using source_acquire_dispatch_effect_activates
  by (simp add: finality_source_prefix_is_the_actual_parent_prefix unresolved_source_obligations_def
      sample_data_defs sample.protocol_definitions record_observation_def commit_reservation_event_def
      empty_message_state_def Let_def)

lemma pending_source_survives_actual_timeout:
  "let s = finality_sample_source 17;
       timed = sample.finality_step (Invoke_Protocol 0 (core_epoch s) 0 (Time_Intent 10)) s;
       rs = machine_state (core_parent timed)
   in source_units rs (0,17) = 5 \<and>
      sample_binding 17 \<in> unresolved_source_obligations rs \<and> destination_units rs (2,17,3) = 0"
  using sample.actual_finality_timeout_preserves_pending_and_balances[of 0 "finality_sample_source 17" 0 10]
    source_debit_puts_five_into_pending by (simp add: Let_def)

end

lemma pending_source_rejects_cancel_and_fence:
  "snd (sample.invoke_protocol 0 (core_epoch (finality_sample_source 17)) 0
      (Cancel_Intent (sample_request 17) 0 []) (finality_sample_source 17)) = Protocol_Response Request_Rejected"
  "snd (sample.invoke_protocol 0 (core_epoch (finality_sample_source 17)) 0
      (Fence_Intent (sample_request 17) 0 []) (finality_sample_source 17)) = Protocol_Response Request_Rejected"
proof -
  have phase: "phase_at (machine_state (core_parent (finality_sample_source 17)))
     (binding_key (request_binding (sample_request 17))) = Some Source_Pending"
    using the_same_key_binding_and_expired_pending_state
    by (simp add: finality_source_prefix_is_the_actual_parent_prefix expired_pending_sample_def
        advance_reservation_time_def commit_reservation_event_def phase_at_def sample_request_def
        sample_binding_def example_binding_def)
  have debit: "source_was_debited (machine_state (core_parent (finality_sample_source 17)))
     (binding_key (request_binding (sample_request 17)))"
    using source_acquire_dispatch_effect_activates
    by (simp add: finality_source_prefix_is_the_actual_parent_prefix source_was_debited_def sample_request_def)
  show "snd (sample.invoke_protocol 0 (core_epoch (finality_sample_source 17)) 0
      (Cancel_Intent (sample_request 17) 0 []) (finality_sample_source 17)) = Protocol_Response Request_Rejected"
    using sample.actual_cancel_cannot_release_a_pending_source[OF phase, of 0 0 0 "[]"] by (simp add: Let_def)
  show "snd (sample.invoke_protocol 0 (core_epoch (finality_sample_source 17)) 0
      (Fence_Intent (sample_request 17) 0 []) (finality_sample_source 17)) = Protocol_Response Request_Rejected"
    using sample.actual_fence_cannot_release_a_debited_source[OF debit, of 0 0 0 "[]"] by (simp add: Let_def)
qed

lemmas exact_confirmation_and_reversal_execute =
  normal_bypass_credit_uses_the_terminal_record normal_reverse_returns_the_recorded_source

lemmas missing_terminal_reference_mutation = removal_accepts_a_wrong_reference_at_a_generated_state
lemmas timeout_refund_mutation = timeout_only_refund_and_late_credit_duplicate_money

end
