theory EAB_Recovery_Replay
  imports EAB_Primary_Repair Evidence_Atomic_Binding.Source_Observation_Projection
begin

context source_attestation
begin

definition replayed_receipt_repair ::
  "'d routing_grants \<Rightarrow> nat set \<Rightarrow> eab_primary_authority \<Rightarrow> eab_primary_receipt \<Rightarrow>
    (sourced_observation_state, sourced_request, sourced_reply, sourced_environment) durable_call_machine \<Rightarrow>
    (sourced_observation_state, sourced_request, sourced_reply, sourced_environment) recovery_candidate \<Rightarrow>
    ('d recovery_state, 'd repair_action, 'd repair_result) step_rel"
where
  "replayed_receipt_repair grants governance authority receipt source candidate s action result t \<longleftrightarrow>
    (if map_option (\<lambda>state. coupled_core (observation_source state))
          (sourced_calls.checked_current_replay source candidate) = Some (terminal_authority authority)
     then receipt_repair_step grants governance authority receipt s action result t
     else replica_repair action \<and> result = transition_result.Operational_Failure Evidence_Unavailable \<and> t = s)"

lemma shortened_source_journal_cannot_complete_a_replica_install:
  assumes "length (candidate_entries candidate) < length (call_authority_log source)"
  shows "\<not> replayed_receipt_repair grants governance authority receipt source candidate s action
    (transition_result.Accepted (Installed job domain sequence)) t"
  using sourced_calls.shortened_journal_is_rejected[OF assms]
  by (simp add: replayed_receipt_repair_def)

lemma mismatched_live_authority_blocks_replayed_replica_install:
  assumes "sourced_calls.checked_current_replay source candidate = Some restored"
    "terminal_authority authority \<noteq> coupled_core (observation_source restored)"
    "replica_repair action"
  shows "replayed_receipt_repair grants governance authority receipt source candidate s action result t
    \<longleftrightarrow> result = transition_result.Operational_Failure Evidence_Unavailable \<and> t = s"
  using assms by (simp add: replayed_receipt_repair_def)

theorem checked_replay_recovers_the_live_receipt_and_source_consumer:
  assumes source: "sourced_calls.authority_replay_contract source"
    and restored: "sourced_calls.checked_current_replay source candidate = Some restored"
    and slot_source: "terminal_authority authority = coupled_core (observation_source (call_authority_state source))"
  shows "replayed_receipt_repair grants governance authority receipt source candidate s action reply t =
      receipt_repair_step grants governance authority receipt s action reply t \<and>
    source_observation_alpha restored = source_observation_alpha (call_authority_state source) \<and>
    execute_sourced_request request restored = execute_sourced_request request (call_authority_state source)"
proof -
  have exact: "restored = call_authority_state source"
    using sourced_calls.valid_current_replay_is_the_actual_source_state[OF source restored] .
  have authority: "coupled_core (observation_source restored) = terminal_authority authority"
    using slot_source exact by simp
  show ?thesis
    using exact_sourced_recovery_preserves_source_and_current_consumers[OF source restored, of request] restored authority
    by (simp add: replayed_receipt_repair_def)
qed

end

end
