theory Outcome_Recovery
  imports Call_Outcomes
begin

definition authoritative_outcome_snapshot where
  "authoritative_outcome_snapshot s = (product_durable_snapshot (outcome_source s),
    outcome_entries s, outcome_completed s)"

context source_attestation
begin

definition crash_outcome_world where
  "crash_outcome_world s = s\<lparr>outcome_source := product_crash (outcome_source s)\<rparr>"

definition recover_outcome_world where
  "recover_outcome_world candidate s =
    (if candidate = Some (authoritative_outcome_snapshot s)
     then s\<lparr>outcome_source := product_restart (Some (product_durable_snapshot (outcome_source s))) (outcome_source s)\<rparr>
     else s)"

lemma crash_retains_authoritative_outcome_snapshot:
  "authoritative_outcome_snapshot (crash_outcome_world s) = authoritative_outcome_snapshot s"
  by (simp add: authoritative_outcome_snapshot_def crash_outcome_world_def product_crash_keeps_snapshot)

lemma divergent_outcome_snapshot_cannot_be_installed:
  "candidate \<noteq> Some (authoritative_outcome_snapshot s) \<Longrightarrow> recover_outcome_world candidate s = s"
  by (simp add: recover_outcome_world_def)

lemma outcome_snapshot_equality_preserves_result_observation:
  assumes "authoritative_outcome_snapshot s = authoritative_outcome_snapshot t"
  shows "read_authoritative_result verified who call_id payload s = read_authoritative_result verified who call_id payload t"
proof -
  have entries: "outcome_entries s = outcome_entries t"
    using assms by (simp add: authoritative_outcome_snapshot_def)
  have durable: "product_durable (outcome_source s) = product_durable (outcome_source t)"
    using assms by (simp add: authoritative_outcome_snapshot_def product_durable_snapshot_def)
  have core: "call_authority_state (product_calls (outcome_source s)) = call_authority_state (product_calls (outcome_source t))"
    using assms by (simp add: authoritative_outcome_snapshot_def product_durable_snapshot_def)
  have access: "result_access_bound verified who call_id payload s = result_access_bound verified who call_id payload t"
    by (simp add: result_access_bound_def product_identity_bound_def current_product_cut_def durable)
  have ready: "result_completion_ready recorded s = result_completion_ready recorded t" for recorded
    by (cases "final_effect_key (envelope_command (payload_envelope (result_payload recorded))) (result_outcome recorded)")
      (simp_all add: result_completion_ready_def Let_def core)
  show ?thesis by (cases "outcome_entries t call_id")
    (simp_all add: read_authoritative_result_def access entries ready)
qed

theorem exact_recovery_preserves_reply_and_execution_history:
  assumes "call_connection (product_calls (outcome_source s)) = Authority_Connected"
  shows "let restored = recover_outcome_world (Some (authoritative_outcome_snapshot s)) (crash_outcome_world s)
    in read_authoritative_result verified who call_id payload restored = read_authoritative_result verified who call_id payload s \<and>
       call_authority_log (product_calls (outcome_source restored)) = call_authority_log (product_calls (outcome_source s))"
proof -
  let ?restored = "recover_outcome_world (Some (authoritative_outcome_snapshot s)) (crash_outcome_world s)"
  have unchanged: "authoritative_outcome_snapshot ?restored = authoritative_outcome_snapshot s"
    using product_restart_from_durable_state[OF assms]
    by (simp add: recover_outcome_world_def crash_retains_authoritative_outcome_snapshot
        authoritative_outcome_snapshot_def crash_outcome_world_def product_crash_keeps_snapshot)
  have reply: "read_authoritative_result verified who call_id payload ?restored = read_authoritative_result verified who call_id payload s"
    by (rule outcome_snapshot_equality_preserves_result_observation[OF unchanged])
  have journal: "call_authority_log (product_calls (outcome_source ?restored)) = call_authority_log (product_calls (outcome_source s))"
    using arg_cong[OF unchanged, where f="\<lambda>snapshot. fst (snd (snd (snd (fst snapshot))))"]
    by (simp add: authoritative_outcome_snapshot_def product_durable_snapshot_def)
  show ?thesis using reply journal by (simp add: Let_def)
qed

end

end
