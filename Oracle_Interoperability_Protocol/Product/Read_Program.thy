theory Read_Program
  imports Checked_Execution
begin

datatype product_read_action =
    Capture_Read product_principal product_session_id application_query
  | Execute_Checked lock_entry product_principal product_cut client_call_id product_call_payload
  | Read_Authority_Action exact_action

fun internal_read_authority_action where
  "internal_read_authority_action (Exact_Submit entry who call_id payload) = False"
| "internal_read_authority_action action = True"

context source_attestation
begin

fun product_read_step where
  "product_read_step read_permitted permitted verified maintainers registered verified_ack (Capture_Read who session query) s =
    capture_product_cache read_permitted who session query s"
| "product_read_step read_permitted permitted verified maintainers registered verified_ack
      (Execute_Checked entry who expected call_id payload) s =
    fst (execute_at_checked_cut permitted verified maintainers registered verified_ack
      entry who expected call_id payload s)"
| "product_read_step read_permitted permitted verified maintainers registered verified_ack (Read_Authority_Action action) s =
    (if internal_read_authority_action action then s\<lparr>read_authority := exact_step permitted verified maintainers registered verified_ack
        action (read_authority s)\<rparr> else s)"

fun run_product_reads where
  "run_product_reads read_permitted permitted verified maintainers registered verified_ack [] s = s"
| "run_product_reads read_permitted permitted verified maintainers registered verified_ack (action # rest) s =
    run_product_reads read_permitted permitted verified maintainers registered verified_ack rest
      (product_read_step read_permitted permitted verified maintainers registered verified_ack action s)"

definition read_world_valid where
  "read_world_valid s \<longleftrightarrow> authenticated_cache_invariant s \<and>
    finality_calls.authority_replay_contract (exact_calls (read_authority s))"

lemma public_word_preserves_read_replay_contract:
  "finality_calls.authority_replay_contract m \<Longrightarrow>
    finality_calls.authority_replay_contract (finality_calls.run_calls word m)"
  by (induction word arbitrary: m) (auto intro: finality_calls.authority_replay_contract_step)

lemma authority_update_keeps_read_world_valid:
  assumes "read_world_valid s"
  shows "read_world_valid (s\<lparr>read_authority := exact_step permitted verified maintainers registered verified_ack action (read_authority s)\<rparr>)"
proof -
  let ?before = "read_authority s"
  let ?after = "exact_step permitted verified maintainers registered verified_ack action ?before"
  have inv: "authenticated_cache_invariant s" and replay: "finality_calls.authority_replay_contract (exact_calls ?before)"
    using assms by (simp_all add: read_world_valid_def)
  have cache: "authenticated_cache_invariant (s\<lparr>read_authority := ?after\<rparr>)"
    by (rule authority_advance_preserves_cached_historical_values[OF inv])
  obtain word where segment: "exact_calls ?after = finality_calls.run_calls word (exact_calls ?before)"
    using exact_step_has_a_public_segment[of permitted verified maintainers registered verified_ack action ?before] by blast
  have replay_after: "finality_calls.authority_replay_contract (exact_calls ?after)"
    unfolding segment by (rule public_word_preserves_read_replay_contract[OF replay])
  show ?thesis using cache replay_after by (simp add: read_world_valid_def)
qed

lemma cache_capture_keeps_read_world_valid:
  assumes "read_world_valid s"
  shows "read_world_valid (capture_product_cache read_permitted who session query s)"
proof -
  have source: "read_authority (capture_product_cache read_permitted who session query s) = read_authority s"
    by (simp add: capture_product_cache_def Let_def split: option.splits if_splits)
  have inv: "authenticated_cache_invariant s" using assms by (simp add: read_world_valid_def)
  show ?thesis using assms cache_capture_preserves_source_values[OF inv]
    by (simp add: read_world_valid_def source)
qed

lemma product_read_step_keeps_world_valid:
  assumes valid: "read_world_valid s"
  shows "read_world_valid (product_read_step read_permitted permitted verified maintainers registered verified_ack action s)"
proof (cases action)
  case (Capture_Read who session query)
  then show ?thesis by (simp add: cache_capture_keeps_read_world_valid[OF valid])
next
  case (Execute_Checked entry who expected call_id payload)
  let ?step = "fst (execute_at_checked_cut permitted verified maintainers registered verified_ack
    entry who expected call_id payload s)"
  have "?step = s \<or> ?step = s\<lparr>read_authority := exact_step permitted verified maintainers registered verified_ack
       (Exact_Submit entry who call_id payload) (read_authority s)\<rparr>"
    by (rule checked_execution_source_is_stutter_or_actual_submit[unfolded Let_def])
  with Execute_Checked valid authority_update_keeps_read_world_valid[OF valid, of permitted verified maintainers registered verified_ack
      "Exact_Submit entry who call_id payload"]
  show ?thesis by (elim disjE) simp_all
next
  case (Read_Authority_Action internal)
  then show ?thesis using valid authority_update_keeps_read_world_valid[OF valid, of permitted verified maintainers registered verified_ack internal]
    by (simp split: if_splits)
qed

lemma product_read_trace_keeps_world_valid:
  "read_world_valid s \<Longrightarrow>
    read_world_valid (run_product_reads read_permitted permitted verified maintainers registered verified_ack actions s)"
  by (induction actions arbitrary: s) (auto intro: product_read_step_keeps_world_valid)

lemma canonical_initial_read_world_is_valid:
  "read_world_valid (initial_product_reads provider (initial_exact_product balances regulatory contexts durable target))"
proof -
  let ?start = "initial_product_reads provider (initial_exact_product balances regulatory contexts durable target)"
  have cache: "authenticated_cache_invariant ?start" by (rule initial_read_cache_is_authentic)
  have replay: "finality_calls.authority_replay_contract (exact_calls (read_authority ?start))"
    by (simp add: initial_product_reads_def exact_calls_def outcome_calls_def initial_exact_product_def
      initial_settlement_world_def initial_origin_world_def initial_outcome_world_def initial_lock_world_def
      initial_call_machine_def finality_calls.authority_replay_contract_def)
  show ?thesis unfolding read_world_valid_def by (rule conjI[OF cache replay])
qed

theorem generated_current_reads_are_the_actual_cut:
  fixes provider balances regulatory contexts durable target
  defines "start \<equiv> initial_product_reads provider (initial_exact_product balances regulatory contexts durable target)"
  assumes reply: "read_current_product read_permitted who session query expected
     (run_product_reads read_permitted permitted verified maintainers registered verified_ack actions start) =
      Current_Cut_Value reply_cut value"
  shows "let current = read_authority (run_product_reads read_permitted permitted verified maintainers registered verified_ack actions start)
    in reply_cut = expected \<and> reply_cut = observed_product_cut current \<and>
      value = stored_query query (capture_snapshot (authoritative_read_core current))"
proof -
  let ?now = "run_product_reads read_permitted permitted verified maintainers registered verified_ack actions start"
  have initial: "read_world_valid start" unfolding start_def by (rule canonical_initial_read_world_is_valid)
  have inv: "read_world_valid ?now" by (rule product_read_trace_keeps_world_valid[OF initial])
  have replay: "finality_calls.authority_replay_contract (exact_calls (read_authority ?now))"
    using inv by (simp add: read_world_valid_def)
  have authentic: "cache_has_source_value ?now entry" if "query_cache ?now query = Some entry" for entry
    using inv that by (simp add: read_world_valid_def authenticated_cache_invariant_def)
  show ?thesis unfolding Let_def
    by (rule successful_current_product_read_comes_from_the_actual_cut[OF reply replay authentic])
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    source_attestation.generated_current_reads_are_the_actual_cut
    source_attestation.successful_historical_product_read_is_the_named_prefix
    source_attestation.exact_authority_step_keeps_every_historical_prefix
    source_attestation.forwarded_execution_consumes_the_cut_it_checked
    source_attestation.changed_authority_epoch_blocks_checked_execution})
  then () else error "Unexpected oracle in current and historical read proofs"
\<close>

end
