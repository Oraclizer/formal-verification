theory Read_Cuts
  imports "OIP_Product_Base.Exact_Source_Safety"
begin

section \<open>Current authority and exact historical prefixes\<close>

definition observed_product_source where
  "observed_product_source s = outcome_source (origin_outcomes (settlement_primary s))"

definition observed_product_cut where
  "observed_product_cut s = current_product_cut (observed_product_source s)"

definition authoritative_read_core where
  "authoritative_read_core s = call_authority_state (exact_calls s)"

lemma observed_revision_is_the_public_log_length:
  "cut_revision (observed_product_cut s) = length (call_authority_log (exact_calls s))"
  by (simp add: observed_product_cut_def observed_product_source_def current_product_cut_def exact_calls_def outcome_calls_def)

context source_attestation
begin

definition authority_prefix_core where
  "authority_prefix_core revision s = finality_calls.replay_call_authority
    (take revision (call_authority_log (exact_calls s))) (call_genesis (exact_calls s))"

definition authority_prefix_snapshot where
  "authority_prefix_snapshot revision s =
    (if revision \<le> cut_revision (observed_product_cut s)
     then Some (capture_snapshot (authority_prefix_core revision s)) else None)"

lemma authority_prefix_snapshot_has_exact_requested_history:
  "authority_prefix_snapshot revision s = Some snapshot \<Longrightarrow>
    revision \<le> length (call_authority_log (exact_calls s)) \<and>
    snapshot = capture_snapshot (finality_calls.replay_call_authority
       (take revision (call_authority_log (exact_calls s))) (call_genesis (exact_calls s)))"
  by (auto simp: authority_prefix_snapshot_def authority_prefix_core_def observed_revision_is_the_public_log_length
      split: if_splits)

lemma generated_exact_source_supplies_authoritative_replay:
  "finality_calls.authority_replay_contract (exact_calls
    (run_exact_product permitted verified maintainers registered verified_ack actions
      (initial_exact_product balances regulatory contexts durable target)))"
proof -
  let ?core = "initial_finality_core balances regulatory contexts"
  let ?start = "initial_exact_product balances regulatory contexts durable target"
  let ?current = "run_exact_product permitted verified maintainers registered verified_ack actions ?start"
  have initial: "exact_calls ?start = initial_call_machine ?core"
    by (simp add: exact_calls_def outcome_calls_def initial_exact_product_def initial_settlement_world_def
        initial_origin_world_def initial_outcome_world_def initial_lock_world_def)
  obtain word where trace: "exact_calls ?current = finality_calls.run_calls word (exact_calls ?start)"
    using exact_product_trace_is_a_public_word[of permitted verified maintainers registered verified_ack actions ?start]
    by blast
  have replay: "finality_calls.authority_replay_contract (finality_calls.run_calls word (initial_call_machine ?core))"
    using finality_calls.generated_call_contracts[of word ?core] by blast
  show ?thesis unfolding trace initial by (rule replay)
qed

lemma full_authority_prefix_equals_the_current_core:
  assumes "finality_calls.authority_replay_contract (exact_calls s)"
  shows "authority_prefix_core (cut_revision (observed_product_cut s)) s = authoritative_read_core s"
  using assms by (simp add: authority_prefix_core_def authoritative_read_core_def
      observed_revision_is_the_public_log_length finality_calls.authority_replay_contract_def)

theorem generated_current_cut_has_the_actual_authority_snapshot:
  "let current = run_exact_product permitted verified maintainers registered verified_ack actions
          (initial_exact_product balances regulatory contexts durable target)
    in authority_prefix_snapshot (cut_revision (observed_product_cut current)) current =
       Some (capture_snapshot (authoritative_read_core current))"
  using full_authority_prefix_equals_the_current_core[OF generated_exact_source_supplies_authoritative_replay]
  by (simp add: authority_prefix_snapshot_def Let_def)

end

end
