theory Exact_Source_Safety
  imports Exact_Source_Trace
begin

definition initial_exact_product where
  "initial_exact_product balances regulatory contexts durable target = initial_settlement_world target
    (initial_origin_world (initial_lock_world balances regulatory contexts durable))"

definition exact_parent where
  "exact_parent s = core_parent (call_authority_state (exact_calls s))"

context source_attestation
begin

lemma initialized_exact_execution_has_public_reservation_contract:
  "reservation_contract balances (exact_parent
    (run_exact_product permitted verified maintainers registered verified_ack actions
       (initial_exact_product balances regulatory contexts durable target)))"
proof -
  let ?core = "initial_finality_core balances regulatory contexts"
  let ?start = "initial_exact_product balances regulatory contexts durable target"
  let ?end = "run_exact_product permitted verified maintainers registered verified_ack actions ?start"
  have initial: "exact_calls ?start = initial_call_machine ?core"
    by (simp add: exact_calls_def outcome_calls_def initial_exact_product_def initial_settlement_world_def
        initial_origin_world_def initial_outcome_world_def initial_lock_world_def)
  obtain word where lift: "exact_calls ?end = finality_calls.run_calls word (exact_calls ?start)"
    using exact_product_trace_is_a_public_word[of permitted verified maintainers registered verified_ack actions ?start] by blast
  have word: "exact_calls ?end = finality_calls.run_calls word (initial_call_machine ?core)"
    using lift unfolding initial .
  let ?run = "finality_calls.run_calls word (initial_call_machine ?core)"
  have actual: "call_authority_state ?run = run_finality (call_operations (call_authority_log ?run) ?core) ?core"
    by (rule generated_calls_have_actual_finality_source)
  show ?thesis unfolding exact_parent_def word actual
    by (rule finality_supplies_actual_reservation_contract)
qed

lemma reservation_contract_keeps_settlement_keys_disjoint:
  assumes contract: "reservation_contract balances m"
  shows "binding_key ` set (credit_history (received_messages (machine_state m))) \<inter>
         binding_key ` returned_source_bindings (machine_state m) = {}"
proof -
  let ?s = "machine_state m"
  have msg: "message_invariant (received_messages ?s)"
    using contract unfolding reservation_contract_def message_source_invariant_def by blast
  have records: "settlement_records_consistent ?s"
    using contract unfolding reservation_contract_def by blast
  have disjoint: "set (credit_history (received_messages ?s)) \<inter> returned_source_bindings ?s = {}"
    by (rule completed_credit_and_returned_are_disjoint[OF records msg])
  have credit_origin: "set (credit_history (received_messages ?s)) \<subseteq> set (source_effects ?s)"
    using contract unfolding reservation_contract_def message_source_invariant_def credited_source_origin_def by blast
  have return_origin: "returned_source_bindings ?s \<subseteq> set (source_effects ?s)"
    by (simp add: returned_source_bindings_def)
  have unique: "inj_on binding_key (set (source_effects ?s))"
    using contract unfolding reservation_contract_def source_history_unique_def distinct_map by blast
  show ?thesis
  proof (rule equals0I)
    fix key
    assume both: "key \<in> binding_key ` set (credit_history (received_messages ?s)) \<inter>
      binding_key ` returned_source_bindings ?s"
    from IntD1[OF both] obtain credit where credit_key: "key = binding_key credit"
      and credit: "credit \<in> set (credit_history (received_messages ?s))" by (rule imageE)
    from IntD2[OF both] obtain refund where refund_key: "key = binding_key refund"
      and refund: "refund \<in> returned_source_bindings ?s" by (rule imageE)
    have credit_debit: "credit \<in> set (source_effects ?s)" by (rule subsetD[OF credit_origin credit])
    have refund_debit: "refund \<in> set (source_effects ?s)" by (rule subsetD[OF return_origin refund])
    have same_key: "binding_key credit = binding_key refund" using credit_key refund_key by simp
    have same_binding: "credit = refund" by (rule inj_onD[OF unique same_key credit_debit refund_debit])
    have "credit \<in> set (credit_history (received_messages ?s)) \<inter> returned_source_bindings ?s"
      using credit refund same_binding by simp
    with disjoint show False by simp
  qed
qed

theorem every_exact_product_trace_settles_each_origin_at_most_once:
  "let m = exact_parent (run_exact_product permitted verified maintainers registered verified_ack actions
       (initial_exact_product balances regulatory contexts durable target)); s = machine_state m
   in distinct (map binding_key (source_effects s)) \<and>
      distinct (map binding_key (credit_history (received_messages s))) \<and>
      distinct (map binding_key (returned_bindings (machine_journal m))) \<and>
      binding_key ` set (credit_history (received_messages s)) \<inter> binding_key ` returned_source_bindings s = {}"
proof -
  let ?m = "exact_parent (run_exact_product permitted verified maintainers registered verified_ack actions
      (initial_exact_product balances regulatory contexts durable target))"
  have contract: "reservation_contract balances ?m" by (rule initialized_exact_execution_has_public_reservation_contract)
  have debit: "distinct (map binding_key (source_effects (machine_state ?m)))"
    using contract unfolding reservation_contract_def source_history_unique_def by blast
  have credit: "distinct (map binding_key (credit_history (received_messages (machine_state ?m))))"
    using contract unfolding reservation_contract_def message_source_invariant_def message_invariant_def by blast
  have refund: "distinct (map binding_key (returned_bindings (machine_journal ?m)))"
    using contract unfolding reservation_contract_def return_history_agreement_def by blast
  show ?thesis using debit credit refund reservation_contract_keeps_settlement_keys_disjoint[OF contract]
    by (simp add: Let_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    source_attestation.every_exact_product_trace_settles_each_origin_at_most_once
    source_attestation.every_product_continuation_keeps_the_same_primary_decision
    source_attestation.conflicting_origin_binding_cannot_change_public_state
    source_attestation.authoritative_call_retry_does_not_repeat_effect
    source_attestation.exact_recovery_preserves_reply_and_execution_history
    completed_result_has_a_committed_exact_binding
    retry_keeps_the_exact_publication_under_the_same_key
    wrong_ack_cannot_complete_a_secondary_job})
  then () else error "Unexpected oracle in exact product outcomes"
\<close>

end
