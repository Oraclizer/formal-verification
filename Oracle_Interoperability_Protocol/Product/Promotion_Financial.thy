theory Promotion_Financial
  imports Promotion_Trace_Retention Promotion_Resolution
begin

definition initial_promotable_product where
  "initial_promotable_product balances regulatory contexts durable target provider =
    capture_retained_product (initial_regulated_product (initial_product_reads provider
      (initial_exact_product balances regulatory contexts durable target)))"

context source_attestation
begin

lemma canonical_product_initialization_supplies_the_actual_public_genesis:
  "retained_source_replay_valid (initial_promotable_product balances regulatory contexts durable target provider)"
  "retained_genesis (retained_source (initial_promotable_product balances regulatory contexts durable target provider)) =
     initial_finality_core balances regulatory contexts"
  by (simp_all add: initial_promotable_product_def actual_product_calls_def identity_source_def regulated_read_world_def
      observed_product_source_def retained_call_source_is_the_actual_product_source capture_retained_source_def
      initial_regulated_product_def initial_governed_world_def initial_legal_world_def initial_product_reads_def
      initial_exact_product_def initial_settlement_world_def initial_origin_world_def initial_outcome_world_def
      initial_lock_world_def initial_call_machine_def finality_calls.authority_replay_contract_def Let_def)

theorem every_actual_product_word_preserves_the_public_source_reservation_contract:
  fixes execute :: "authority_connection \<Rightarrow> 'token retained_service_action \<Rightarrow> retained_product \<Rightarrow> retained_product \<times> scheduled_service_reply"
    and directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
  defines "execute \<equiv> schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack"
  shows "reservation_contract balances (core_parent (retained_core (retained_source
     (run_product_action_word execute actions (initial_promotable_product balances regulatory contexts durable target provider)))))"
proof -
  let ?initial = "initial_promotable_product balances regulatory contexts durable target provider"
  let ?current = "run_product_action_word execute actions ?initial"
  let ?genesis = "initial_finality_core balances regulatory contexts"
  let ?source = "retained_source ?current"
  have init: "retained_source_replay_valid ?initial"
    by (rule canonical_product_initialization_supplies_the_actual_public_genesis(1))
  have traced: "retained_source_replay_valid ?current \<and> retained_genesis ?source = retained_genesis (retained_source ?initial)"
    unfolding execute_def
    by (rule every_product_word_keeps_its_actual_genesis_and_authority_replay[OF init])
  have core: "retained_core ?source =
      finality_calls.replay_call_authority (retained_log ?source) ?genesis"
    using traced canonical_product_initialization_supplies_the_actual_public_genesis(2)
    by (simp add: retained_source_replay_valid_def reopen_retained_source_def finality_calls.authority_replay_contract_def)
  show ?thesis unfolding core call_replay_is_actual_finality_run
    by (rule finality_supplies_actual_reservation_contract)
qed

lemma a_public_reservation_contract_conserves_the_product_source_pool:
  assumes "reservation_contract balances m"
  shows "product_source_mass m account = int (balances account)"
  using assms
  unfolding product_source_mass_def
  by (intro source_pool_mass_is_conserved) (auto simp: reservation_contract_def)

lemma a_public_reservation_contract_fences_every_duplicate_original_effect:
  assumes contract: "reservation_contract balances machine"
  shows "distinct (map binding_key (source_effects (machine_state machine)))"
    "distinct (map binding_key (credit_history (received_messages (machine_state machine))))"
    "distinct (map binding_key (returned_bindings (machine_journal machine)))"
    "binding_key ` set (credit_history (received_messages (machine_state machine))) \<inter>
      binding_key ` returned_source_bindings (machine_state machine) = {}"
  using contract reservation_contract_keeps_settlement_keys_disjoint[OF contract]
  by (auto simp: reservation_contract_def source_history_unique_def message_source_invariant_def message_invariant_def
      return_history_agreement_def)

end

end
