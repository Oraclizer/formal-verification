theory Reference_Central_Trace
  imports Reference_Authority_Trace "OIP_Product.Promotion_Call_Ids"
begin

record 'token reference_service_input =
  reference_connection :: authority_connection
  reference_service_action :: "'token retained_service_action"
  reference_supplied_grants :: "reference_authority_inputs option"

fun run_reference_word where
  "run_reference_word execute [] initial = initial"
| "run_reference_word execute (action # rest) initial =
    run_reference_word execute rest (fst (execute action initial))"

context source_attestation
begin

definition reference_service_contract where
  "reference_service_contract registered genesis snapshot \<longleftrightarrow>
     reference_grants_fit registered (reference_product snapshot) (reference_inputs snapshot) \<and>
     retained_source_replay_valid (reference_product snapshot) \<and>
     retained_call_ids_exact (reference_product snapshot) \<and>
     retained_genesis (retained_source (reference_product snapshot)) = genesis"

lemma an_actual_reference_service_step_preserves_its_authority_contract:
  assumes initial: "reference_service_contract registered genesis snapshot"
    and step: "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
      authenticated connection action supplied snapshot = (after, reply)"
  shows "reference_service_contract registered genesis after"
proof -
  have replay: "retained_source_replay_valid (reference_product snapshot)"
    and grants: "reference_grants_fit registered (reference_product snapshot) (reference_inputs snapshot)"
    and ids: "retained_call_ids_exact (reference_product snapshot)"
    using initial by (auto simp: reference_service_contract_def)
  have preserved: "retained_source_replay_valid (reference_product after) \<and>
    retained_genesis (retained_source (reference_product after)) =
      retained_genesis (retained_source (reference_product snapshot)) \<and>
    reference_grants_fit registered (reference_product after) (reference_inputs after)"
    by (rule a_reference_step_keeps_replay_and_genesis_under_current_grants[OF replay grants step])
  have "retained_call_ids_exact (reference_product after)"
  proof (cases reply)
    case None
    have "after = snapshot"
      by (rule reference_service_refusal_leaves_the_exact_snapshot[OF step[unfolded None]])
    then show ?thesis using ids by simp
  next
    case (Some response)
    let ?selected = "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted
      (reference_permitted_at (reference_inputs snapshot)) verified maintainers registered verified_ack
      connection action (reference_product snapshot)"
    have service: "?selected = (reference_product after, response)"
      by (rule a_reference_step_uses_the_actual_service_with_the_retained_grants[OF step[unfolded Some]])
    have "retained_call_ids_exact (fst ?selected)"
      by (rule the_actual_scheduled_step_preserves_retained_call_id_uniqueness[OF ids])
    then show ?thesis using service by simp
  qed
  then show ?thesis using initial preserved by (simp add: reference_service_contract_def)
qed

lemma an_actual_reference_word_preserves_its_authority_contract:
  fixes execute :: "'token reference_service_input \<Rightarrow> reference_authority_snapshot
     \<Rightarrow> reference_authority_snapshot \<times> scheduled_service_reply option"
    and directory policy read_policy authenticate verify verify_read endorse approve
    and legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack authenticated
  defines "execute \<equiv> \<lambda>entry snapshot.
    service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
      authenticated (reference_connection entry) (reference_service_action entry)
      (reference_supplied_grants entry) snapshot"
  assumes start: "reference_service_contract registered genesis initial"
  shows "reference_service_contract registered genesis (run_reference_word execute word initial)"
  using start
proof (induction word arbitrary: initial)
  case Nil
  then show ?case by simp
next
  case (Cons entry rest)
  note tail = Cons(1)
  obtain after reply where actual: "execute entry initial = (after, reply)" by (cases "execute entry initial")
  have contract: "reference_service_contract registered genesis after"
    by (rule an_actual_reference_service_step_preserves_its_authority_contract[OF Cons.prems actual[unfolded execute_def]])
  show ?case using tail[OF contract] actual by simp
qed

theorem actual_reference_history_consumes_the_public_replay_and_single_origin_settlement:
  assumes contract: "reference_service_contract registered (initial_finality_core balances regulatory contexts) snapshot"
  shows "retained_core (retained_source (reference_product snapshot)) =
      run_finality (call_operations (retained_log (retained_source (reference_product snapshot)))
        (initial_finality_core balances regulatory contexts)) (initial_finality_core balances regulatory contexts)"
    "distinct (authority_execution_ids (retained_log (retained_source (reference_product snapshot))))"
    "distinct (map binding_key (credit_history (received_messages
      (machine_state (core_parent (retained_core (retained_source (reference_product snapshot))))))))"
    "distinct (map binding_key (returned_bindings
      (machine_journal (core_parent (retained_core (retained_source (reference_product snapshot)))))))"
    "binding_key ` set (credit_history (received_messages
      (machine_state (core_parent (retained_core (retained_source (reference_product snapshot))))))) \<inter>
      binding_key ` returned_source_bindings
        (machine_state (core_parent (retained_core (retained_source (reference_product snapshot))))) = {}"
proof -
  let ?records = "retained_source (reference_product snapshot)"
  let ?genesis = "initial_finality_core balances regulatory contexts"
  let ?machine = "core_parent (retained_core ?records)"
  let ?state = "machine_state ?machine"
  have valid: "retained_source_replay_valid (reference_product snapshot)"
    and gen: "retained_genesis ?records = ?genesis"
    and ids: "retained_call_ids_exact (reference_product snapshot)"
    using contract by (auto simp: reference_service_contract_def)
  have core: "retained_core ?records = finality_calls.replay_call_authority (retained_log ?records) ?genesis"
    using valid gen by (simp add: retained_source_replay_valid_def reopen_retained_source_def
      finality_calls.authority_replay_contract_def)
  show replay: "retained_core ?records = run_finality (call_operations (retained_log ?records) ?genesis) ?genesis"
    using core unfolding call_replay_is_actual_finality_run .
  show "distinct (authority_execution_ids (retained_log ?records))"
    using ids by (simp add: retained_call_ids_exact_def authority_cache_contract_def reopen_retained_source_def)
  have ledger: "reservation_contract balances ?machine"
    unfolding replay by (rule finality_supplies_actual_reservation_contract)
  show "distinct (map binding_key (credit_history (received_messages ?state)))"
    "distinct (map binding_key (returned_bindings (machine_journal ?machine)))"
    "binding_key ` set (credit_history (received_messages ?state)) \<inter>
       binding_key ` returned_source_bindings ?state = {}"
    by (rule a_public_reservation_contract_fences_every_duplicate_original_effect(2-4)[OF ledger])+
qed

theorem a_word_of_actual_reference_services_settles_each_origin_at_most_once:
  fixes execute :: "'token reference_service_input \<Rightarrow> reference_authority_snapshot
     \<Rightarrow> reference_authority_snapshot \<times> scheduled_service_reply option"
    and directory policy read_policy authenticate verify verify_read endorse approve
    and legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack authenticated
  defines "execute \<equiv> \<lambda>entry snapshot.
    service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
      authenticated (reference_connection entry) (reference_service_action entry)
      (reference_supplied_grants entry) snapshot"
  assumes initial: "reference_service_contract registered (initial_finality_core balances regulatory contexts) initial"
  shows "let snapshot = run_reference_word execute word initial;
       machine = core_parent (retained_core (retained_source (reference_product snapshot)));
       state = machine_state machine
    in distinct (map binding_key (credit_history (received_messages state))) \<and>
       distinct (map binding_key (returned_bindings (machine_journal machine))) \<and>
       binding_key ` set (credit_history (received_messages state)) \<inter>
         binding_key ` returned_source_bindings state = {}"
proof -
  have final: "reference_service_contract registered (initial_finality_core balances regulatory contexts)
      (run_reference_word execute word initial)"
    unfolding execute_def
    by (rule an_actual_reference_word_preserves_its_authority_contract[OF initial])
  show ?thesis using actual_reference_history_consumes_the_public_replay_and_single_origin_settlement(3-5)[OF final]
    by (simp add: Let_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.an_actual_reference_service_step_preserves_its_authority_contract
      source_attestation.an_actual_reference_word_preserves_its_authority_contract
      source_attestation.actual_reference_history_consumes_the_public_replay_and_single_origin_settlement
      source_attestation.a_word_of_actual_reference_services_settles_each_origin_at_most_once})
  then () else error "Unexpected oracle in reference central authority consumption"
\<close>

end
