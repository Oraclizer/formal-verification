(* SPDX-License-Identifier: BSD-3-Clause *)
theory Funding_Completion_Separation
  imports Source_Call_Realization
begin

section \<open>The Same Fresh Probe after Two Actual Source Histories\<close>

definition funding_separation_effect :: descendant_effect where
  "funding_separation_effect=realization_effect(sample_binding 17)4 3 1"

definition funding_separation_command :: client_command where
  "funding_separation_command=Client_Protocol(binding_destination(lineage_root funding_separation_effect))0
    (source_realization_intent(linked_certificate 17)funding_separation_effect)"

definition funding_separation_environment :: source_coupling_action where
  "funding_separation_environment=Coupling_Environment(binding_destination(lineage_root funding_separation_effect))
    (source_realization_context funding_separation_effect)"

definition funding_separation_word :: "source_coupling_action list" where
  "funding_separation_word=source_realization_word(linked_certificate 17)0 funding_separation_effect"

lemma funding_separation_word_shape:
  "funding_separation_word=[funding_separation_environment,Coupling_Client True funding_separation_command]"
  by (simp add: funding_separation_word_def source_realization_word_def
    funding_separation_environment_def funding_separation_command_def)

definition funding_comparison_calls :: "source_coupling_action list \<Rightarrow> sourced_durable_machine" where
  "funding_comparison_calls actions=realized.sourced_calls.run_calls(coupling_call_word 91 0 actions)
    realization_call_initial"

definition funding_probe_calls :: "source_coupling_action list \<Rightarrow> sourced_durable_machine" where
  "funding_probe_calls prefix=funding_comparison_calls(prefix@funding_separation_word)"

definition funding_probe_call_id :: "source_coupling_action list \<Rightarrow> client_call_id" where
  "funding_probe_call_id prefix=(91,Suc(2*length(prefix@[funding_separation_environment])))"

lemma funding_comparison_calls_actual_source:
  "observation_source(call_authority_state(funding_comparison_calls actions))=
    realized.run_source_coupling actions conservation_initial"
  using realized.translated_finite_word_has_the_exact_joint_source
    [OF realization_call_initial_source(2), where actions=actions]
  by (simp add: funding_comparison_calls_def realization_call_initial_source(1))

lemma funding_comparison_calls_keep_a_fresh_identifier_supply:
  "source_call_ready 91(2*length actions)(funding_comparison_calls actions)"
  using realized.translated_finite_word_has_the_exact_joint_source
    [OF realization_call_initial_source(2), where actions=actions]
  by (simp add: funding_comparison_calls_def)

theorem generated_probe_completes_the_actual_joint_reply:
  "call_completions(funding_probe_calls prefix)(funding_probe_call_id prefix)=
    Some(coupling_client_observation(snd(realized.source_coupling_step
      (Coupling_Client True funding_separation_command)
      (realized.source_realization_installed funding_separation_effect
        (realized.run_source_coupling prefix conservation_initial)))))"
  using realized.every_translated_client_cut_has_its_actual_completed_reply
    [OF realization_call_initial_source(2), where prefix="prefix@[funding_separation_environment]"
      and suffix="[]" and available=True and command=funding_separation_command]
  by (simp add: funding_probe_calls_def funding_comparison_calls_def funding_probe_call_id_def
    funding_separation_word_shape append_assoc realization_call_initial_source(1)
    realized.progress_source_run_append funding_separation_environment_def
    realized.source_realization_installed_def)

section \<open>Primitive Funding and the Unchanged Terminal and Current Inputs\<close>

lemma separation_exchange_financial:
  "financial_history_agreement sample_balances(core_parent(coupled_core realization_exchange_finished))"
  using run_realization_financial[OF realization_seed_financial realization_exchange_parent_success]
  by (simp only: realization_exchange_parent_projection)

lemma separation_exchange_frames:
  "core_records(coupled_core realization_exchange_finished)=core_records(coupled_core realization_lineage_seed)"
  "core_published(coupled_core realization_exchange_finished)=core_published(coupled_core realization_lineage_seed)"
  "core_regulatory(coupled_core realization_exchange_finished)=core_regulatory(coupled_core realization_lineage_seed)"
proof -
  have references: "\<forall>effect\<in>set realization_exchange_effects.
    record_reference(coupled_core realization_lineage_seed)0(lineage_root effect)Confirmed_Decision\<noteq>None"
    using realization_exchange_inputs(5) by (simp add: realization_exchange_effects_def realization_effect_def)
  have published: "\<forall>effect\<in>set realization_exchange_effects.
    binding_key(lineage_root effect)\<in>core_published(coupled_core realization_lineage_seed)"
    using realization_exchange_inputs(6) by (simp add: realization_exchange_effects_def realization_effect_def)
  have active: "\<forall>effect\<in>set realization_exchange_effects.
    get_reg_state(receiver_snapshot(core_regulatory(coupled_core realization_lineage_seed)))
      (binding_destination(lineage_root effect))(binding_asset(lineage_root effect))=Some ACTIVE"
    using realization_exchange_inputs(7) by (simp add: realization_exchange_effects_def realization_effect_def)
  note frame=realized.source_realization_finite_word_projection[OF references published active,
    where certificates=realization_certificates]
  show "core_records(coupled_core realization_exchange_finished)=core_records(coupled_core realization_lineage_seed)"
    "core_published(coupled_core realization_exchange_finished)=core_published(coupled_core realization_lineage_seed)"
    "core_regulatory(coupled_core realization_exchange_finished)=core_regulatory(coupled_core realization_lineage_seed)"
    using frame unfolding realization_exchange_finished_def by blast+
qed

lemma separation_source_inputs:
  assumes member: "provider\<in>{realization_lineage_seed,realization_exchange_finished}"
  shows "financial_history_agreement sample_balances(core_parent(coupled_core provider))"
    "sample_binding 17\<in>set(credit_history(received_messages(machine_state(core_parent(coupled_core provider)))))"
    "record_reference(coupled_core provider)0(sample_binding 17)Confirmed_Decision\<noteq>None"
    "binding_key(sample_binding 17)\<in>core_published(coupled_core provider)"
    "get_reg_state(receiver_snapshot(core_regulatory(coupled_core provider)))
      (binding_destination(sample_binding 17))(binding_asset(sample_binding 17))=Some ACTIVE"
proof -
  have seed_credit: "sample_binding 17\<in>set(credit_history(received_messages
    (machine_state(core_parent(coupled_core realization_lineage_seed)))))"
    using realization_exchange_inputs(1) by simp
  have seed_reference: "record_reference(coupled_core realization_lineage_seed)0(sample_binding 17)Confirmed_Decision\<noteq>None"
    and seed_published: "binding_key(sample_binding 17)\<in>core_published(coupled_core realization_lineage_seed)"
    and seed_active: "get_reg_state(receiver_snapshot(core_regulatory(coupled_core realization_lineage_seed)))
      (binding_destination(sample_binding 17))(binding_asset(sample_binding 17))=Some ACTIVE"
    using realization_exchange_inputs(5,6,7) by simp_all
  have exchange_credit: "sample_binding 17\<in>set(credit_history(received_messages
    (machine_state(core_parent(coupled_core realization_exchange_finished)))))"
    using seed_credit actual_realization_has_no_new_source_credit_or_return by auto
  show "financial_history_agreement sample_balances(core_parent(coupled_core provider))"
    using member realization_seed_financial separation_exchange_financial by auto
  show "sample_binding 17\<in>set(credit_history(received_messages(machine_state(core_parent(coupled_core provider)))))"
    using member seed_credit exchange_credit by auto
  show "record_reference(coupled_core provider)0(sample_binding 17)Confirmed_Decision\<noteq>None"
    using member seed_reference separation_exchange_frames(1) by (auto simp: record_reference_def)
  show "binding_key(sample_binding 17)\<in>core_published(coupled_core provider)"
    using member seed_published separation_exchange_frames(2) by auto
  show "get_reg_state(receiver_snapshot(core_regulatory(coupled_core provider)))
      (binding_destination(sample_binding 17))(binding_asset(sample_binding 17))=Some ACTIVE"
    using member seed_active separation_exchange_frames(3) by auto
qed

lemma separation_same_pooled_but_distinct_root_funding:
  "destination_units(machine_state(core_parent(coupled_core realization_lineage_seed)))=
    destination_units(machine_state(core_parent(coupled_core realization_exchange_finished)))"
  "funded_units(machine_state(core_parent(coupled_core realization_lineage_seed)))((0,17),(2,17,4))=5"
  "funded_units(machine_state(core_parent(coupled_core realization_exchange_finished)))((0,17),(2,17,4))=0"
proof -
  show "destination_units(machine_state(core_parent(coupled_core realization_lineage_seed)))=
      destination_units(machine_state(core_parent(coupled_core realization_exchange_finished)))"
    using actual_source_realization_preserves_erased_state_and_source_pool by auto
  show "funded_units(machine_state(core_parent(coupled_core realization_lineage_seed)))((0,17),(2,17,4))=5"
    by (rule realization_seed_funding(2))
  show "funded_units(machine_state(core_parent(coupled_core realization_exchange_finished)))((0,17),(2,17,4))=0"
    using actual_two_root_plan_activates_every_source_dispatch
    by (auto simp: realization_units_def realization_exchange_target_def sample_binding_def example_binding_def holder_account_def)
qed

lemma actual_separation_parent_probe:
  assumes member: "provider\<in>{realization_lineage_seed,realization_exchange_finished}"
  shows "snd(execute_descendant(source_realization_context funding_separation_effect)
      (source_realization_request(linked_certificate 17)funding_separation_effect)
      (lineage_root funding_separation_effect)(lineage_from funding_separation_effect)
      (lineage_to funding_separation_effect)(lineage_amount funding_separation_effect)(core_parent(coupled_core provider)))=
    (if 1\<le>funded_units(machine_state(core_parent(coupled_core provider)))((0,17),(2,17,4))
      then Descendant_Executed else Request_Rejected)"
  using actual_probe_reply_is_the_funding_threshold[OF separation_source_inputs(1,2)[OF member],
    where certificate="linked_certificate 17" and sender=4 and recipient=3 and amount=1]
  by (simp add: funding_separation_effect_def realization_effect_def source_realization_context_def
    source_realization_request_def sample_binding_def example_binding_def holder_account_def)

theorem same_probe_uses_actual_terminal_and_current_inputs:
  assumes member: "provider\<in>{realization_lineage_seed,realization_exchange_finished}"
  shows "snd(realized.source_coupling_step(Coupling_Client True funding_separation_command)
      (realized.source_realization_installed funding_separation_effect provider))=
    Coupling_Client_Reply(Protocol_Response
      (if 1\<le>funded_units(machine_state(core_parent(coupled_core provider)))((0,17),(2,17,4))
        then Descendant_Executed else Request_Rejected))"
proof -
  have reference: "record_reference(coupled_core provider)0(lineage_root funding_separation_effect)Confirmed_Decision\<noteq>None"
    and published: "binding_key(lineage_root funding_separation_effect)\<in>core_published(coupled_core provider)"
    and active: "get_reg_state(receiver_snapshot(core_regulatory(coupled_core provider)))
      (binding_destination(lineage_root funding_separation_effect))(binding_asset(lineage_root funding_separation_effect))=Some ACTIVE"
    using separation_source_inputs(3,4,5)[OF member]
    by (simp_all add: funding_separation_effect_def realization_effect_def)
  note actual=realized.source_realization_one_step_is_the_actual_parent_result[OF reference published active,
    where certificate="linked_certificate 17"]
  have reply: "snd(realized.source_coupling_step(Coupling_Client True funding_separation_command)
      (realized.source_realization_installed funding_separation_effect provider))=
    Coupling_Client_Reply(Protocol_Response(snd(execute_descendant(source_realization_context funding_separation_effect)
      (source_realization_request(linked_certificate 17)funding_separation_effect)
      (lineage_root funding_separation_effect)(lineage_from funding_separation_effect)
      (lineage_to funding_separation_effect)(lineage_amount funding_separation_effect)(core_parent(coupled_core provider)))))"
    using actual unfolding funding_separation_command_def by blast
  show ?thesis by (simp only: reply actual_separation_parent_probe[OF member])
qed

theorem actual_joint_probe_separates_the_two_source_histories:
  "snd(realized.source_coupling_step(Coupling_Client True funding_separation_command)
      (realized.source_realization_installed funding_separation_effect realization_lineage_seed))=
    Coupling_Client_Reply(Protocol_Response Descendant_Executed)"
  "snd(realized.source_coupling_step(Coupling_Client True funding_separation_command)
      (realized.source_realization_installed funding_separation_effect realization_exchange_finished))=
    Coupling_Client_Reply(Protocol_Response Request_Rejected)"
  using same_probe_uses_actual_terminal_and_current_inputs[of realization_lineage_seed]
    same_probe_uses_actual_terminal_and_current_inputs[of realization_exchange_finished]
  by (simp_all add: separation_same_pooled_but_distinct_root_funding)

theorem same_pooled_genesis_histories_produce_distinct_completed_decisions:
  "call_completions(funding_probe_calls realization_call_prefix)(funding_probe_call_id realization_call_prefix)=
    Some(Sourced_Observation(Effect_Reply(Protocol_Response Descendant_Executed)))"
  "call_completions(funding_probe_calls realization_call_actions)(funding_probe_call_id realization_call_actions)=
    Some(Sourced_Observation(Effect_Reply(Protocol_Response Request_Rejected)))"
  by (simp_all only: generated_probe_completes_the_actual_joint_reply
    realization_call_prefix_is_the_actual_lineage_seed realization_call_word_is_the_actual_exchange
    actual_joint_probe_separates_the_two_source_histories coupling_client_observation.simps)

theorem generated_prefixes_have_equal_pooled_balances_and_distinct_funding:
  "destination_units(machine_state(core_parent(coupled_core(observation_source
      (call_authority_state(funding_comparison_calls realization_call_prefix))))))=
    destination_units(machine_state(core_parent(coupled_core(observation_source
      (call_authority_state(funding_comparison_calls realization_call_actions))))))"
  "funded_units(machine_state(core_parent(coupled_core(observation_source
      (call_authority_state(funding_comparison_calls realization_call_prefix))))))((0,17),(2,17,4))=5"
  "funded_units(machine_state(core_parent(coupled_core(observation_source
      (call_authority_state(funding_comparison_calls realization_call_actions))))))((0,17),(2,17,4))=0"
  by (simp_all only: funding_comparison_calls_actual_source realization_call_prefix_is_the_actual_lineage_seed
    realization_call_word_is_the_actual_exchange separation_same_pooled_but_distinct_root_funding)

theorem pooled_balances_do_not_determine_the_actual_fresh_completed_probe:
  "\<not>(\<exists>decide. \<forall>prefix\<in>{realization_call_prefix,realization_call_actions}.
    decide(destination_units(machine_state(core_parent(coupled_core(observation_source
      (call_authority_state(funding_comparison_calls prefix)))))))=
    call_completions(funding_probe_calls prefix)(funding_probe_call_id prefix))"
  using generated_prefixes_have_equal_pooled_balances_and_distinct_funding(1)
    same_pooled_genesis_histories_produce_distinct_completed_decisions(1,2)
  by auto

lemma the_two_probe_identifiers_are_fresh_at_their_own_cuts:
  "source_call_ready 91(2*length(realization_call_prefix@[funding_separation_environment]))
    (funding_comparison_calls(realization_call_prefix@[funding_separation_environment]))"
  "source_call_ready 91(2*length(realization_call_actions@[funding_separation_environment]))
    (funding_comparison_calls(realization_call_actions@[funding_separation_environment]))"
  by (rule funding_comparison_calls_keep_a_fresh_identifier_supply)+

lemma probe_identifier_difference_records_only_the_extra_prefix:
  "funding_probe_call_id realization_call_actions=
    (91,snd(funding_probe_call_id realization_call_prefix)+8)"
  by (simp add: funding_probe_call_id_def realization_call_actions_def realization_exchange_effects_def
    source_realization_word_def algebra_simps)

section \<open>The Distinction Survives Exact Recovery and Historical Projection\<close>

definition funding_probe_runtime :: "source_coupling_action list \<Rightarrow>
  (sourced_observation_state,sourced_request,sourced_reply,sourced_environment) recovered_call_runtime" where
  "funding_probe_runtime prefix=\<lparr>recovery_source=funding_probe_calls prefix,
    recovery_replica=None,recovery_connected=True\<rparr>"

definition recovered_funding_probe_calls :: "source_coupling_action list \<Rightarrow>
  (sourced_request,sourced_environment) client_call_action list \<Rightarrow> sourced_durable_machine" where
  "recovered_funding_probe_calls prefix future=realized.sourced_history_projection.reduced.run_calls future
    (realized.sourced_history_projection.normalize_call_machine(recovery_source
      (realized.sourced_calls.dispatch_from_recovered_replica(funding_probe_call_id prefix)
        (Endpoint_Request(Execute_Current 0 funding_separation_command))
        (realized.sourced_calls.restore_current_replica(current_source_candidate(funding_probe_calls prefix))
          (funding_probe_runtime prefix)))))"

theorem each_generated_probe_has_exact_current_recovery:
  "realized.sourced_calls.checked_current_replay(funding_probe_calls prefix)
      (current_source_candidate(funding_probe_calls prefix))=Some(call_authority_state(funding_probe_calls prefix))"
  unfolding funding_probe_calls_def funding_comparison_calls_def realization_call_initial_def
  by (rule realized.sourced_calls.generated_source_supplies_recovery_without_a_truth_flag)

theorem each_recovery_keeps_the_original_generated_machine:
  "recovery_source(realized.sourced_calls.restore_current_replica
      (current_source_candidate(funding_probe_calls prefix))(funding_probe_runtime prefix))=funding_probe_calls prefix"
  "recovery_replica(realized.sourced_calls.restore_current_replica
      (current_source_candidate(funding_probe_calls prefix))(funding_probe_runtime prefix))=
    Some(call_authority_state(funding_probe_calls prefix))"
  by (simp_all add: funding_probe_runtime_def realized.sourced_calls.restore_current_replica_def
    each_generated_probe_has_exact_current_recovery)

theorem recovered_probe_has_the_original_future_completion_table:
  "call_completions(recovered_funding_probe_calls prefix future)=
    call_completions(realized.sourced_calls.run_calls future
      (realized.sourced_calls.dispatch_client_call(funding_probe_call_id prefix)
        (Endpoint_Request(Execute_Current 0 funding_separation_command))(funding_probe_calls prefix)))"
  using realized.generated_translation_transports_recovery_and_future_replies(1)
    [where namespace=91 and ?next=0 and actions="prefix@funding_separation_word"
      and balances=sample_balances and regulatory="sample_metadata ACTIVE" and contexts=conservation_contexts
      and future=future and call_id="funding_probe_call_id prefix"
      and request="Endpoint_Request(Execute_Current 0 funding_separation_command)"]
  by (simp add: recovered_funding_probe_calls_def funding_probe_runtime_def funding_probe_calls_def
    funding_comparison_calls_def realization_call_initial_def)

lemma recovered_probe_retains_an_actual_completed_reply:
  assumes completed: "call_completions(funding_probe_calls prefix)(funding_probe_call_id prefix)=Some reply"
  shows "call_completions(recovered_funding_probe_calls prefix future)(funding_probe_call_id prefix)=Some reply"
proof -
  have dispatched: "call_completions(realized.sourced_calls.dispatch_client_call(funding_probe_call_id prefix)
      (Endpoint_Request(Execute_Current 0 funding_separation_command))(funding_probe_calls prefix))
      (funding_probe_call_id prefix)=Some reply"
    using realized.sourced_completion_survives_every_step[OF completed,
      where action="Dispatch_Call(funding_probe_call_id prefix)(Endpoint_Request(Execute_Current 0 funding_separation_command))"]
    by simp
  have continued: "call_completions(realized.sourced_calls.run_calls future
      (realized.sourced_calls.dispatch_client_call(funding_probe_call_id prefix)
        (Endpoint_Request(Execute_Current 0 funding_separation_command))(funding_probe_calls prefix)))
      (funding_probe_call_id prefix)=Some reply"
    by (rule realized.sourced_completed_replies_survive_finite_continuations[OF dispatched])
  show ?thesis by (simp only: recovered_probe_has_the_original_future_completion_table continued)
qed

theorem recovery_and_projection_preserve_the_actual_funding_separation:
  "call_completions(recovered_funding_probe_calls realization_call_prefix future)
      (funding_probe_call_id realization_call_prefix)=
    Some(Sourced_Observation(Effect_Reply(Protocol_Response Descendant_Executed)))"
  "call_completions(recovered_funding_probe_calls realization_call_actions future)
      (funding_probe_call_id realization_call_actions)=
    Some(Sourced_Observation(Effect_Reply(Protocol_Response Request_Rejected)))"
  by (rule recovered_probe_retains_an_actual_completed_reply
      [OF same_pooled_genesis_histories_produce_distinct_completed_decisions(1)],
      rule recovered_probe_retains_an_actual_completed_reply
      [OF same_pooled_genesis_histories_produce_distinct_completed_decisions(2)])

text \<open>The two pre-probe states are generated from the same actual sourced
  genesis. Their pooled destination balances agree, while root 17 funds held
  by holder 4 are five in the lineage seed and zero after the constructive
  exchange. The same ordinary one-unit command installs the same current
  permission and consumes the same confirmed terminal reference. The inherited
  parent funding threshold gives different actual callbacks, and the existing
  fresh-call translation produces their durable completed replies.

  The identifiers differ because the second history contains four additional
  coupling inputs. Each identifier is fresh at its own source cut. The request,
  installed current context and amount agree; an old cached result is not used
  to manufacture the initial decision difference. After completion, exact
  recovery intentionally retains each real prior reply, and the historical
  projection preserves it under every finite future call word. Equal pooled
  balances refer to the states before the probe, not to states after a
  successful additional transfer. The parent threshold theorem is inherited;
  the new connection is to actual generated calls, completion and recovery.\<close>

end
