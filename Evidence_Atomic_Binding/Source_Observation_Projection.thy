(* SPDX-License-Identifier: BSD-3-Clause *)
theory Source_Observation_Projection
  imports Sourced_Observations Source_Coupling_Conservation Finality_Recovery
begin

record source_observation_target =
  target_observation :: observation_target
  target_source_units :: "source_account \<Rightarrow> nat"
  target_source_effects :: "transfer_binding list"
  target_source_returns :: "transfer_binding list"

definition source_observation_alpha :: "sourced_observation_state \<Rightarrow> source_observation_target" where
  "source_observation_alpha s=\<lparr>
    target_observation=observation_alpha(coupled_core(observation_source s)),
    target_source_units=boundary_units(controlled_endpoint(coupled_source(observation_source s))),
    target_source_effects=boundary_effects(controlled_endpoint(coupled_source(observation_source s))),
    target_source_returns=controlled_returns(coupled_source(observation_source s))\<rparr>"

context source_attestation
begin

fun coupling_core_word :: "source_coupling_action \<Rightarrow> source_coupling_state \<Rightarrow>
  finality_operation list" where
  "coupling_core_word(Coupling_Client available command)s=
    (if coupling_guard available s command then [client_operation(coupled_core s)command] else [])"
| "coupling_core_word(Coupling_Environment endpoint c)s=[Install_Context endpoint c]"
| "coupling_core_word _ s=[]"

lemma coupling_step_has_its_actual_core_word:
  "coupled_core(fst(source_coupling_step action s))=
    run_finality(coupling_core_word action s)(coupled_core s)"
proof (cases action)
  case (Coupling_Client available command)
  show ?thesis
  proof (cases "coupling_guard available s command")
    case True
    have actual: "coupling_client_result command s=execute_finality_client command(coupled_core s)"
      by (rule guarded_client_is_the_actual_child[OF True])
    show ?thesis by (simp add: Coupling_Client coupling_client_step_def True actual
        execute_finality_client_def Let_def split: option.splits)
  qed (simp add: Coupling_Client coupling_client_step_def)
qed (auto simp: coupling_source_result_def coupling_issue_result_def
  execute_finality_environment_def Let_def split: option.splits)

definition sourced_application_word :: "nat \<Rightarrow> nat \<Rightarrow> execution_request \<Rightarrow>
  nat \<Rightarrow> sourced_observation_state \<Rightarrow> finality_operation list" where
  "sourced_application_word endpoint index r asset s=
    (if protected_read_access endpoint index r(Application_Value asset)(sourced_view s)
     then case current_query_reply endpoint(Application_Value asset)(sourced_view s) of
       Current_Value revision payload \<Rightarrow> coupling_core_word
         (Coupling_Client(observation_source_available s)(Client_Protocol endpoint index(Data_Read_Intent r)))
         (observation_source s)
     | _ \<Rightarrow> [] else [])"

fun sourced_endpoint_word :: "observed_command \<Rightarrow> sourced_observation_state \<Rightarrow>
  finality_operation list" where
  "sourced_endpoint_word(Execute_Current endpoint command)s=
    (if current_cache_valid(sourced_view s)endpoint then
      coupling_core_word(Coupling_Client(observation_source_available s)command)(observation_source s) else [])"
| "sourced_endpoint_word(Read_Protected_Current endpoint index r(Application_Value asset))s=
    sourced_application_word endpoint index r asset s"
| "sourced_endpoint_word _ s=[]"

fun sourced_request_word :: "sourced_request \<Rightarrow> sourced_observation_state \<Rightarrow>
  finality_operation list" where
  "sourced_request_word(Endpoint_Request command)s=
    (case current_source_query command of None \<Rightarrow> sourced_endpoint_word command s
     | Some account \<Rightarrow> if observation_source_available s \<and>
         source_view_is_reconciled(observation_source s)account
       then sourced_endpoint_word command s else [])"
| "sourced_request_word _ s=[]"

fun sourced_environment_word :: "sourced_environment \<Rightarrow> finality_operation list" where
  "sourced_environment_word(View_Environment(Replace_Current_Context endpoint c))=[Install_Context endpoint c]"
| "sourced_environment_word _=[]"

lemma sourced_effect_projects_its_core_word:
  "coupled_core(observation_source(fst(sourced_effect_call endpoint command s)))=
    run_finality(sourced_endpoint_word(Execute_Current endpoint command)s)(coupled_core(observation_source s))"
  by (auto simp: sourced_effect_call_def install_sourced_view_def coupling_client_step_def Let_def
      guarded_client_is_the_actual_child execute_finality_client_def
      split: if_splits option.splits)

lemma sourced_application_projects_its_core_word:
  "coupled_core(observation_source(fst(sourced_application_read endpoint index r asset s)))=
    run_finality(sourced_application_word endpoint index r asset s)(coupled_core(observation_source s))"
  by (auto simp: sourced_application_read_def sourced_application_word_def install_sourced_view_def
      coupling_client_step_def Let_def guarded_client_is_the_actual_child execute_finality_client_def
      split: if_splits observed_reply.splits finality_reply.splits reservation_reply.splits option.splits)

theorem sourced_endpoint_projects_its_actual_core_word:
  "coupled_core(observation_source(fst(execute_sourced_endpoint command s)))=
    run_finality(sourced_endpoint_word command s)(coupled_core(observation_source s))"
proof (cases command)
  case (Read_Protected_Current endpoint index r query)
  show ?thesis by (cases query)
    (simp_all add: Read_Protected_Current sourced_application_projects_its_core_word
      install_sourced_view_def Let_def)
qed (auto simp: sourced_effect_projects_its_core_word install_sourced_view_def Let_def)

theorem sourced_request_projects_its_actual_core_word:
  "coupled_core(observation_source(fst(execute_sourced_request command s)))=
    run_finality(sourced_request_word command s)(coupled_core(observation_source s))"
  by (cases command)
    (auto simp: sourced_endpoint_projects_its_actual_core_word split: option.splits if_splits)

theorem sourced_environment_projects_its_actual_core_word:
  "coupled_core(observation_source(fst(execute_sourced_environment input s)))=
    run_finality(sourced_environment_word input)(coupled_core(observation_source s))"
proof (cases input)
  case (View_Environment view_input)
  show ?thesis by (cases view_input)
    (simp_all add: View_Environment install_sourced_view_def execute_finality_environment_def Let_def)
qed (auto simp: coupling_source_result_def coupling_issue_result_def Let_def split: option.splits)

fun sourced_core_operations ::
  "(sourced_request,sourced_reply,sourced_environment) authority_call_entry list \<Rightarrow>
    sourced_observation_state \<Rightarrow> finality_operation list" where
  "sourced_core_operations [] s=[]"
| "sourced_core_operations(Authority_Executed call_id command reply#rest)s=
    sourced_request_word command s@sourced_core_operations rest(fst(execute_sourced_request command s))"
| "sourced_core_operations(Authority_Input input reply#rest)s=
    sourced_environment_word input@sourced_core_operations rest(fst(execute_sourced_environment input s))"

theorem sourced_replay_projects_to_actual_finality_run:
  "coupled_core(observation_source(sourced_calls.replay_call_authority entries s))=
    run_finality(sourced_core_operations entries s)(coupled_core(observation_source s))"
proof (induction entries arbitrary:s)
  case Nil
  then show ?case by (simp only: sourced_calls.replay_call_authority.simps
    sourced_core_operations.simps run_finality.simps)
next
  case (Cons entry entries)
  then show ?case by (cases entry)
    (simp_all only: sourced_calls.replay_call_authority.simps sourced_core_operations.simps
      Cons.IH finality_run_append sourced_request_projects_its_actual_core_word
      sourced_environment_projects_its_actual_core_word)
qed

theorem sourced_replay_refines_both_product_words:
  fixes entries :: "(sourced_request,sourced_reply,sourced_environment) authority_call_entry list"
  assumes parent: "reservation_contract balances(core_parent(coupled_core(observation_source initial)))"
  defines "operations \<equiv> sourced_core_operations entries initial"
  shows "fst(finality_alpha(coupled_core(observation_source(sourced_calls.replay_call_authority entries initial))))=
      run_transfer_ledger(finality_transfer_word operations(coupled_core(observation_source initial)))
        (fst(finality_alpha(coupled_core(observation_source initial)))) \<and>
    run_regulatory_word(finality_regulatory_word operations(coupled_core(observation_source initial)))
        (snd(finality_alpha(coupled_core(observation_source initial))))=
      Some(snd(finality_alpha(coupled_core(observation_source(sourced_calls.replay_call_authority entries initial)))))"
  using finite_actual_child_execution_refines_transfer_word[OF parent, where actions=operations]
    finality_run_refines_regulatory_word[of operations "coupled_core(observation_source initial)"]
  by (simp only: sourced_replay_projects_to_actual_finality_run operations_def finality_alpha_def fst_conv snd_conv)

theorem generated_sourced_calls_have_actual_finality_core:
  fixes actions :: "(sourced_request,sourced_environment) client_call_action list"
    and initial :: sourced_observation_state
  defines "m \<equiv> sourced_calls.run_calls actions(initial_call_machine initial)"
  shows "coupled_core(observation_source(call_authority_state m))=
    run_finality(sourced_core_operations(call_authority_log m)initial)(coupled_core(observation_source initial))"
proof -
  have replay: "sourced_calls.authority_replay_contract m"
    using sourced_calls.generated_call_contracts[of actions initial] by (simp add: m_def)
  have genesis: "call_genesis m=initial" by (simp add: m_def initial_call_machine_def)
  have actual: "call_authority_state m=sourced_calls.replay_call_authority(call_authority_log m)initial"
    using replay by (simp add: sourced_calls.authority_replay_contract_def genesis)
  show ?thesis by (simp only: actual sourced_replay_projects_to_actual_finality_run)
qed

theorem generated_sourced_calls_refine_both_product_words:
  fixes actions :: "(sourced_request,sourced_environment) client_call_action list"
    and initial :: sourced_observation_state
  assumes parent: "reservation_contract balances(core_parent(coupled_core(observation_source initial)))"
  defines "m \<equiv> sourced_calls.run_calls actions(initial_call_machine initial)"
  shows "fst(finality_alpha(coupled_core(observation_source(call_authority_state m))))=
      run_transfer_ledger(finality_transfer_word(sourced_core_operations(call_authority_log m)initial)
        (coupled_core(observation_source initial)))
        (fst(finality_alpha(coupled_core(observation_source initial)))) \<and>
    run_regulatory_word(finality_regulatory_word(sourced_core_operations(call_authority_log m)initial)
        (coupled_core(observation_source initial)))
        (snd(finality_alpha(coupled_core(observation_source initial))))=
      Some(snd(finality_alpha(coupled_core(observation_source(call_authority_state m)))))"
proof -
  have replay: "sourced_calls.authority_replay_contract m"
    using sourced_calls.generated_call_contracts[of actions initial] by (simp add: m_def)
  have genesis: "call_genesis m=initial" by (simp add: m_def initial_call_machine_def)
  have actual: "call_authority_state m=sourced_calls.replay_call_authority(call_authority_log m)initial"
    using replay by (simp add: sourced_calls.authority_replay_contract_def genesis)
  show ?thesis unfolding actual
    by (rule sourced_replay_refines_both_product_words[OF parent])
qed

theorem sourced_replay_supplies_the_financial_and_regulatory_premises:
  assumes parent: "reservation_contract balances(core_parent(coupled_core(observation_source initial)))"
    and regulatory: "valid_state(receiver_snapshot(core_regulatory(coupled_core(observation_source initial))))"
  shows "reservation_contract balances(core_parent(coupled_core(observation_source
      (sourced_calls.replay_call_authority entries initial)))) \<and>
    valid_state(receiver_snapshot(core_regulatory(coupled_core(observation_source
      (sourced_calls.replay_call_authority entries initial)))))"
  by (simp only: sourced_replay_projects_to_actual_finality_run, intro conjI)
    (rule finite_finality_preserves_parent_contract[OF parent], rule finality_word_preserves_cdsp[OF regulatory])

theorem exact_sourced_recovery_preserves_source_and_current_consumers:
  assumes contract: "sourced_calls.authority_replay_contract source"
    and recovered: "sourced_calls.checked_current_replay source candidate=Some restored"
  shows "source_observation_alpha restored=source_observation_alpha(call_authority_state source) \<and>
    execute_sourced_request request restored=execute_sourced_request request(call_authority_state source)"
  using sourced_calls.valid_current_replay_is_the_actual_source_state[OF contract recovered] by simp

lemma sourced_endpoint_preserves_actual_source_accounting:
  assumes "source_coupling_accounting_invariant balances(observation_source s)"
  shows "source_coupling_accounting_invariant balances(observation_source(fst(execute_sourced_endpoint command s)))"
proof -
  have client: "source_coupling_accounting_invariant balances
      (fst(coupling_client_step available client(observation_source s)))"
    for available client
    using source_coupling_accounting_step[OF assms, where action="Coupling_Client available client"]
    by (simp only: source_coupling_step.simps)
  show ?thesis
  proof (cases command)
    case (Read_Protected_Current endpoint index r query)
    show ?thesis using assms by (cases query)
      (auto simp: Read_Protected_Current sourced_application_read_def install_sourced_view_def Let_def
        intro: client split: if_splits observed_reply.splits source_coupling_reply.splits
          finality_reply.splits reservation_reply.splits)
  qed (use assms in \<open>auto simp: sourced_effect_call_def install_sourced_view_def Let_def
    intro: client split: if_splits source_coupling_reply.splits\<close>)
qed

lemma sourced_request_preserves_actual_source_accounting:
  assumes "source_coupling_accounting_invariant balances(observation_source s)"
  shows "source_coupling_accounting_invariant balances(observation_source(fst(execute_sourced_request request s)))"
  using assms by (cases request)
    (auto intro: sourced_endpoint_preserves_actual_source_accounting split: option.splits if_splits)

lemma sourced_environment_preserves_actual_source_accounting:
  assumes "source_coupling_accounting_invariant balances(observation_source s)"
  shows "source_coupling_accounting_invariant balances(observation_source(fst(execute_sourced_environment input s)))"
proof (cases input)
  case (Source_Exchange arrived replied command)
  have actual: "source_coupling_accounting_invariant balances
    (fst(source_coupling_step(Coupling_Source arrived replied command)(observation_source s)))"
    by (rule source_coupling_accounting_step[OF assms])
  show ?thesis using actual by (simp add: Source_Exchange Let_def)
next
  case (Source_Receipt_Arrival available cert)
  have actual: "source_coupling_accounting_invariant balances
    (fst(source_coupling_step(Coupling_Issue available cert)(observation_source s)))"
    by (rule source_coupling_accounting_step[OF assms])
  show ?thesis using actual by (simp add: Source_Receipt_Arrival Let_def)
next
  case (View_Environment view_input)
  show ?thesis
  proof (cases view_input)
    case (Replace_Current_Context endpoint c)
    have actual: "source_coupling_accounting_invariant balances
      (fst(source_coupling_step(Coupling_Environment endpoint c)(observation_source s)))"
      by (rule source_coupling_accounting_step[OF assms])
    show ?thesis using actual
      by (simp add: View_Environment Replace_Current_Context install_sourced_view_def Let_def)
  qed (use assms View_Environment in \<open>simp_all add: install_sourced_view_def Let_def\<close>)
qed (use assms in simp)

lemma sourced_call_step_preserves_actual_source_accounting:
  assumes "source_coupling_accounting_invariant balances(observation_source(call_authority_state m))"
  shows "source_coupling_accounting_invariant balances
    (observation_source(call_authority_state(sourced_calls.call_step action m)))"
  using assms by (cases action)
    (auto simp: sourced_calls.call_definitions Let_def
      intro: sourced_request_preserves_actual_source_accounting sourced_environment_preserves_actual_source_accounting
      split: option.splits prod.splits if_splits)

theorem generated_sourced_calls_preserve_actual_source_accounting:
  "source_coupling_accounting_invariant balances(observation_source(call_authority_state
    (sourced_calls.run_calls actions(initial_call_machine(initial_sourced_observations balances regulatory contexts)))))"
proof -
  have preserve: "\<And>m. source_coupling_accounting_invariant balances(observation_source(call_authority_state m)) \<Longrightarrow>
    source_coupling_accounting_invariant balances(observation_source(call_authority_state(sourced_calls.run_calls actions m)))"
    by (induction actions) (auto intro: sourced_call_step_preserves_actual_source_accounting)
  have initial: "source_coupling_accounting_invariant balances(initial_source_coupling balances regulatory contexts)"
    using generated_joint_accounting_invariant[of balances "[]" regulatory contexts] by simp
  show ?thesis by (rule preserve)
    (simp add: initial_call_machine_def initial_sourced_observations_def Let_def initial)
qed

theorem actual_sourced_calls_preserve_the_physical_pool:
  fixes actions :: "(sourced_request,sourced_environment) client_call_action list"
    and balances :: "source_account \<Rightarrow> nat" and regulatory :: global_state
    and contexts :: "nat \<Rightarrow> lock_context"
  defines "provider \<equiv> observation_source(call_authority_state(sourced_calls.run_calls actions
    (initial_call_machine(initial_sourced_observations balances regulatory contexts))))"
  shows "coupling_remote_returns provider\<inter>coupling_credits provider={} \<and>
    int(boundary_units(controlled_endpoint(coupled_source provider))pool)+
      coupling_remote_pending_mass provider pool+
      destination_pool_funding(machine_state(core_parent(coupled_core provider)))pool=int(balances pool)"
proof -
  have inv: "source_coupling_accounting_invariant balances provider"
    unfolding provider_def by (rule generated_sourced_calls_preserve_actual_source_accounting)
  show ?thesis using remote_return_and_child_credit_are_disjoint[OF inv]
    actual_source_pool_is_conserved[OF inv, where pool=pool] by blast
qed

theorem actual_sourced_history_supplies_the_complete_recovery_candidate:
  "sourced_calls.checked_current_replay(sourced_calls.run_calls actions(initial_call_machine initial))
    (current_source_candidate(sourced_calls.run_calls actions(initial_call_machine initial)))=
    Some(call_authority_state(sourced_calls.run_calls actions(initial_call_machine initial)))"
  by (rule sourced_calls.generated_source_supplies_recovery_without_a_truth_flag)

theorem restored_sourced_dispatch_still_uses_the_actual_source_guard:
  assumes contract: "sourced_calls.authority_replay_contract(recovery_source runtime)"
    and connected: "recovery_connected runtime"
    and recovered: "sourced_calls.checked_current_replay(recovery_source runtime)candidate=Some state"
  shows "recovery_source(sourced_calls.dispatch_from_recovered_replica call_id command
    (sourced_calls.restore_current_replica candidate runtime))=
      sourced_calls.dispatch_client_call call_id command(recovery_source runtime)"
  by (rule sourced_calls.restored_dispatch_is_the_actual_guarded_call[OF contract connected recovered])

theorem physical_source_unit_response_has_its_independent_target:
  "observation_source_available s \<Longrightarrow>
    snd(execute_sourced_request(Inspect_Source_Units account)s)=
      Source_Unit_Value(target_source_units(source_observation_alpha s)account)"
  by (simp add: source_observation_alpha_def)

theorem physical_source_effect_response_has_its_independent_target:
  "observation_source_available s \<Longrightarrow>
    snd(execute_sourced_request Inspect_Source_Effects s)=
      Source_Effect_History(target_source_effects(source_observation_alpha s))"
  by (simp add: source_observation_alpha_def)

end

section \<open>A Real Lost Acknowledgment Distinguishes the Source Observation\<close>

definition source_raw_start :: sourced_observation_state where
  "source_raw_start=initial_sourced_observations sample_balances(sample_metadata ACTIVE)
    (\<lambda>_.sample_source_context ACTIVE)"

definition source_raw_after :: sourced_observation_state where
  "source_raw_after=call_authority_state(linked.sourced_calls.run_calls
    [Apply_Authority_Input(Source_Exchange True False
      (Controlled_Boundary(Boundary_Apply(sample_binding 17))))]
      (initial_call_machine source_raw_start))"

lemma source_raw_after_is_the_actual_callback:
  "source_raw_after=fst(linked.execute_sourced_environment
    (Source_Exchange True False(Controlled_Boundary(Boundary_Apply(sample_binding 17))))source_raw_start)"
  by (simp add: source_raw_after_def initial_call_machine_def linked.sourced_calls.call_definitions Let_def)

theorem lost_source_ack_has_identical_local_observation_state:
  "sourced_view source_raw_after=sourced_view source_raw_start"
  by (simp add: source_raw_after_is_the_actual_callback coupling_source_result_def
    sourced_view_def Let_def split: option.splits)

theorem lost_source_ack_changes_the_actual_physical_observation:
  "linked.execute_sourced_request(Inspect_Source_Units(0,17))source_raw_start=
      (source_raw_start,Source_Unit_Value 10) \<and>
    linked.execute_sourced_request(Inspect_Source_Units(0,17))source_raw_after=
      (source_raw_after,Source_Unit_Value 5)"
  by (simp add: source_raw_after_is_the_actual_callback source_raw_start_def
    initial_sourced_observations_def initial_source_coupling_def initial_controlled_source_def
    initial_source_boundary_def coupling_source_result_def controlled_boundary_def boundary_apply_def
    boundary_record_effect_def boundary_valid_binding_def sample_binding_def example_binding_def
    sample_balances_def source_account_of_def Let_def)

theorem local_view_cannot_reconstruct_every_physical_source_response:
  "\<not>(\<exists>read_units. \<forall>s. observation_source_available s \<longrightarrow>
    snd(linked.execute_sourced_request(Inspect_Source_Units(0,17))s)=read_units(sourced_view s))"
proof -
  have available: "observation_source_available source_raw_start" "observation_source_available source_raw_after"
    by (simp_all add: source_raw_start_def source_raw_after_is_the_actual_callback
      initial_sourced_observations_def Let_def)
  have before_execution: "linked.execute_sourced_request(Inspect_Source_Units(0,17))source_raw_start=
      (source_raw_start,Source_Unit_Value 10)"
    and after_execution: "linked.execute_sourced_request(Inspect_Source_Units(0,17))source_raw_after=
      (source_raw_after,Source_Unit_Value 5)"
    using lost_source_ack_changes_the_actual_physical_observation by blast+
  have before_reply: "snd(linked.execute_sourced_request(Inspect_Source_Units(0,17))source_raw_start)=
    Source_Unit_Value 10"
    by (simp only: before_execution snd_conv)
  have after_reply: "snd(linked.execute_sourced_request(Inspect_Source_Units(0,17))source_raw_after)=
    Source_Unit_Value 5"
    by (simp only: after_execution snd_conv)
  show ?thesis
  proof
    assume "\<exists>read_units. \<forall>s. observation_source_available s \<longrightarrow>
      snd(linked.execute_sourced_request(Inspect_Source_Units(0,17))s)=read_units(sourced_view s)"
    then obtain read_units where decoder:
      "\<And>s. observation_source_available s \<Longrightarrow>
        snd(linked.execute_sourced_request(Inspect_Source_Units(0,17))s)=read_units(sourced_view s)"
      by blast
    have before_value: "Source_Unit_Value 10=read_units(sourced_view source_raw_start)"
      using decoder[OF available(1)] by (simp only: before_reply)
    have after_value: "Source_Unit_Value 5=read_units(sourced_view source_raw_after)"
      using decoder[OF available(2)] by (simp only: after_reply)
    have "Source_Unit_Value 10=read_units(sourced_view source_raw_start)"
      by (rule before_value)
    also have "...=read_units(sourced_view source_raw_after)"
      by (simp only: lost_source_ack_has_identical_local_observation_state)
    also have "...=Source_Unit_Value 5"
      by (rule after_value[symmetric])
    finally show False by simp
  qed
qed

definition source_raw_refreshed :: sourced_observation_state where
  "source_raw_refreshed=fst(linked.execute_sourced_request(Endpoint_Request(Refresh_Endpoint 0))source_raw_after)"

lemma source_refresh_calculation:
  "source_attestation.execute_observed example_roster example_threshold
      (source_receipt_verifies linked_receipts)(Refresh_Endpoint endpoint)view=
    (view\<lparr>endpoint_cache:=(endpoint_cache view)
      (endpoint:=Some(capture_snapshot(observed_core view)))\<rparr>,Cache_Refreshed)"
  by (rule source_attestation.execute_observed.simps(8)[OF linked.source_attestation_axioms])

lemma source_refresh_keeps_the_actual_provider:
  "observation_source source_raw_refreshed=observation_source source_raw_after"
  "observation_source_available source_raw_refreshed"
  "sourced_view source_raw_refreshed=(sourced_view source_raw_after)\<lparr>
    endpoint_cache:=(endpoint_cache(sourced_view source_raw_after))
      (0:=Some(capture_snapshot(observed_core(sourced_view source_raw_after))))\<rparr>"
  by (simp_all add: source_raw_refreshed_def source_refresh_calculation install_sourced_view_def sourced_view_def Let_def
    source_raw_after_is_the_actual_callback source_raw_start_def initial_sourced_observations_def)

lemma lost_ack_has_an_actual_unreconciled_debit:
  "source_debit_gap(coupled_source(observation_source source_raw_refreshed))
    (core_parent(coupled_core(observation_source source_raw_refreshed)))(0,17)=5"
  by (simp add: source_refresh_keeps_the_actual_provider source_raw_after_is_the_actual_callback
    source_raw_start_def initial_sourced_observations_def initial_source_coupling_def
    initial_controlled_source_def initial_source_boundary_def initial_finality_core_def
    initial_reservation_machine_def initial_reservation_state_def source_debit_gap_def source_debits_def
    coupling_source_result_def controlled_boundary_def boundary_apply_def boundary_record_effect_def
    boundary_valid_binding_def boundary_debited_def sample_binding_def example_binding_def
    sample_balances_def source_account_of_def Let_def)

theorem actual_source_gap_blocks_the_current_balance_response:
  "snd(linked.execute_sourced_request(Endpoint_Request(Read_Current 0(Source_Balance(0,17))))
    source_raw_refreshed)=Sourced_Observation Observation_Busy"
proof -
  have gap: "\<not>source_view_is_reconciled(observation_source source_raw_refreshed)(0,17)"
    by (simp add: source_view_is_reconciled_def lost_ack_has_an_actual_unreconciled_debit)
  show ?thesis by (simp add: gap source_refresh_keeps_the_actual_provider(2))
qed

theorem removing_the_source_gap_guard_exposes_a_stale_physical_balance:
  "snd(linked.execute_sourced_endpoint(Read_Current 0(Source_Balance(0,17)))source_raw_refreshed)=
      Sourced_Observation(Current_Value 0(Units_Value 10)) \<and>
    snd(linked.execute_sourced_request(Inspect_Source_Units(0,17))source_raw_refreshed)=Source_Unit_Value 5"
proof -
  note read_current = source_attestation.execute_observed.simps(1)[OF linked.source_attestation_axioms]
  have view: "sourced_view source_raw_refreshed=(sourced_view source_raw_start)\<lparr>
    endpoint_cache:=(endpoint_cache(sourced_view source_raw_start))
      (0:=Some(capture_snapshot(observed_core(sourced_view source_raw_start))))\<rparr>"
    using source_refresh_keeps_the_actual_provider(3)
    by (simp only: lost_source_ack_has_identical_local_observation_state)
  have current_reply: "current_query_reply 0(Source_Balance(0,17))(sourced_view source_raw_refreshed)=
    Current_Value 0(Units_Value 10)"
    unfolding view
    by (simp add: source_raw_start_def initial_sourced_observations_def initial_source_coupling_def sourced_view_def
      initial_observed_finality_def initial_finality_core_def initial_reservation_machine_def
      initial_reservation_state_def empty_message_state_def current_query_reply_def current_cache_valid_def
      snapshot_query_ready_def capture_snapshot_def sample_balances_def Let_def)
  have local_reply: "snd(linked.execute_sourced_endpoint(Read_Current 0(Source_Balance(0,17)))source_raw_refreshed)=
    Sourced_Observation(Current_Value 0(Units_Value 10))"
    by (simp add: read_current current_reply Let_def)
  have after_execution: "linked.execute_sourced_request(Inspect_Source_Units(0,17))source_raw_after=
    (source_raw_after,Source_Unit_Value 5)"
    using lost_source_ack_changes_the_actual_physical_observation by blast
  have after_available: "observation_source_available source_raw_after"
    by (simp add: source_raw_after_is_the_actual_callback source_raw_start_def initial_sourced_observations_def Let_def)
  have after_units: "boundary_units(controlled_endpoint(coupled_source(observation_source source_raw_after)))(0,17)=5"
    using after_execution by (simp add: after_available)
  have physical_reply: "snd(linked.execute_sourced_request(Inspect_Source_Units(0,17))source_raw_refreshed)=
    Source_Unit_Value 5"
    by (simp add: source_refresh_keeps_the_actual_provider(1,2) after_units)
  show ?thesis using local_reply physical_reply by blast
qed

text \<open>The source target keeps physical available units and the source's
  effect and return histories in addition to the local observation target.
  A single generated environment input can execute a source effect and lose
  its reply while leaving the complete local observation state unchanged.
  Consequently that local state alone cannot reconstruct every physical
  response. The source observer remains in the API. Product action words
  describe actual admitted core transitions; their stuttering source steps
  are visible in the richer source target. Recovery requires the current
  authoritative source and reuses the actual sourced dispatcher. A new
  authority execution consumes current guards; a repeated identifier with
  an existing durable result retransmits that result without executing again.
  The target is not a classifier for every API reply: source availability,
  endpoint caches, historical cuts, secondary progress and current permission
  inputs remain explicit in the corresponding response relations. In
  particular, changing source availability can change a physical inspection
  to Unavailable without changing this target. The result for the two product
  words concerns the actual core projection, not a full transition simulation of
  this larger source target. Physical authentication, persistence and
  availability remain implementation duties.\<close>

end
