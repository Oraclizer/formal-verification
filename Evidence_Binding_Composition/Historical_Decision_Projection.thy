(* SPDX-License-Identifier: BSD-3-Clause *)
theory Historical_Decision_Projection
  imports "Evidence_Atomic_Binding.Sourced_Observations"
    "Evidence_Atomic_Binding.Finality_Recovery"
    "Evidence_Atomic_Binding.Regulatory_Finality_Scenarios"
begin

section \<open>The Primitive Information of Historical Queries\<close>

definition normalize_historical_snapshot :: "endpoint_snapshot \<Rightarrow> endpoint_snapshot" where
  "normalize_historical_snapshot snapshot = snapshot\<lparr>snapshot_financial :=
    (snapshot_financial snapshot)\<lparr>reservation_at := (\<lambda>_. None),
      asset_version := (\<lambda>_. 0), issued_certificates := [],
      received_messages := empty_message_state, lawful_descendants := [],
      reservation_clock := 0\<rparr>\<rparr>"

lemma normalize_historical_snapshot_idempotent [simp]:
  "normalize_historical_snapshot(normalize_historical_snapshot snapshot) =
    normalize_historical_snapshot snapshot"
  by (simp add: normalize_historical_snapshot_def)

lemma normalized_snapshot_stored_query [simp]:
  "stored_query query(normalize_historical_snapshot snapshot) = stored_query query snapshot"
  by (cases query) (simp_all add: normalize_historical_snapshot_def)

lemma normalized_snapshot_query_ready [simp]:
  "snapshot_query_ready query(normalize_historical_snapshot snapshot) =
    snapshot_query_ready query snapshot"
  by (cases query)
    (simp_all add: snapshot_query_ready_def normalize_historical_snapshot_def)

lemma normalized_snapshot_keeps_revision_records_and_publication:
  "snapshot_revision(normalize_historical_snapshot snapshot) = snapshot_revision snapshot"
  "snapshot_records(normalize_historical_snapshot snapshot) = snapshot_records snapshot"
  "snapshot_published(normalize_historical_snapshot snapshot) = snapshot_published snapshot"
  "snapshot_regulatory(normalize_historical_snapshot snapshot) = snapshot_regulatory snapshot"
  "source_effects(snapshot_financial(normalize_historical_snapshot snapshot)) =
    source_effects(snapshot_financial snapshot)"
  by (simp_all add: normalize_historical_snapshot_def)

definition normalize_snapshot_history :: "(nat \<Rightarrow> endpoint_snapshot option) \<Rightarrow>
  nat \<Rightarrow> endpoint_snapshot option" where
  "normalize_snapshot_history history = (\<lambda>revision.
    map_option normalize_historical_snapshot(history revision))"

lemma normalize_snapshot_history_lookup [simp]:
  "normalize_snapshot_history history revision =
    map_option normalize_historical_snapshot(history revision)"
  by (simp add: normalize_snapshot_history_def)

lemma normalize_snapshot_history_idempotent [simp]:
  "normalize_snapshot_history(normalize_snapshot_history history) = normalize_snapshot_history history"
proof (rule ext)
  fix revision
  show "normalize_snapshot_history(normalize_snapshot_history history) revision =
      normalize_snapshot_history history revision"
    by (cases "history revision") simp_all
qed

lemma normalize_snapshot_history_update [simp]:
  "normalize_snapshot_history(history(revision := Some snapshot)) =
    (normalize_snapshot_history history)(revision := Some(normalize_historical_snapshot snapshot))"
  by (rule ext) simp

definition normalize_observed_history :: "observed_finality \<Rightarrow> observed_finality" where
  "normalize_observed_history state = state\<lparr>historical_snapshots :=
    normalize_snapshot_history(historical_snapshots state)\<rparr>"

lemma normalize_observed_history_idempotent [simp]:
  "normalize_observed_history(normalize_observed_history state) = normalize_observed_history state"
  by (simp add: normalize_observed_history_def)

lemma normalize_observed_history_fields [simp]:
  "observed_core(normalize_observed_history state) = observed_core state"
  "endpoint_cache(normalize_observed_history state) = endpoint_cache state"
  "secondary_progress(normalize_observed_history state) = secondary_progress state"
  "historical_snapshots(normalize_observed_history state) =
    normalize_snapshot_history(historical_snapshots state)"
  by (simp_all add: normalize_observed_history_def)

lemma normalize_observed_history_cache_update [simp]:
  "normalize_observed_history(state\<lparr>endpoint_cache := cache\<rparr>) =
    (normalize_observed_history state)\<lparr>endpoint_cache := cache\<rparr>"
  by (simp add: normalize_observed_history_def)

lemma normalize_observed_history_secondary_update [simp]:
  "normalize_observed_history(state\<lparr>secondary_progress := progress\<rparr>) =
    (normalize_observed_history state)\<lparr>secondary_progress := progress\<rparr>"
  by (simp add: normalize_observed_history_def)

lemma normalized_current_cache_valid [simp]:
  "current_cache_valid(normalize_observed_history state) endpoint = current_cache_valid state endpoint"
  by (simp add: current_cache_valid_def)

lemma normalized_protected_read_access [simp]:
  "protected_read_access endpoint index request query(normalize_observed_history state) =
    protected_read_access endpoint index request query state"
  by (simp add: protected_read_access_def)

lemma normalized_current_query_reply [simp]:
  "current_query_reply endpoint query(normalize_observed_history state) =
    current_query_reply endpoint query state"
  by (simp add: current_query_reply_def split: option.splits)

lemma normalized_historical_query_reply [simp]:
  "historical_query_reply revision query(normalize_observed_history state) =
    historical_query_reply revision query state"
  by (simp add: historical_query_reply_def split: option.splits)

lemma normalized_store_core_state [simp]:
  "normalize_observed_history(fst(store_core_result result(normalize_observed_history state))) =
    normalize_observed_history(fst(store_core_result result state))"
  by (simp add: store_core_result_def normalize_observed_history_def Let_def)

lemma store_core_reply [simp]:
  "snd(store_core_result result state) = Effect_Reply(snd result)"
  by (simp add: store_core_result_def Let_def)

definition normalize_result :: "('state \<Rightarrow> 'state) \<Rightarrow> 'state \<times> 'reply \<Rightarrow>
  'state \<times> 'reply" where
  "normalize_result projection_map result = (projection_map(fst result), snd result)"

lemma normalize_result_components:
  fixes projection_map :: "'state \<Rightarrow> 'state"
    and first second :: "'state \<times> 'reply"
  assumes "normalize_result projection_map first = normalize_result projection_map second"
  shows "projection_map(fst first) = projection_map(fst second)" "snd first = snd second"
  using assms by (simp_all add: normalize_result_def)

context source_attestation
begin

lemma protected_current_history_projection:
  "normalize_result normalize_observed_history
      (execute_protected_current endpoint index request query(normalize_observed_history state)) =
    normalize_result normalize_observed_history
      (execute_protected_current endpoint index request query state)"
  by (auto simp: execute_protected_current_def normalize_result_def Let_def
      split: observed_reply.splits application_query.splits finality_reply.splits
        reservation_reply.splits if_splits)

theorem observed_callback_history_projection:
  "normalize_result normalize_observed_history(execute_observed command(normalize_observed_history state)) =
    normalize_result normalize_observed_history(execute_observed command state)"
  by (cases command)
    (simp_all add: normalize_result_def protected_current_history_projection
      normalize_result_components(1)[OF protected_current_history_projection]
      normalize_result_components(2)[OF protected_current_history_projection]
      Let_def split: if_splits)

theorem observed_environment_history_projection:
  "normalize_result normalize_observed_history
      (execute_observed_environment input(normalize_observed_history state)) =
    normalize_result normalize_observed_history(execute_observed_environment input state)"
  by (cases input) (simp_all add: normalize_result_def Let_def)

lemma observed_callback_reply_preserved:
  "snd(execute_observed command(normalize_observed_history state)) = snd(execute_observed command state)"
  by (rule normalize_result_components(2)[OF observed_callback_history_projection])

lemma observed_callback_update_preserved:
  "normalize_observed_history(fst(execute_observed command(normalize_observed_history state))) =
    normalize_observed_history(fst(execute_observed command state))"
  by (rule normalize_result_components(1)[OF observed_callback_history_projection])

lemma observed_environment_reply_preserved:
  "snd(execute_observed_environment input(normalize_observed_history state)) =
    snd(execute_observed_environment input state)"
  by (rule normalize_result_components(2)[OF observed_environment_history_projection])

lemma observed_environment_update_preserved:
  "normalize_observed_history(fst(execute_observed_environment input(normalize_observed_history state))) =
    normalize_observed_history(fst(execute_observed_environment input state))"
  by (rule normalize_result_components(1)[OF observed_environment_history_projection])

end

section \<open>The Source-Aware Endpoint Retains Its Actual Source\<close>

definition normalize_sourced_history :: "sourced_observation_state \<Rightarrow> sourced_observation_state" where
  "normalize_sourced_history state = state\<lparr>observation_history :=
    normalize_snapshot_history(observation_history state)\<rparr>"

lemma normalize_sourced_history_idempotent [simp]:
  "normalize_sourced_history(normalize_sourced_history state) = normalize_sourced_history state"
  by (simp add: normalize_sourced_history_def)

lemma normalize_sourced_history_fields [simp]:
  "observation_source(normalize_sourced_history state) = observation_source state"
  "observation_caches(normalize_sourced_history state) = observation_caches state"
  "observation_secondary(normalize_sourced_history state) = observation_secondary state"
  "observation_source_available(normalize_sourced_history state) = observation_source_available state"
  "observation_history(normalize_sourced_history state) =
    normalize_snapshot_history(observation_history state)"
  by (simp_all add: normalize_sourced_history_def)

lemma sourced_view_normalized [simp]:
  "sourced_view(normalize_sourced_history state) = normalize_observed_history(sourced_view state)"
  by (simp add: sourced_view_def normalize_sourced_history_def normalize_observed_history_def)

lemma normalize_installed_sourced_view:
  "normalize_sourced_history(install_sourced_view provider view state) =
    install_sourced_view provider(normalize_observed_history view)(normalize_sourced_history state)"
  by (simp add: install_sourced_view_def normalize_sourced_history_def normalize_observed_history_def)

lemma normalized_install_base [simp]:
  "normalize_sourced_history(install_sourced_view provider view(normalize_sourced_history state)) =
    normalize_sourced_history(install_sourced_view provider view state)"
  by (simp add: install_sourced_view_def normalize_sourced_history_def)

lemma normalized_install_view [simp]:
  "normalize_sourced_history(install_sourced_view provider(normalize_observed_history view) state) =
    normalize_sourced_history(install_sourced_view provider view state)"
  by (simp add: install_sourced_view_def normalize_sourced_history_def normalize_observed_history_def)

lemma normalized_install_cong:
  assumes "normalize_observed_history first = normalize_observed_history second"
  shows "normalize_sourced_history(install_sourced_view provider first state) =
    normalize_sourced_history(install_sourced_view provider second state)"
  using arg_cong[OF assms, where f="\<lambda>view.
    install_sourced_view provider view(normalize_sourced_history state)"]
  by (simp only: normalize_installed_sourced_view[symmetric])

lemma normalized_install_cache_update [simp]:
  "normalize_sourced_history(install_sourced_view provider
      ((normalize_observed_history view)\<lparr>endpoint_cache := cache\<rparr>) state) =
    normalize_sourced_history(install_sourced_view provider(view\<lparr>endpoint_cache := cache\<rparr>) state)"
  by (rule normalized_install_cong) simp

lemma normalized_install_secondary_update [simp]:
  "normalize_sourced_history(install_sourced_view provider
      ((normalize_observed_history view)\<lparr>secondary_progress := progress\<rparr>) state) =
    normalize_sourced_history(install_sourced_view provider(view\<lparr>secondary_progress := progress\<rparr>) state)"
  by (rule normalized_install_cong) simp

lemma normalize_sourced_source_update [simp]:
  "normalize_sourced_history(state\<lparr>observation_source := provider\<rparr>) =
    (normalize_sourced_history state)\<lparr>observation_source := provider\<rparr>"
  by (simp add: normalize_sourced_history_def)

lemma normalize_sourced_availability_update [simp]:
  "normalize_sourced_history(state\<lparr>observation_source_available := available\<rparr>) =
    (normalize_sourced_history state)\<lparr>observation_source_available := available\<rparr>"
  by (simp add: normalize_sourced_history_def)

lemma normalized_install_stored_core [simp]:
  "normalize_sourced_history(install_sourced_view provider
      (fst(store_core_result result(normalize_observed_history view))) state) =
    normalize_sourced_history(install_sourced_view provider(fst(store_core_result result view)) state)"
  by (rule normalized_install_cong) (rule normalized_store_core_state)

context source_attestation
begin

lemma normalized_install_protected_current [simp]:
  "normalize_sourced_history(install_sourced_view provider
      (fst(execute_protected_current endpoint index request query(normalize_observed_history view))) state) =
    normalize_sourced_history(install_sourced_view provider
      (fst(execute_protected_current endpoint index request query view)) state)"
  by (rule normalized_install_cong)
    (rule normalize_result_components(1)[OF protected_current_history_projection])

lemma normalized_install_observed_callback [simp]:
  "normalize_sourced_history(install_sourced_view provider
      (fst(execute_observed command(normalize_observed_history view))) state) =
    normalize_sourced_history(install_sourced_view provider(fst(execute_observed command view)) state)"
  by (rule normalized_install_cong) (rule observed_callback_update_preserved)

lemma normalized_install_observed_environment [simp]:
  "normalize_sourced_history(install_sourced_view provider
      (fst(execute_observed_environment input(normalize_observed_history view))) state) =
    normalize_sourced_history(install_sourced_view provider(fst(execute_observed_environment input view)) state)"
  by (rule normalized_install_cong) (rule observed_environment_update_preserved)

lemma sourced_effect_history_projection:
  "normalize_result normalize_sourced_history
      (sourced_effect_call endpoint command(normalize_sourced_history state)) =
    normalize_result normalize_sourced_history(sourced_effect_call endpoint command state)"
  by (auto simp: sourced_effect_call_def normalize_result_def Let_def
      split: source_coupling_reply.splits if_splits)

lemma sourced_application_history_projection:
  "normalize_result normalize_sourced_history
      (sourced_application_read endpoint index request asset(normalize_sourced_history state)) =
    normalize_result normalize_sourced_history(sourced_application_read endpoint index request asset state)"
  by (auto simp: sourced_application_read_def normalize_result_def Let_def
      split: observed_reply.splits source_coupling_reply.splits finality_reply.splits
        reservation_reply.splits if_splits)

theorem sourced_endpoint_history_projection:
  "normalize_result normalize_sourced_history
      (execute_sourced_endpoint command(normalize_sourced_history state)) =
    normalize_result normalize_sourced_history(execute_sourced_endpoint command state)"
proof (cases command)
  case (Read_Protected_Current endpoint index request query)
  then show ?thesis
    by (cases query)
      (auto simp: normalize_result_def Let_def observed_callback_reply_preserved
        normalize_result_components(2)[OF protected_current_history_projection]
        normalize_result_components(1)[OF sourced_application_history_projection]
        normalize_result_components(2)[OF sourced_application_history_projection])
qed (auto simp: normalize_result_def Let_def observed_callback_reply_preserved
      normalize_result_components(1)[OF sourced_effect_history_projection]
      normalize_result_components(2)[OF sourced_effect_history_projection])

theorem sourced_callback_history_projection:
  "normalize_result normalize_sourced_history
      (execute_sourced_request request(normalize_sourced_history state)) =
    normalize_result normalize_sourced_history(execute_sourced_request request state)"
  by (cases request)
    (auto simp: normalize_result_def
      normalize_result_components(1)[OF sourced_endpoint_history_projection]
      normalize_result_components(2)[OF sourced_endpoint_history_projection]
      split: option.splits if_splits)

theorem sourced_environment_history_projection:
  "normalize_result normalize_sourced_history
      (execute_sourced_environment input(normalize_sourced_history state)) =
    normalize_result normalize_sourced_history(execute_sourced_environment input state)"
proof (cases input)
  case (View_Environment environment)
  then show ?thesis
    by (cases environment)
      (auto simp: normalize_result_def Let_def observed_environment_reply_preserved
        split: source_coupling_reply.splits)
qed (auto simp: normalize_result_def Let_def)

lemma sourced_callback_reply_preserved:
  "snd(execute_sourced_request request(normalize_sourced_history state)) =
    snd(execute_sourced_request request state)"
  by (rule normalize_result_components(2)[OF sourced_callback_history_projection])

lemma sourced_callback_update_preserved:
  "normalize_sourced_history(fst(execute_sourced_request request(normalize_sourced_history state))) =
    normalize_sourced_history(fst(execute_sourced_request request state))"
  by (rule normalize_result_components(1)[OF sourced_callback_history_projection])

lemma sourced_environment_reply_preserved:
  "snd(execute_sourced_environment input(normalize_sourced_history state)) =
    snd(execute_sourced_environment input state)"
  by (rule normalize_result_components(2)[OF sourced_environment_history_projection])

lemma sourced_environment_update_preserved:
  "normalize_sourced_history(fst(execute_sourced_environment input(normalize_sourced_history state))) =
    normalize_sourced_history(fst(execute_sourced_environment input state))"
  by (rule normalize_result_components(1)[OF sourced_environment_history_projection])

end

section \<open>Actual Durable Calls over an Operational State Projection\<close>

text \<open>The hypotheses below are equations of executable callbacks. The two
  concrete interpretations supply them by unfolding every observed and
  source-aware constructor above. There is no assumed safety decision or
  assumed reply table. Both call protocols use the existing invocation,
  dispatch, response collection, completion, crash and connection functions.\<close>

locale operational_call_projection =
  fixes projection_map :: "'state \<Rightarrow> 'state"
    and execute :: "'command \<Rightarrow> 'state \<Rightarrow> 'state \<times> 'reply"
    and environment_execute :: "'environment \<Rightarrow> 'state \<Rightarrow> 'state \<times> 'reply"
  assumes normalize_idempotent: "\<And>state. projection_map(projection_map state) = projection_map state"
    and command_reply: "\<And>command state. snd(execute command(projection_map state)) = snd(execute command state)"
    and command_update: "\<And>command state.
      projection_map(fst(execute command(projection_map state))) = projection_map(fst(execute command state))"
    and environment_reply: "\<And>input state.
      snd(environment_execute input(projection_map state)) = snd(environment_execute input state)"
    and environment_update: "\<And>input state.
      projection_map(fst(environment_execute input(projection_map state))) = projection_map(fst(environment_execute input state))"
begin

definition reduced_execute :: "'command \<Rightarrow> 'state \<Rightarrow> 'state \<times> 'reply" where
  "reduced_execute command state = normalize_result projection_map(execute command state)"

definition reduced_environment_execute :: "'environment \<Rightarrow> 'state \<Rightarrow> 'state \<times> 'reply" where
  "reduced_environment_execute input state = normalize_result projection_map(environment_execute input state)"

sublocale original: durable_call_protocol execute environment_execute .
sublocale reduced: durable_call_protocol reduced_execute reduced_environment_execute .

lemma reduced_command_on_projection [simp]:
  "reduced_execute command(projection_map state) =
    (projection_map(fst(execute command state)), snd(execute command state))"
  by (simp add: reduced_execute_def normalize_result_def command_reply command_update)

lemma reduced_environment_on_projection [simp]:
  "reduced_environment_execute input(projection_map state) =
    (projection_map(fst(environment_execute input state)), snd(environment_execute input state))"
  by (simp add: reduced_environment_execute_def normalize_result_def environment_reply environment_update)

definition normalize_call_machine ::
  "('state,'command,'reply,'environment) durable_call_machine \<Rightarrow>
    ('state,'command,'reply,'environment) durable_call_machine" where
  "normalize_call_machine machine = machine\<lparr>
    call_genesis := projection_map(call_genesis machine),
    call_authority_state := projection_map(call_authority_state machine)\<rparr>"

lemma normalize_call_machine_idempotent [simp]:
  "normalize_call_machine(normalize_call_machine machine) = normalize_call_machine machine"
  by (simp add: normalize_call_machine_def normalize_idempotent)

lemma normalized_call_fields [simp]:
  "call_genesis(normalize_call_machine machine) = projection_map(call_genesis machine)"
  "call_authority_state(normalize_call_machine machine) = projection_map(call_authority_state machine)"
  "call_authority_log(normalize_call_machine machine) = call_authority_log machine"
  "call_authority_results(normalize_call_machine machine) = call_authority_results machine"
  "call_invocations(normalize_call_machine machine) = call_invocations machine"
  "call_completions(normalize_call_machine machine) = call_completions machine"
  "call_local_results(normalize_call_machine machine) = call_local_results machine"
  "call_local_status(normalize_call_machine machine) = call_local_status machine"
  "call_connection(normalize_call_machine machine) = call_connection machine"
  "call_history(normalize_call_machine machine) = call_history machine"
  by (simp_all add: normalize_call_machine_def)

lemma normalized_initial_call_machine [simp]:
  "normalize_call_machine(initial_call_machine state) = initial_call_machine(projection_map state)"
  by (simp add: normalize_call_machine_def initial_call_machine_def)

lemma begin_call_projection:
  "reduced.begin_client_call call_id command(normalize_call_machine machine) =
    normalize_call_machine(original.begin_client_call call_id command machine)"
  by (auto simp: reduced.begin_client_call_def original.begin_client_call_def normalize_call_machine_def
      split: option.splits prod.splits if_splits)

lemma execute_once_projection:
  "reduced.execute_authority_once call_id command(normalize_call_machine machine) =
    normalize_call_machine(original.execute_authority_once call_id command machine)"
  by (auto simp: reduced.execute_authority_once_def original.execute_authority_once_def
      normalize_call_machine_def Let_def split: option.splits prod.splits if_splits)

lemma dispatch_call_projection:
  "reduced.dispatch_client_call call_id command(normalize_call_machine machine) =
    normalize_call_machine(original.dispatch_client_call call_id command machine)"
proof (cases "call_local_status machine = Endpoint_Up \<and>
    call_connection machine = Authority_Connected \<and>
    map_option fst(call_invocations machine call_id) = Some command")
  case True
  then show ?thesis
    by (simp only: reduced.dispatch_client_call_def original.dispatch_client_call_def
        normalized_call_fields True HOL.simp_thms if_True execute_once_projection)
next
  case False
  have reduced_guard_false:
    "\<not>(call_local_status(normalize_call_machine machine) = Endpoint_Up \<and>
      call_connection(normalize_call_machine machine) = Authority_Connected \<and>
      map_option fst(call_invocations(normalize_call_machine machine) call_id) = Some command)"
    using False by (simp only: normalized_call_fields HOL.simp_thms)
  have original_wait:
    "original.dispatch_client_call call_id command machine =
      machine\<lparr>call_history := call_history machine @ [Call_Waiting call_id]\<rparr>"
    by (simp only: original.dispatch_client_call_def if_not_P[OF False])
  have reduced_wait:
    "reduced.dispatch_client_call call_id command(normalize_call_machine machine) =
      (normalize_call_machine machine)\<lparr>call_history :=
        call_history(normalize_call_machine machine) @ [Call_Waiting call_id]\<rparr>"
    by (simp only: reduced.dispatch_client_call_def if_not_P[OF reduced_guard_false])
  show ?thesis
    unfolding original_wait reduced_wait
    by (simp add: normalize_call_machine_def)
qed

lemma collect_response_projection:
  "reduced.collect_client_response call_id command(normalize_call_machine machine) =
    normalize_call_machine(original.collect_client_response call_id command machine)"
  by (auto simp: reduced.collect_client_response_def original.collect_client_response_def
      normalize_call_machine_def split: option.splits prod.splits if_splits)

lemma complete_call_projection:
  "reduced.complete_client_call call_id(normalize_call_machine machine) =
    normalize_call_machine(original.complete_client_call call_id machine)"
  by (auto simp: reduced.complete_client_call_def original.complete_client_call_def
      normalize_call_machine_def split: option.splits prod.splits if_splits)

lemma authority_input_projection:
  "reduced.apply_authority_input input(normalize_call_machine machine) =
    normalize_call_machine(original.apply_authority_input input machine)"
  by (simp add: reduced.apply_authority_input_def original.apply_authority_input_def
      normalize_call_machine_def Let_def)

theorem actual_call_step_projection:
  "reduced.call_step action(normalize_call_machine machine) =
    normalize_call_machine(original.call_step action machine)"
proof (cases action)
  case (Begin_Call call_id command)
  then show ?thesis by (simp only: reduced.call_step.simps original.call_step.simps begin_call_projection)
next
  case (Dispatch_Call call_id command)
  then show ?thesis by (simp only: reduced.call_step.simps original.call_step.simps dispatch_call_projection)
next
  case (Collect_Response call_id command)
  then show ?thesis by (simp only: reduced.call_step.simps original.call_step.simps collect_response_projection)
next
  case (Lose_Response call_id)
  then show ?thesis by (simp add: normalize_call_machine_def)
next
  case (Complete_Call call_id)
  then show ?thesis by (simp only: reduced.call_step.simps original.call_step.simps complete_call_projection)
next
  case Crash_Local_Endpoint
  then show ?thesis by (simp add: normalize_call_machine_def)
next
  case Recover_Local_Endpoint
  then show ?thesis by (simp add: normalize_call_machine_def)
next
  case (Set_Authority_Connection connection)
  then show ?thesis by (simp add: normalize_call_machine_def)
next
  case (Apply_Authority_Input input)
  then show ?thesis by (simp only: reduced.call_step.simps original.call_step.simps authority_input_projection)
qed

theorem finite_call_projection:
  "reduced.run_calls actions(normalize_call_machine machine) =
    normalize_call_machine(original.run_calls actions machine)"
  by (induction actions arbitrary: machine)
    (simp_all only: reduced.run_calls.simps original.run_calls.simps actual_call_step_projection)

theorem finite_call_observable_fields:
  "call_authority_log(reduced.run_calls actions(normalize_call_machine machine)) =
    call_authority_log(original.run_calls actions machine)"
  "call_authority_results(reduced.run_calls actions(normalize_call_machine machine)) =
    call_authority_results(original.run_calls actions machine)"
  "call_invocations(reduced.run_calls actions(normalize_call_machine machine)) =
    call_invocations(original.run_calls actions machine)"
  "call_completions(reduced.run_calls actions(normalize_call_machine machine)) =
    call_completions(original.run_calls actions machine)"
  "call_local_results(reduced.run_calls actions(normalize_call_machine machine)) =
    call_local_results(original.run_calls actions machine)"
  "call_local_status(reduced.run_calls actions(normalize_call_machine machine)) =
    call_local_status(original.run_calls actions machine)"
  "call_connection(reduced.run_calls actions(normalize_call_machine machine)) =
    call_connection(original.run_calls actions machine)"
  "call_history(reduced.run_calls actions(normalize_call_machine machine)) =
    call_history(original.run_calls actions machine)"
  by (simp_all only: finite_call_projection normalized_call_fields)

theorem finite_call_authority_state:
  "call_authority_state(reduced.run_calls actions(normalize_call_machine machine)) =
    projection_map(call_authority_state(original.run_calls actions machine))"
  by (simp only: finite_call_projection normalized_call_fields)

theorem generated_calls_projection:
  "reduced.run_calls actions(initial_call_machine(projection_map initial)) =
    normalize_call_machine(original.run_calls actions(initial_call_machine initial))"
  using finite_call_projection[of actions "initial_call_machine initial"] by simp

theorem authority_replay_projection:
  "reduced.replay_call_authority entries(projection_map state) =
    projection_map(original.replay_call_authority entries state)"
proof (induction entries arbitrary: state)
  case Nil
  then show ?case by simp
next
  case (Cons entry entries)
  then show ?case by (cases entry) simp_all
qed

theorem authority_reply_authenticity_projection:
  "reduced.authentic_call_history entries(projection_map state) = original.authentic_call_history entries state"
proof (induction entries arbitrary: state)
  case Nil
  then show ?case by simp
next
  case (Cons entry entries)
  then show ?case by (cases entry) simp_all
qed

lemma original_run_calls_append:
  "original.run_calls(first @ second) machine = original.run_calls second(original.run_calls first machine)"
  by (induction first arbitrary: machine) simp_all

lemma reduced_run_calls_append:
  "reduced.run_calls(first @ second) machine = reduced.run_calls second(reduced.run_calls first machine)"
  by (induction first arbitrary: machine) simp_all

theorem ordered_call_composition_projection:
  "reduced.run_calls second(reduced.run_calls first(normalize_call_machine machine)) =
    normalize_call_machine(original.run_calls(first @ second) machine)"
  by (simp only: finite_call_projection original_run_calls_append)

end

section \<open>Concrete Interpretations for Both Complete Call Languages\<close>

context source_attestation
begin

sublocale observed_history_projection: operational_call_projection
  normalize_observed_history execute_observed execute_observed_environment
proof unfold_locales
  show "\<And>state. normalize_observed_history(normalize_observed_history state) = normalize_observed_history state"
    by simp
  show "\<And>command state. snd(execute_observed command(normalize_observed_history state)) =
      snd(execute_observed command state)"
    by (rule observed_callback_reply_preserved)
  show "\<And>command state. normalize_observed_history(fst(execute_observed command(normalize_observed_history state))) =
      normalize_observed_history(fst(execute_observed command state))"
    by (rule observed_callback_update_preserved)
  show "\<And>input state. snd(execute_observed_environment input(normalize_observed_history state)) =
      snd(execute_observed_environment input state)"
    by (rule observed_environment_reply_preserved)
  show "\<And>input state.
      normalize_observed_history(fst(execute_observed_environment input(normalize_observed_history state))) =
      normalize_observed_history(fst(execute_observed_environment input state))"
    by (rule observed_environment_update_preserved)
qed

sublocale sourced_history_projection: operational_call_projection
  normalize_sourced_history execute_sourced_request execute_sourced_environment
proof unfold_locales
  show "\<And>state. normalize_sourced_history(normalize_sourced_history state) = normalize_sourced_history state"
    by simp
  show "\<And>request state. snd(execute_sourced_request request(normalize_sourced_history state)) =
      snd(execute_sourced_request request state)"
    by (rule sourced_callback_reply_preserved)
  show "\<And>request state. normalize_sourced_history(fst(execute_sourced_request request(normalize_sourced_history state))) =
      normalize_sourced_history(fst(execute_sourced_request request state))"
    by (rule sourced_callback_update_preserved)
  show "\<And>input state. snd(execute_sourced_environment input(normalize_sourced_history state)) =
      snd(execute_sourced_environment input state)"
    by (rule sourced_environment_reply_preserved)
  show "\<And>input state.
      normalize_sourced_history(fst(execute_sourced_environment input(normalize_sourced_history state))) =
      normalize_sourced_history(fst(execute_sourced_environment input state))"
    by (rule sourced_environment_update_preserved)
qed

theorem every_observed_call_word_has_the_same_decisions:
  "observed_history_projection.reduced.run_calls actions
      (observed_history_projection.normalize_call_machine machine) =
    observed_history_projection.normalize_call_machine(observed_calls.run_calls actions machine)"
  by (rule observed_history_projection.finite_call_projection)

theorem every_sourced_call_word_has_the_same_decisions:
  "sourced_history_projection.reduced.run_calls actions
      (sourced_history_projection.normalize_call_machine machine) =
    sourced_history_projection.normalize_call_machine(sourced_calls.run_calls actions machine)"
  by (rule sourced_history_projection.finite_call_projection)

theorem observed_finite_completions_and_history:
  "call_completions(observed_history_projection.reduced.run_calls actions
      (observed_history_projection.normalize_call_machine machine)) =
    call_completions(observed_calls.run_calls actions machine)"
  "call_history(observed_history_projection.reduced.run_calls actions
      (observed_history_projection.normalize_call_machine machine)) =
    call_history(observed_calls.run_calls actions machine)"
  "call_authority_results(observed_history_projection.reduced.run_calls actions
      (observed_history_projection.normalize_call_machine machine)) =
    call_authority_results(observed_calls.run_calls actions machine)"
  by (rule observed_history_projection.finite_call_observable_fields)+

theorem sourced_finite_completions_and_history:
  "call_completions(sourced_history_projection.reduced.run_calls actions
      (sourced_history_projection.normalize_call_machine machine)) =
    call_completions(sourced_calls.run_calls actions machine)"
  "call_history(sourced_history_projection.reduced.run_calls actions
      (sourced_history_projection.normalize_call_machine machine)) =
    call_history(sourced_calls.run_calls actions machine)"
  "call_authority_results(sourced_history_projection.reduced.run_calls actions
      (sourced_history_projection.normalize_call_machine machine)) =
    call_authority_results(sourced_calls.run_calls actions machine)"
  by (rule sourced_history_projection.finite_call_observable_fields)+

text \<open>The full current core, endpoint caches, financial journal, source
  effect history and source-coupling state remain unchanged by the projection.
  Historical query values still originate in the original stored snapshots:
  the projection preserves each query and its readiness test, rather than
  claiming that the normalized snapshot equals the original complete capture.

  The recovery protocol continues to compare the original genesis, complete
  authority entries and complete current replica. A normalized observation
  state is an analysis representation, not a replacement input for that
  full-state comparison. Successful exact recovery can be followed by the
  finite-call projection; the recovery comparison itself is not weakened.\<close>

end

end
