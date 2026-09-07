(* SPDX-License-Identifier: BSD-3-Clause *)
theory Source_Call_Realization
  imports Source_Realization_Link Integration_Transport
    "Evidence_Atomic_Binding.Finality_Progress"
    "Evidence_Atomic_Binding.Sourced_Response_Link"
begin

section \<open>Fresh Identifiers for the Existing Four-Action Call Program\<close>

definition source_call_ready :: "nat \<Rightarrow> nat \<Rightarrow>
  ('state,'command,'reply,'environment) durable_call_machine \<Rightarrow> bool" where
  "source_call_ready namespace next machine \<longleftrightarrow>
    call_local_status machine=Endpoint_Up \<and> call_connection machine=Authority_Connected \<and>
    (\<forall>index\<ge>next. call_invocations machine(namespace,index)=None \<and>
      call_authority_results machine(namespace,index)=None \<and>
      call_completions machine(namespace,index)=None)"

lemma initial_source_call_ready [simp]:
  "source_call_ready namespace next(initial_call_machine initial)"
  by (simp add: source_call_ready_def initial_call_machine_def)

lemma source_call_ready_mono:
  assumes "source_call_ready namespace first machine" "first\<le>second"
  shows "source_call_ready namespace second machine"
  using assms unfolding source_call_ready_def by auto

lemma source_call_ready_fields:
  assumes "source_call_ready namespace next machine"
  shows "call_local_status machine=Endpoint_Up"
    "call_connection machine=Authority_Connected"
    "call_invocations machine(namespace,next)=None"
    "call_authority_results machine(namespace,next)=None"
    "call_completions machine(namespace,next)=None"
  using assms unfolding source_call_ready_def by auto

context durable_call_protocol
begin

lemma primitive_authority_input_keeps_source_call_ready [simp]:
  "source_call_ready namespace next(apply_authority_input input machine)=
    source_call_ready namespace next machine"
  by (simp add: source_call_ready_def apply_authority_input_def Let_def)

lemma authority_input_keeps_source_call_ready [simp]:
  "source_call_ready namespace next(call_step(Apply_Authority_Input input)machine)=
    source_call_ready namespace next machine"
  by (simp add: source_call_ready_def apply_authority_input_def Let_def)

lemma fresh_program_other_identifiers:
  assumes local: "call_local_status machine=Endpoint_Up"
    and connected: "call_connection machine=Authority_Connected"
    and invocation: "call_invocations machine call_id=None"
    and source: "call_authority_results machine call_id=None"
    and incomplete: "call_completions machine call_id=None"
    and other: "other_id\<noteq>call_id"
  shows "call_invocations(run_calls(complete_call_program call_id command)machine)other_id=
      call_invocations machine other_id"
    "call_authority_results(run_calls(complete_call_program call_id command)machine)other_id=
      call_authority_results machine other_id"
    "call_completions(run_calls(complete_call_program call_id command)machine)other_id=
      call_completions machine other_id"
    "call_local_status(run_calls(complete_call_program call_id command)machine)=Endpoint_Up"
    "call_connection(run_calls(complete_call_program call_id command)machine)=Authority_Connected"
  using assms
  by (simp_all add: complete_call_program_def call_definitions Let_def nth_append)

theorem fresh_program_advances_the_identifier_supply:
  assumes ready: "source_call_ready namespace next machine"
  shows "source_call_ready namespace(Suc next)
    (run_calls(complete_call_program(namespace,next)command)machine)"
proof -
  note fields=source_call_ready_fields[OF ready]
  have different: "(namespace,Suc next)\<noteq>(namespace,next)" by simp
  note link=fresh_program_other_identifiers(4,5)[OF fields different, where command=command]
  have tail: "\<forall>index\<ge>Suc next.
    call_invocations(run_calls(complete_call_program(namespace,next)command)machine)(namespace,index)=None \<and>
    call_authority_results(run_calls(complete_call_program(namespace,next)command)machine)(namespace,index)=None \<and>
    call_completions(run_calls(complete_call_program(namespace,next)command)machine)(namespace,index)=None"
  proof (intro allI impI)
    fix index
    assume bound: "Suc next\<le>index"
    have other: "(namespace,index)\<noteq>(namespace,next)" using bound by auto
    have prior: "call_invocations machine(namespace,index)=None \<and>
      call_authority_results machine(namespace,index)=None \<and>
      call_completions machine(namespace,index)=None"
      using ready bound unfolding source_call_ready_def by auto
    show "call_invocations(run_calls(complete_call_program(namespace,next)command)machine)(namespace,index)=None \<and>
      call_authority_results(run_calls(complete_call_program(namespace,next)command)machine)(namespace,index)=None \<and>
      call_completions(run_calls(complete_call_program(namespace,next)command)machine)(namespace,index)=None"
      using fresh_program_other_identifiers(1,2,3)[OF fields other, where command=command] prior by simp
  qed
  show ?thesis using link tail unfolding source_call_ready_def by blast
qed

theorem fresh_program_uses_the_actual_callback:
  assumes ready: "source_call_ready namespace next machine"
  shows "call_completions(run_calls(complete_call_program(namespace,next)command)machine)(namespace,next)=
      Some(snd(execute command(call_authority_state machine)))"
    "call_authority_state(run_calls(complete_call_program(namespace,next)command)machine)=
      fst(execute command(call_authority_state machine))"
  using an_uninterrupted_fresh_call_completes_its_actual_reply
    [OF source_call_ready_fields[OF ready], where command=command] by blast+

end

section \<open>A Constructive Translation of Every Source-Coupling Input\<close>

type_synonym sourced_durable_machine =
  "(sourced_observation_state,sourced_request,sourced_reply,sourced_environment) durable_call_machine"

fun coupling_call_program :: "nat \<Rightarrow> nat \<Rightarrow> source_coupling_action \<Rightarrow>
  (sourced_request,sourced_environment) client_call_action list" where
  "coupling_call_program namespace next(Coupling_Source arrived replied command)=
    [Apply_Authority_Input(Source_Exchange arrived replied command)]"
| "coupling_call_program namespace next(Coupling_Issue available certificate)=
    [Apply_Authority_Input(Source_Receipt_Arrival available certificate)]"
| "coupling_call_program namespace next(Coupling_Environment endpoint context)=
    [Apply_Authority_Input(View_Environment(Replace_Current_Context endpoint context))]"
| "coupling_call_program namespace next(Coupling_Client available command)=
    [Apply_Authority_Input(Set_Source_Availability available)] @
    complete_call_program(namespace,next)(Endpoint_Request(Refresh_Endpoint 0)) @
    complete_call_program(namespace,Suc next)(Endpoint_Request(Execute_Current 0 command))"

fun coupling_call_word :: "nat \<Rightarrow> nat \<Rightarrow> source_coupling_action list \<Rightarrow>
  (sourced_request,sourced_environment) client_call_action list" where
  "coupling_call_word namespace next []=[]"
| "coupling_call_word namespace next(action#rest)=coupling_call_program namespace next action @
    coupling_call_word namespace(next+2)rest"

fun coupling_client_observation :: "source_coupling_reply \<Rightarrow> sourced_reply" where
  "coupling_client_observation(Coupling_Client_Reply reply)=Sourced_Observation(Effect_Reply reply)"
| "coupling_client_observation _=Sourced_Observation Observation_Rejected"

lemma coupling_call_word_append:
  "coupling_call_word namespace next(first@second)=coupling_call_word namespace next first @
    coupling_call_word namespace(next+2*length first)second"
  by (induction first arbitrary:"next") (simp_all add: algebra_simps)

context source_attestation
begin

lemma actual_sourced_refresh_shape:
  "execute_sourced_request(Endpoint_Request(Refresh_Endpoint endpoint))state=
    (state\<lparr>observation_caches:=(observation_caches state)
      (endpoint:=Some(capture_snapshot(coupled_core(observation_source state))))\<rparr>,
      Sourced_Observation Cache_Refreshed)"
  by (simp add: sourced_view_def install_sourced_view_def)

lemma actual_sourced_refresh_is_current:
  "current_cache_valid(sourced_view(fst(execute_sourced_request
    (Endpoint_Request(Refresh_Endpoint endpoint))state)))endpoint"
  by (simp only: actual_sourced_refresh_shape)
    (simp add: sourced_view_def current_cache_valid_def)

theorem current_sourced_effect_has_the_exact_joint_source:
  assumes current: "current_cache_valid(sourced_view state)endpoint"
  shows "observation_source(fst(execute_sourced_request(Endpoint_Request(Execute_Current endpoint command))state))=
      fst(source_coupling_step(Coupling_Client(observation_source_available state)command)(observation_source state))"
    "snd(execute_sourced_request(Endpoint_Request(Execute_Current endpoint command))state)=
      coupling_client_observation(snd(source_coupling_step
        (Coupling_Client(observation_source_available state)command)(observation_source state)))"
  using current
  by (auto simp: sourced_effect_call_def coupling_client_step_def install_sourced_view_def Let_def
      split: if_splits)

lemma actual_source_environment_frames:
  "observation_source(fst(execute_sourced_environment(Source_Exchange arrived replied command)state))=
    fst(source_coupling_step(Coupling_Source arrived replied command)(observation_source state))"
  "observation_source(fst(execute_sourced_environment(Source_Receipt_Arrival available certificate)state))=
    fst(source_coupling_step(Coupling_Issue available certificate)(observation_source state))"
  "observation_source(fst(execute_sourced_environment(View_Environment(Replace_Current_Context endpoint context))state))=
    fst(source_coupling_step(Coupling_Environment endpoint context)(observation_source state))"
  by (simp_all add: install_sourced_view_def Let_def)

theorem translated_client_is_a_fresh_completed_actual_call:
  fixes machine :: sourced_durable_machine
    and namespace "next" :: nat
    and available :: bool
    and command :: client_command
    and after :: sourced_durable_machine
  assumes ready: "source_call_ready namespace next machine"
  defines "after \<equiv> sourced_calls.run_calls
    (coupling_call_program namespace next(Coupling_Client available command))machine"
  shows "source_call_ready namespace(next+2)after"
    "observation_source(call_authority_state after)=
      fst(source_coupling_step(Coupling_Client available command)(observation_source(call_authority_state machine)))"
    "call_completions after(namespace,Suc next)=Some(coupling_client_observation
      (snd(source_coupling_step(Coupling_Client available command)(observation_source(call_authority_state machine)))))"
proof -
  let ?prepared="sourced_calls.call_step(Apply_Authority_Input(Set_Source_Availability available))machine"
  let ?refreshed="sourced_calls.run_calls
    (complete_call_program(namespace,next)(Endpoint_Request(Refresh_Endpoint 0)))?prepared"
  let ?finished="sourced_calls.run_calls
    (complete_call_program(namespace,Suc next)(Endpoint_Request(Execute_Current 0 command)))?refreshed"
  have prepared_ready: "source_call_ready namespace next ?prepared"
    using ready by simp
  have prepared_state: "call_authority_state ?prepared=
    (call_authority_state machine)\<lparr>observation_source_available:=available\<rparr>"
    by (simp add: sourced_calls.apply_authority_input_def Let_def)
  have refreshed_ready: "source_call_ready namespace(Suc next)?refreshed"
    by (rule sourced_calls.fresh_program_advances_the_identifier_supply[OF prepared_ready])
  have refreshed_state: "call_authority_state ?refreshed=
    fst(execute_sourced_request(Endpoint_Request(Refresh_Endpoint 0))(call_authority_state ?prepared))"
    by (rule sourced_calls.fresh_program_uses_the_actual_callback(2)[OF prepared_ready])
  have current: "current_cache_valid(sourced_view(call_authority_state ?refreshed))0"
    by (simp only: refreshed_state actual_sourced_refresh_is_current)
  have source_before: "observation_source(call_authority_state ?refreshed)=
    observation_source(call_authority_state machine)"
    by (simp only: refreshed_state actual_sourced_refresh_shape prepared_state; simp)
  have availability: "observation_source_available(call_authority_state ?refreshed)=available"
  proof -
    have transport: "observation_source_available(call_authority_state ?refreshed)=
        observation_source_available(fst(execute_sourced_request(Endpoint_Request(Refresh_Endpoint 0))
          (call_authority_state ?prepared)))"
      by (rule arg_cong[where f=observation_source_available, OF refreshed_state])
    have refreshed_availability: "observation_source_available(fst(execute_sourced_request(Endpoint_Request(Refresh_Endpoint 0))
        (call_authority_state ?prepared)))=available"
      by (simp only: actual_sourced_refresh_shape prepared_state; simp)
    show ?thesis by (rule trans[OF transport refreshed_availability])
  qed
  have finished_ready: "source_call_ready namespace(Suc(Suc next))?finished"
    by (rule sourced_calls.fresh_program_advances_the_identifier_supply[OF refreshed_ready])
  note completed=sourced_calls.fresh_program_uses_the_actual_callback[OF refreshed_ready,
    where command="Endpoint_Request(Execute_Current 0 command)"]
  have after_shape: "after=?finished"
    by (simp add: after_def sourced_calls.run_calls_append)
  show "source_call_ready namespace(next+2)after"
    using finished_ready by (simp add: after_shape numeral_2_eq_2)
  show "observation_source(call_authority_state after)=
      fst(source_coupling_step(Coupling_Client available command)(observation_source(call_authority_state machine)))"
    by (simp only: after_shape completed(2) current_sourced_effect_has_the_exact_joint_source(1)[OF current]
      source_before availability)
  show "call_completions after(namespace,Suc next)=Some(coupling_client_observation
      (snd(source_coupling_step(Coupling_Client available command)(observation_source(call_authority_state machine)))))"
    by (simp only: after_shape completed(1) current_sourced_effect_has_the_exact_joint_source(2)[OF current]
      source_before availability)
qed

theorem translated_action_preserves_readiness_and_source:
  fixes machine :: sourced_durable_machine
  assumes ready: "source_call_ready namespace next machine"
  shows "source_call_ready namespace(next+2)(sourced_calls.run_calls(coupling_call_program namespace next action)machine)"
    "observation_source(call_authority_state(sourced_calls.run_calls(coupling_call_program namespace next action)machine))=
      fst(source_coupling_step action(observation_source(call_authority_state machine)))"
proof -
  have advanced: "source_call_ready namespace(Suc(Suc next))machine"
    by (rule source_call_ready_mono[OF ready]) simp
  show "source_call_ready namespace(next+2)(sourced_calls.run_calls(coupling_call_program namespace next action)machine)"
  proof (cases action)
    case (Coupling_Client available command)
    then show ?thesis
      by (simp only: Coupling_Client translated_client_is_a_fresh_completed_actual_call(1)[OF ready])
  qed (simp_all add: advanced)
  show "observation_source(call_authority_state(sourced_calls.run_calls(coupling_call_program namespace next action)machine))=
      fst(source_coupling_step action(observation_source(call_authority_state machine)))"
  proof (cases action)
    case (Coupling_Client available command)
    then show ?thesis
      by (simp only: Coupling_Client translated_client_is_a_fresh_completed_actual_call(2)[OF ready])
  qed (simp_all add: sourced_calls.apply_authority_input_def actual_source_environment_frames
      install_sourced_view_def Let_def)
qed

theorem translated_finite_word_has_the_exact_joint_source:
  fixes machine :: sourced_durable_machine
  assumes ready: "source_call_ready namespace next machine"
  shows "source_call_ready namespace(next+2*length actions)
      (sourced_calls.run_calls(coupling_call_word namespace next actions)machine) \<and>
    observation_source(call_authority_state(sourced_calls.run_calls(coupling_call_word namespace next actions)machine))=
      run_source_coupling actions(observation_source(call_authority_state machine))"
  using ready
proof (induction actions arbitrary:"next" machine)
  case Nil
  then show ?case by simp
next
  case (Cons action actions)
  let ?step="sourced_calls.run_calls(coupling_call_program namespace next action)machine"
  note step=translated_action_preserves_readiness_and_source[OF Cons.prems, where action=action]
  note tail=Cons.IH[OF step(1)]
  show ?case using tail step(2)
    by (simp add: sourced_calls.run_calls_append algebra_simps)
qed

theorem every_translated_client_cut_has_its_actual_completed_reply:
  fixes machine :: sourced_durable_machine
  assumes ready: "source_call_ready namespace next machine"
  shows "call_completions(sourced_calls.run_calls
      (coupling_call_word namespace next(prefix@Coupling_Client available command#suffix))machine)
      (namespace,Suc(next+2*length prefix))=
    Some(coupling_client_observation(snd(source_coupling_step(Coupling_Client available command)
      (run_source_coupling prefix(observation_source(call_authority_state machine))))))"
proof -
  let ?index="next+2*length prefix"
  let ?prefix="sourced_calls.run_calls(coupling_call_word namespace next prefix)machine"
  let ?client="sourced_calls.run_calls(coupling_call_program namespace ?index(Coupling_Client available command))?prefix"
  have prefix_ready: "source_call_ready namespace ?index ?prefix"
    and prefix_source: "observation_source(call_authority_state ?prefix)=
      run_source_coupling prefix(observation_source(call_authority_state machine))"
    using translated_finite_word_has_the_exact_joint_source[OF ready, where actions=prefix] by blast+
  have completed: "call_completions ?client(namespace,Suc ?index)=
    Some(coupling_client_observation(snd(source_coupling_step(Coupling_Client available command)
      (run_source_coupling prefix(observation_source(call_authority_state machine))))))"
    using translated_client_is_a_fresh_completed_actual_call(3)[OF prefix_ready,
      where available=available and command=command] by (simp only: prefix_source)
  have retained: "call_completions(sourced_calls.run_calls(coupling_call_word namespace(?index+2)suffix)?client)
    (namespace,Suc ?index)=Some(coupling_client_observation(snd(source_coupling_step(Coupling_Client available command)
      (run_source_coupling prefix(observation_source(call_authority_state machine))))))"
    by (rule sourced_completed_replies_survive_finite_continuations[OF completed])
  show ?thesis using retained
    by (simp only: coupling_call_word_append coupling_call_word.simps sourced_calls.run_calls_append)
qed

theorem generated_translation_has_exact_current_recovery:
  fixes namespace "next" :: nat
    and actions :: "source_coupling_action list"
    and balances :: "source_account \<Rightarrow> nat"
    and regulatory :: global_state
    and contexts :: "nat \<Rightarrow> lock_context"
    and machine :: sourced_durable_machine
  defines "machine \<equiv> sourced_calls.run_calls(coupling_call_word namespace next actions)
    (initial_call_machine(initial_sourced_observations balances regulatory contexts))"
  shows "sourced_calls.checked_current_replay machine(current_source_candidate machine)=
    Some(call_authority_state machine)"
  unfolding machine_def
  by (rule sourced_calls.generated_source_supplies_recovery_without_a_truth_flag)

theorem generated_translation_transports_recovery_and_future_replies:
  fixes namespace "next" :: nat
    and actions :: "source_coupling_action list"
    and balances :: "source_account \<Rightarrow> nat"
    and regulatory :: global_state
    and contexts :: "nat \<Rightarrow> lock_context"
    and machine :: sourced_durable_machine
    and runtime :: "(sourced_observation_state,sourced_request,sourced_reply,sourced_environment) recovered_call_runtime"
    and candidate :: "(sourced_observation_state,sourced_request,sourced_reply,sourced_environment) recovery_candidate"
    and future :: "(sourced_request,sourced_environment) client_call_action list"
    and call_id :: client_call_id
    and request :: sourced_request
  defines "machine \<equiv> sourced_calls.run_calls(coupling_call_word namespace next actions)
    (initial_call_machine(initial_sourced_observations balances regulatory contexts))"
    and "runtime \<equiv> \<lparr>recovery_source=machine,recovery_replica=None,recovery_connected=True\<rparr>"
    and "candidate \<equiv> current_source_candidate machine"
  shows "call_completions(sourced_history_projection.reduced.run_calls future
      (sourced_history_projection.normalize_call_machine(recovery_source
        (sourced_calls.dispatch_from_recovered_replica call_id request
          (sourced_calls.restore_current_replica candidate runtime)))))=
    call_completions(sourced_calls.run_calls future(sourced_calls.dispatch_client_call call_id request machine))"
    "call_history(sourced_history_projection.reduced.run_calls future
      (sourced_history_projection.normalize_call_machine(recovery_source
        (sourced_calls.dispatch_from_recovered_replica call_id request
          (sourced_calls.restore_current_replica candidate runtime)))))=
    call_history(sourced_calls.run_calls future(sourced_calls.dispatch_client_call call_id request machine))"
proof -
  have contract: "sourced_calls.authority_replay_contract machine"
    using sourced_calls.generated_call_contracts
      [of "coupling_call_word namespace next actions" "initial_sourced_observations balances regulatory contexts"]
    by (simp add: machine_def)
  have decoded: "sourced_calls.checked_current_replay machine candidate=Some(call_authority_state machine)"
    unfolding candidate_def by (rule sourced_calls.actual_source_produces_a_valid_complete_candidate[OF contract])
  have runtime_contract: "sourced_calls.authority_replay_contract(recovery_source runtime)"
    and connected: "recovery_connected runtime"
    and restored: "sourced_calls.checked_current_replay(recovery_source runtime)candidate=Some(call_authority_state machine)"
    using contract decoded by (simp_all add: runtime_def)
  show "call_completions(sourced_history_projection.reduced.run_calls future
      (sourced_history_projection.normalize_call_machine(recovery_source
        (sourced_calls.dispatch_from_recovered_replica call_id request
          (sourced_calls.restore_current_replica candidate runtime)))))=
    call_completions(sourced_calls.run_calls future(sourced_calls.dispatch_client_call call_id request machine))"
    using sourced_history_projection.restored_runtime_preserves_all_future_completed_replies(1)
      [OF runtime_contract connected restored, where actions=future and call_id=call_id and command=request]
    by (simp add: runtime_def)
  show "call_history(sourced_history_projection.reduced.run_calls future
      (sourced_history_projection.normalize_call_machine(recovery_source
        (sourced_calls.dispatch_from_recovered_replica call_id request
          (sourced_calls.restore_current_replica candidate runtime)))))=
    call_history(sourced_calls.run_calls future(sourced_calls.dispatch_client_call call_id request machine))"
    using sourced_history_projection.restored_runtime_preserves_all_future_completed_replies(2)
      [OF runtime_contract connected restored, where actions=future and call_id=call_id and command=request]
    by (simp add: runtime_def)
qed

end

section \<open>The Actual Two-Root Value Flow Ends in a Durable Completed Reply\<close>

definition realization_call_prefix :: "source_coupling_action list" where
  "realization_call_prefix=realization_credit_word 17 @ realization_credit_word 23 @
    source_realization_word(linked_certificate 17)0 realization_seed_effect"

definition realization_call_actions :: "source_coupling_action list" where
  "realization_call_actions=realization_call_prefix @
    source_realization_words realization_certificates(\<lambda>_.0)realization_exchange_effects"

definition realization_call_initial :: sourced_durable_machine where
  "realization_call_initial=initial_call_machine
    (initial_sourced_observations sample_balances(sample_metadata ACTIVE)conservation_contexts)"

definition realization_durable_calls :: sourced_durable_machine where
  "realization_durable_calls=realized.sourced_calls.run_calls(coupling_call_word 91 0 realization_call_actions)
    realization_call_initial"

lemma realization_call_initial_source:
  "observation_source(call_authority_state realization_call_initial)=conservation_initial"
  "source_call_ready 91 0 realization_call_initial"
proof -
  show "observation_source(call_authority_state realization_call_initial)=conservation_initial"
    by (simp add: realization_call_initial_def initial_call_machine_def
      initial_sourced_observations_def conservation_initial_def Let_def)
  show "source_call_ready 91 0 realization_call_initial"
    unfolding realization_call_initial_def by (rule initial_source_call_ready)
qed

lemma realization_call_prefix_is_the_actual_lineage_seed:
  "realized.run_source_coupling realization_call_prefix conservation_initial=realization_lineage_seed"
  by (simp add: realization_call_prefix_def realization_lineage_seed_def
    realization_source_second_def realization_source_first_def realized.progress_source_run_append)

lemma realization_call_word_is_the_actual_exchange:
  "realized.run_source_coupling realization_call_actions conservation_initial=realization_exchange_finished"
  by (simp add: realization_call_actions_def realized.progress_source_run_append
    realization_call_prefix_is_the_actual_lineage_seed realization_exchange_finished_def)

theorem actual_durable_calls_have_the_realized_joint_source:
  "observation_source(call_authority_state realization_durable_calls)=realization_exchange_finished"
  using realized.translated_finite_word_has_the_exact_joint_source
    [OF realization_call_initial_source(2), where actions=realization_call_actions]
  by (simp add: realization_durable_calls_def realization_call_initial_source(1)
    realization_call_word_is_the_actual_exchange)

theorem actual_durable_calls_have_the_constructed_funding:
  "\<forall>root\<in>set[sample_binding 17,sample_binding 23]. \<forall>holder\<in>set[3,4].
    realization_units(core_parent(coupled_core(observation_source(call_authority_state realization_durable_calls))))
      root holder=realization_exchange_target root holder"
  using actual_two_root_plan_activates_every_source_dispatch
  unfolding actual_durable_calls_have_the_realized_joint_source by blast

definition realization_last_effect :: descendant_effect where
  "realization_last_effect=realization_effect(sample_binding 23)3 4 5"

definition realization_last_command :: client_command where
  "realization_last_command=Client_Protocol(binding_destination(lineage_root realization_last_effect))0
    (source_realization_intent(realization_certificates(lineage_root realization_last_effect))realization_last_effect)"

definition realization_before_last_call :: "source_coupling_action list" where
  "realization_before_last_call=realization_call_prefix @
    source_realization_word(realization_certificates(sample_binding 17))0
      (realization_effect(sample_binding 17)4 3 5) @
    [Coupling_Environment(binding_destination(lineage_root realization_last_effect))
      (source_realization_context realization_last_effect)]"

definition realization_last_call_id :: client_call_id where
  "realization_last_call_id=(91,Suc(2*length realization_before_last_call))"

lemma realization_call_word_last_client:
  "realization_call_actions=realization_before_last_call@[Coupling_Client True realization_last_command]"
  by (simp add: realization_call_actions_def realization_before_last_call_def realization_last_command_def
    realization_exchange_effects_def realization_last_effect_def realization_effect_def
    source_realization_word_def append_assoc)

lemma realization_last_client_is_an_actual_success:
  "realized.source_coupling_step(Coupling_Client True realization_last_command)
      (realized.run_source_coupling realization_before_last_call conservation_initial) =
    (realization_exchange_finished,Coupling_Client_Reply(Protocol_Response Descendant_Executed))"
proof -
  have all_replies: "\<forall>i<length realization_exchange_effects.
    realized.source_realization_reply realization_certificates(\<lambda>_.0)(realization_exchange_effects!i)
      (realized.run_source_coupling(source_realization_words realization_certificates(\<lambda>_.0)
        (take i realization_exchange_effects))realization_lineage_seed)=
    Coupling_Client_Reply(Protocol_Response Descendant_Executed)"
    using actual_two_root_plan_activates_every_source_dispatch by blast
  have index_bound: "1<length realization_exchange_effects"
    by (simp add: realization_exchange_effects_def)
  have indexed: "realized.source_realization_reply realization_certificates(\<lambda>_.0)
      (realization_exchange_effects!1)
      (realized.run_source_coupling(source_realization_words realization_certificates(\<lambda>_.0)
        (take 1 realization_exchange_effects))realization_lineage_seed)=
    Coupling_Client_Reply(Protocol_Response Descendant_Executed)"
    by (rule all_replies[rule_format, OF index_bound])
  have reply: "snd(realized.source_coupling_step(Coupling_Client True realization_last_command)
      (realized.run_source_coupling realization_before_last_call conservation_initial))=
    Coupling_Client_Reply(Protocol_Response Descendant_Executed)"
    using indexed
    by (simp add: realized.source_realization_reply_def realization_before_last_call_def
      realized.progress_source_run_append realization_call_prefix_is_the_actual_lineage_seed
      realization_exchange_effects_def realization_last_effect_def realization_last_command_def
      realized.source_realization_installed_def realization_effect_def)
  have state: "fst(realized.source_coupling_step(Coupling_Client True realization_last_command)
      (realized.run_source_coupling realization_before_last_call conservation_initial))=realization_exchange_finished"
    using realization_call_word_is_the_actual_exchange
    by (simp only: realization_call_word_last_client realized.progress_source_run_append
      realized.run_source_coupling.simps)
  show ?thesis using state reply by (cases "realized.source_coupling_step(Coupling_Client True realization_last_command)
    (realized.run_source_coupling realization_before_last_call conservation_initial)") simp
qed

theorem actual_two_root_source_to_completed_descendant_reply:
  "call_completions realization_durable_calls realization_last_call_id=
    Some(Sourced_Observation(Effect_Reply(Protocol_Response Descendant_Executed)))"
  using realized.every_translated_client_cut_has_its_actual_completed_reply
    [OF realization_call_initial_source(2), where prefix=realization_before_last_call and suffix="[]"
      and available=True and command=realization_last_command]
  by (simp only: realization_durable_calls_def realization_call_word_last_client realization_last_call_id_def
    realization_call_initial_source(1) realization_last_client_is_an_actual_success snd_conv
    coupling_client_observation.simps; simp)

definition realization_call_recovery where
  "realization_call_recovery=\<lparr>recovery_source=realization_durable_calls,
    recovery_replica=None,recovery_connected=True\<rparr>"

theorem actual_two_root_durable_source_recovers_exactly:
  "realized.sourced_calls.checked_current_replay realization_durable_calls
    (current_source_candidate realization_durable_calls)=Some(call_authority_state realization_durable_calls)"
  unfolding realization_durable_calls_def realization_call_initial_def
  by (rule realized.sourced_calls.generated_source_supplies_recovery_without_a_truth_flag)

theorem actual_recovery_restores_a_replica_of_the_existing_machine:
  "recovery_replica(realized.sourced_calls.restore_current_replica
      (current_source_candidate realization_durable_calls)realization_call_recovery)=
    Some(call_authority_state realization_durable_calls)"
  "recovery_source(realized.sourced_calls.restore_current_replica
      (current_source_candidate realization_durable_calls)realization_call_recovery)=realization_durable_calls"
  by (simp_all add: realization_call_recovery_def realized.sourced_calls.restore_current_replica_def
    actual_two_root_durable_source_recovers_exactly)

theorem actual_two_root_recovery_keeps_future_completed_replies:
  "call_completions(realized.sourced_history_projection.reduced.run_calls future
      (realized.sourced_history_projection.normalize_call_machine(recovery_source
        (realized.sourced_calls.dispatch_from_recovered_replica realization_last_call_id
          (Endpoint_Request(Execute_Current 0 realization_last_command))
          (realized.sourced_calls.restore_current_replica(current_source_candidate realization_durable_calls)
            realization_call_recovery)))))=
    call_completions(realized.sourced_calls.run_calls future
      (realized.sourced_calls.dispatch_client_call realization_last_call_id
        (Endpoint_Request(Execute_Current 0 realization_last_command))realization_durable_calls))"
  using realized.generated_translation_transports_recovery_and_future_replies(1)
    [where namespace=91 and ?next=0 and actions=realization_call_actions
      and balances=sample_balances and regulatory="sample_metadata ACTIVE" and contexts=conservation_contexts
      and future=future and call_id=realization_last_call_id
      and request="Endpoint_Request(Execute_Current 0 realization_last_command)"]
  by (simp only: realization_durable_calls_def realization_call_initial_def realization_call_recovery_def)

theorem recovered_value_flow_retains_its_completed_descendant:
  "call_completions(realized.sourced_history_projection.reduced.run_calls future
      (realized.sourced_history_projection.normalize_call_machine(recovery_source
        (realized.sourced_calls.dispatch_from_recovered_replica realization_last_call_id
          (Endpoint_Request(Execute_Current 0 realization_last_command))
          (realized.sourced_calls.restore_current_replica(current_source_candidate realization_durable_calls)
            realization_call_recovery)))))realization_last_call_id=
    Some(Sourced_Observation(Effect_Reply(Protocol_Response Descendant_Executed)))"
proof -
  have dispatched: "call_completions(realized.sourced_calls.dispatch_client_call realization_last_call_id
      (Endpoint_Request(Execute_Current 0 realization_last_command))realization_durable_calls)
      realization_last_call_id=Some(Sourced_Observation(Effect_Reply(Protocol_Response Descendant_Executed)))"
    using realized.sourced_completion_survives_every_step[OF actual_two_root_source_to_completed_descendant_reply,
      where action="Dispatch_Call realization_last_call_id(Endpoint_Request(Execute_Current 0 realization_last_command))"]
    by simp
  have continued: "call_completions(realized.sourced_calls.run_calls future
      (realized.sourced_calls.dispatch_client_call realization_last_call_id
        (Endpoint_Request(Execute_Current 0 realization_last_command))realization_durable_calls))
      realization_last_call_id=Some(Sourced_Observation(Effect_Reply(Protocol_Response Descendant_Executed)))"
    by (rule realized.sourced_completed_replies_survive_finite_continuations[OF dispatched])
  show ?thesis using continued
    by (simp only: actual_two_root_recovery_keeps_future_completed_replies)
qed

text \<open>The translation reserves two identifiers per coupling input in one
  namespace. Every client input first sets the explicit source-availability
  input, completes an actual full-cache refresh, and completes the unchanged
  command through Execute Current. Environmental source attempts, receipt
  arrivals and context updates use the actual authority-input path. A rejected
  coupling client is a completed rejected observation with the same source
  state; the construction does not assume all commands succeed.

  The concrete instance begins at the actual sourced genesis and contains the
  two source debits, source-produced receipts, terminal records, credits and
  primary publications before the lineage and constructive exchange. Recovery
  receives this same generated authority machine, including its identifiers,
  exact log and stored results. It restores and dispatches against the original
  current-source comparison before the historical projection is applied to
  future calls. Physical-source control, authentication and durable execution
  retain their existing conditional implementation boundary.\<close>

end
