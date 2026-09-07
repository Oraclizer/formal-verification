(* SPDX-License-Identifier: BSD-3-Clause *)
theory Sourced_Call_Order
  imports Sourced_Observations
begin

section \<open>The Revision of the Actual Source-Aware Callbacks\<close>

definition sourced_call_revision :: "sourced_observation_state \<Rightarrow> nat" where
  "sourced_call_revision state=core_epoch(coupled_core(observation_source state))"

lemma sourced_view_revision_for_calls:
  "core_epoch(observed_core(sourced_view state))=sourced_call_revision state"
  by (simp add: sourced_view_def sourced_call_revision_def)

lemma installed_source_revision_for_calls:
  "sourced_call_revision(install_sourced_view provider view state)=core_epoch(coupled_core provider)"
  by (simp add: install_sourced_view_def sourced_call_revision_def)

context source_attestation
begin

lemma coupling_source_core_frame_for_calls:
  "coupled_core(fst(coupling_source_result arrived replied command provider))=coupled_core provider"
  by (auto simp: coupling_source_result_def Let_def split: option.splits if_splits)

lemma coupling_receipt_core_frame_for_calls:
  "coupled_core(fst(coupling_issue_result available certificate provider))=coupled_core provider"
  by (simp add: coupling_issue_result_def Let_def)

lemma coupling_client_revision_for_calls:
  "core_epoch(coupled_core provider)\<le>
    core_epoch(coupled_core(fst(coupling_client_step available command provider)))"
proof (cases "coupling_guard available provider command")
  case False
  then show ?thesis by (simp add: coupling_client_step_def)
next
  case True
  have actual: "coupling_client_result command provider=
    execute_finality_client command(coupled_core provider)"
    by (rule guarded_client_is_the_actual_child[OF True])
  show ?thesis
    by (simp add: coupling_client_step_def True actual execute_finality_client_def Let_def)
qed

lemma coupling_step_revision_for_calls:
  "core_epoch(coupled_core provider)\<le>
    core_epoch(coupled_core(fst(source_coupling_step action provider)))"
proof (cases action)
  case (Coupling_Client available command)
  then show ?thesis
    by (simp only: Coupling_Client source_coupling_step.simps coupling_client_revision_for_calls)
qed (auto simp: coupling_source_core_frame_for_calls coupling_receipt_core_frame_for_calls
  execute_finality_environment_def Let_def split: option.splits if_splits)

lemma sourced_effect_revision_for_calls:
  "sourced_call_revision state\<le>
    sourced_call_revision(fst(sourced_effect_call endpoint command state))"
  by (auto simp: sourced_effect_call_def sourced_call_revision_def install_sourced_view_def Let_def
      intro: coupling_step_revision_for_calls coupling_client_revision_for_calls
      split: if_splits source_coupling_reply.splits)

lemma sourced_effect_never_returns_current_for_calls:
  "snd(sourced_effect_call endpoint command state)\<noteq>
    Sourced_Observation(Current_Value revision payload)"
  by (auto simp: sourced_effect_call_def Let_def split: if_splits source_coupling_reply.splits)

lemma sourced_application_revision_for_calls:
  "sourced_call_revision state\<le>
    sourced_call_revision(fst(sourced_application_read endpoint index request asset state))"
  by (auto simp: sourced_application_read_def sourced_call_revision_def install_sourced_view_def Let_def
      intro: coupling_step_revision_for_calls coupling_client_revision_for_calls
      split: if_splits observed_reply.splits source_coupling_reply.splits
        finality_reply.splits reservation_reply.splits)

lemma sourced_application_current_origin_for_calls:
  assumes "snd(sourced_application_read endpoint index request asset state)=
    Sourced_Observation(Current_Value revision payload)"
  shows "protected_read_access endpoint index request(Application_Value asset)(sourced_view state) \<and>
    current_query_reply endpoint(Application_Value asset)(sourced_view state)=Current_Value revision payload"
  using assms
  by (auto simp: sourced_application_read_def Let_def
      split: if_splits observed_reply.splits source_coupling_reply.splits
        finality_reply.splits reservation_reply.splits)

lemma sourced_query_reply_revision_for_calls:
  assumes "current_query_reply endpoint query(sourced_view state)=Current_Value revision payload"
  shows "revision=sourced_call_revision state"
  using assms
  by (auto simp: current_query_reply_def current_cache_valid_def capture_snapshot_def
      sourced_view_def sourced_call_revision_def split: option.splits if_splits)

lemma sourced_application_current_revision_for_calls:
  assumes "snd(sourced_application_read endpoint index request asset state)=
    Sourced_Observation(Current_Value revision payload)"
  shows "revision=sourced_call_revision state"
proof -
  have actual: "current_query_reply endpoint(Application_Value asset)(sourced_view state)=
    Current_Value revision payload"
    using sourced_application_current_origin_for_calls[OF assms] by blast
  show ?thesis by (rule sourced_query_reply_revision_for_calls[OF actual])
qed

lemma sourced_endpoint_cases_for_calls:
  "(\<exists>endpoint client. command=Execute_Current endpoint client \<and>
      execute_sourced_endpoint command state=sourced_effect_call endpoint client state) \<or>
    (\<exists>endpoint index request asset.
      command=Read_Protected_Current endpoint index request(Application_Value asset) \<and>
      execute_sourced_endpoint command state=sourced_application_read endpoint index request asset state) \<or>
    (observation_source(fst(execute_sourced_endpoint command state))=observation_source state \<and>
      snd(execute_sourced_endpoint command state)=
        Sourced_Observation(snd(execute_observed command(sourced_view state))))"
proof (cases command)
  case (Read_Protected_Current endpoint index request query)
  then show ?thesis
    by (cases query) (auto simp: install_sourced_view_def Let_def)
qed (auto simp: install_sourced_view_def Let_def)

lemma sourced_endpoint_revision_nondecreasing_for_calls:
  "sourced_call_revision state\<le>
    sourced_call_revision(fst(execute_sourced_endpoint command state))"
proof -
  consider (effect) endpoint client where
      "execute_sourced_endpoint command state=sourced_effect_call endpoint client state"
    | (application) endpoint index request asset where
      "execute_sourced_endpoint command state=sourced_application_read endpoint index request asset state"
    | (pure) "observation_source(fst(execute_sourced_endpoint command state))=observation_source state"
    using sourced_endpoint_cases_for_calls[of command state] by blast
  then show ?thesis
  proof cases
    case (effect endpoint client)
    show ?thesis by (simp only: effect sourced_effect_revision_for_calls)
  next
    case (application endpoint index request asset)
    show ?thesis by (simp only: application sourced_application_revision_for_calls)
  next
    case pure
    then show ?thesis by (simp add: sourced_call_revision_def)
  qed
qed

lemma sourced_endpoint_current_revision_for_calls:
  assumes success: "snd(execute_sourced_endpoint command state)=
    Sourced_Observation(Current_Value revision payload)"
  shows "revision=sourced_call_revision state"
proof -
  consider (effect) endpoint client where
      "execute_sourced_endpoint command state=sourced_effect_call endpoint client state"
    | (application) endpoint index request asset where
      "execute_sourced_endpoint command state=sourced_application_read endpoint index request asset state"
    | (pure) "snd(execute_sourced_endpoint command state)=
        Sourced_Observation(snd(execute_observed command(sourced_view state)))"
    using sourced_endpoint_cases_for_calls[of command state] by blast
  then show ?thesis
  proof cases
    case (effect endpoint client)
    have actual: "snd(sourced_effect_call endpoint client state)=
      Sourced_Observation(Current_Value revision payload)"
      using success by (simp only: effect)
    show ?thesis using actual sourced_effect_never_returns_current_for_calls by blast
  next
    case (application endpoint index request asset)
    have actual: "snd(sourced_application_read endpoint index request asset state)=
      Sourced_Observation(Current_Value revision payload)"
      using success by (simp only: application)
    show ?thesis by (rule sourced_application_current_revision_for_calls[OF actual])
  next
    case pure
    have actual: "snd(execute_observed command(sourced_view state))=Current_Value revision payload"
      using pure success by simp
    have "revision=core_epoch(observed_core(sourced_view state))"
      by (rule any_current_reply_has_actual_revision[OF actual])
    then show ?thesis by (simp only: sourced_view_revision_for_calls)
  qed
qed

theorem sourced_request_current_revision_for_calls:
  assumes "snd(execute_sourced_request request state)=Sourced_Observation(Current_Value revision payload)"
  shows "revision=sourced_call_revision state"
  using assms
  by (cases request)
    (auto dest: sourced_endpoint_current_revision_for_calls split: option.splits if_splits)

theorem sourced_request_revision_nondecreasing_for_calls:
  "sourced_call_revision state\<le>sourced_call_revision(fst(execute_sourced_request request state))"
  by (cases request)
    (auto intro: sourced_endpoint_revision_nondecreasing_for_calls split: option.splits if_splits)

theorem sourced_environment_revision_nondecreasing_for_calls:
  "sourced_call_revision state\<le>sourced_call_revision(fst(execute_sourced_environment input state))"
proof (cases input)
  case (View_Environment environment)
  then show ?thesis
    by (cases environment)
      (auto simp: sourced_call_revision_def install_sourced_view_def Let_def
        execute_finality_environment_def
        intro: coupling_step_revision_for_calls split: source_coupling_reply.splits)
qed (auto simp: sourced_call_revision_def Let_def
  coupling_source_core_frame_for_calls coupling_receipt_core_frame_for_calls
  intro: coupling_step_revision_for_calls)

theorem current_source_guards_are_retained_for_calls:
  assumes query: "current_source_query command=Some account"
    and success: "snd(execute_sourced_request(Endpoint_Request command)state)=
      Sourced_Observation(Current_Value revision payload)"
  shows "observation_source_available state \<and>
    source_view_is_reconciled(observation_source state)account"
  using query success by (auto split: if_splits)

sublocale sourced_order: revision_ordered_calls execute_sourced_request execute_sourced_environment
  sourced_call_revision
  by unfold_locales
    (rule sourced_request_revision_nondecreasing_for_calls,
     rule sourced_environment_revision_nondecreasing_for_calls)

section \<open>Source-Aware Results and Nonoverlapping Calls\<close>

lemma sourced_cached_current_revision_upper:
  assumes cache: "authority_cache_contract machine"
    and replay: "sourced_calls.authority_replay_contract machine"
    and found: "call_authority_results machine call_id=
      Some(request,Sourced_Observation(Current_Value revision payload),index)"
  shows "revision\<le>sourced_call_revision(call_authority_state machine)"
proof -
  have actual: "Sourced_Observation(Current_Value revision payload)=
    snd(execute_sourced_request request(sourced_calls.replay_call_authority
      (take index(call_authority_log machine))(call_genesis machine)))"
    by (rule sourced_calls.cached_result_is_the_actual_indexed_reply[OF cache replay found])
  have issued: "revision=sourced_call_revision(sourced_calls.replay_call_authority
    (take index(call_authority_log machine))(call_genesis machine))"
    by (rule sourced_request_current_revision_for_calls[OF actual[symmetric]])
  have ordered: "sourced_call_revision(sourced_calls.replay_call_authority
      (take index(call_authority_log machine))(call_genesis machine))\<le>
    sourced_call_revision(sourced_calls.replay_call_authority(call_authority_log machine)(call_genesis machine))"
    by (rule sourced_order.authority_prefix_revision_le)
  show ?thesis using ordered replay
    by (simp add: issued sourced_calls.authority_replay_contract_def)
qed

lemma sourced_fresh_current_revision_lower:
  assumes initial_replay: "sourced_calls.authority_replay_contract machine"
    and final_cache: "authority_cache_contract(sourced_calls.run_calls actions machine)"
    and final_replay: "sourced_calls.authority_replay_contract(sourced_calls.run_calls actions machine)"
    and missing: "call_authority_results machine call_id=None"
    and found: "call_authority_results(sourced_calls.run_calls actions machine)call_id=
      Some(request,Sourced_Observation(Current_Value revision payload),index)"
  shows "sourced_call_revision(call_authority_state machine)\<le>revision"
proof -
  have actual: "Sourced_Observation(Current_Value revision payload)=
    snd(execute_sourced_request request(sourced_calls.replay_call_authority
      (take index(call_authority_log(sourced_calls.run_calls actions machine)))
      (call_genesis(sourced_calls.run_calls actions machine))))"
    by (rule sourced_calls.cached_result_is_the_actual_indexed_reply[OF final_cache final_replay found])
  have issued: "revision=sourced_call_revision(sourced_calls.replay_call_authority
    (take index(call_authority_log(sourced_calls.run_calls actions machine)))
    (call_genesis(sourced_calls.run_calls actions machine)))"
    by (rule sourced_request_current_revision_for_calls[OF actual[symmetric]])
  have ordered: "sourced_call_revision(call_authority_state machine)\<le>
    sourced_call_revision(sourced_calls.replay_call_authority
      (take index(call_authority_log(sourced_calls.run_calls actions machine)))
      (call_genesis(sourced_calls.run_calls actions machine)))"
    by (rule sourced_order.fresh_result_execution_is_after_the_initial_cut[OF initial_replay missing found])
  show ?thesis using ordered by (simp only: issued)
qed

theorem later_sourced_invocation_cannot_complete_an_older_current_revision:
  fixes before gap after :: "(sourced_request,sourced_environment) client_call_action list"
    and initial :: sourced_observation_state
  assumes before_state: "before_completion=sourced_calls.run_calls before(initial_call_machine initial)"
    and completion_state: "after_completion=sourced_calls.call_step(Complete_Call first_call)before_completion"
    and first_not_done: "call_completions before_completion first_call=None"
    and first_done: "call_completions after_completion first_call=
      Some(Sourced_Observation(Current_Value first_revision first_payload))"
    and gap_state: "before_begin=sourced_calls.run_calls gap after_completion"
    and fresh_invocation: "call_invocations before_begin later_call=None"
    and begin_state: "after_begin=sourced_calls.call_step(Begin_Call later_call later_request)before_begin"
    and final_state: "finished=sourced_calls.run_calls after after_begin"
    and later_done: "call_completions finished later_call=
      Some(Sourced_Observation(Current_Value later_revision later_payload))"
  shows "first_revision\<le>later_revision"
proof -
  have generated_before: "authority_cache_contract before_completion \<and>
    sourced_calls.authority_replay_contract before_completion"
    using sourced_calls.generated_call_contracts[of before initial] before_state by simp
  have before_begin_trace: "before_begin=sourced_calls.run_calls
    (before@[Complete_Call first_call]@gap)(initial_call_machine initial)"
    by (simp add: before_state completion_state gap_state sourced_calls.run_calls_append)
  have after_begin_trace: "after_begin=sourced_calls.run_calls
    (before@[Complete_Call first_call]@gap@[Begin_Call later_call later_request])(initial_call_machine initial)"
    by (simp add: before_begin_trace begin_state sourced_calls.run_calls_append)
  have finished_trace: "finished=sourced_calls.run_calls
    (before@[Complete_Call first_call]@gap@[Begin_Call later_call later_request]@after)(initial_call_machine initial)"
    by (simp add: final_state after_begin_trace sourced_calls.run_calls_append)
  have generated_after_begin: "sourced_calls.authority_replay_contract after_begin"
    using sourced_calls.generated_call_contracts
      [of "before@[Complete_Call first_call]@gap@[Begin_Call later_call later_request]" initial]
    by (simp only: after_begin_trace[symmetric])
  have generated_finished: "authority_cache_contract finished \<and>
    sourced_calls.authority_replay_contract finished"
    using sourced_calls.generated_call_contracts
      [of "before@[Complete_Call first_call]@gap@[Begin_Call later_call later_request]@after" initial]
    by (simp only: finished_trace[symmetric])
  have life_before_begin: "call_lifecycle_contract before_begin"
    using sourced_calls.generated_call_lifecycle_contract
      [of "before@[Complete_Call first_call]@gap" initial]
    by (simp only: before_begin_trace[symmetric])
  have life_finished: "call_lifecycle_contract finished"
    using sourced_calls.generated_call_lifecycle_contract
      [of "before@[Complete_Call first_call]@gap@[Begin_Call later_call later_request]@after" initial]
    by (simp only: finished_trace[symmetric])
  obtain first_request first_index where first_source:
    "call_authority_results before_completion first_call=
      Some(first_request,Sourced_Observation(Current_Value first_revision first_payload),first_index)"
    using sourced_calls.completion_has_an_earlier_invocation_and_exact_source_result
      [OF first_not_done] first_done completion_state by auto
  have first_upper: "first_revision\<le>sourced_call_revision(call_authority_state before_completion)"
    by (rule sourced_cached_current_revision_upper[OF _ _ first_source])
      (use generated_before in auto)
  have complete_same: "call_authority_state after_completion=call_authority_state before_completion"
    by (simp add: completion_state)
  have gap_order: "sourced_call_revision(call_authority_state after_completion)\<le>
    sourced_call_revision(call_authority_state before_begin)"
    unfolding gap_state by (rule sourced_order.call_run_revision_nondecreasing)
  have begin_same: "call_authority_state after_begin=call_authority_state before_begin"
    by (simp add: begin_state)
  have no_earlier_source: "call_authority_results before_begin later_call=None"
    by (rule not_invoked_has_no_source_result[OF life_before_begin fresh_invocation])
  have no_source_at_begin: "call_authority_results after_begin later_call=None"
    by (simp add: begin_state no_earlier_source)
  obtain later_command later_index where later_source:
    "call_authority_results finished later_call=
      Some(later_command,Sourced_Observation(Current_Value later_revision later_payload),later_index)"
    using completed_result_has_source[OF life_finished later_done] by blast
  have later_lower: "sourced_call_revision(call_authority_state after_begin)\<le>later_revision"
    by (rule sourced_fresh_current_revision_lower[OF generated_after_begin _ _ no_source_at_begin])
      (use generated_finished later_source in \<open>auto simp: final_state\<close>)
  have between: "sourced_call_revision(call_authority_state before_completion)\<le>
    sourced_call_revision(call_authority_state after_begin)"
    using gap_order by (simp only: complete_same begin_same)
  have first_before_begin: "first_revision\<le>sourced_call_revision(call_authority_state after_begin)"
    by (rule order_trans[OF first_upper between])
  show ?thesis by (rule order_trans[OF first_before_begin later_lower])
qed

text \<open>The source-aware callbacks supply both revision obligations of the
  durable call-order kernel. Current success is tied to the actual coupled
  core before that callback, including the protected application-read path.
  Source-unit reads retain their availability and reconciliation checks.
  Adapter events, raw source observations and historical responses are not
  reclassified as successful current responses.

  The conclusion requires a genuinely new invocation after the first
  completion. It does not order delayed responses of overlapping calls,
  assert monotone balances, or establish physical source authentication,
  persistence or a distributed clock.\<close>

end

end
