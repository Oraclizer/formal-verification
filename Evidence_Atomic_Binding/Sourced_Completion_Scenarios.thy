(* SPDX-License-Identifier: BSD-3-Clause *)
theory Sourced_Completion_Scenarios
  imports Sourced_Response_Link Sourced_Call_Order Source_Observation_Projection Finality_Progress
begin

text \<open>These finite programs use the existing source-attestation instance
  and the actual sourced request and environment callbacks. They exercise
  successful completion premises, including the current source-availability
  and reconciliation checks. The context input changes the actual authority
  revision; it does not replace the source producer or its guards.\<close>

type_synonym completion_machine =
  "(sourced_observation_state,sourced_request,sourced_reply,sourced_environment) durable_call_machine"

definition completion_read :: sourced_request where
  "completion_read=Endpoint_Request(Read_Current 0(Source_Balance(0,17)))"

definition completion_refresh :: sourced_request where
  "completion_refresh=Endpoint_Request(Refresh_Endpoint 0)"

definition completion_history :: sourced_request where
  "completion_history=Endpoint_Request(Read_Historical 0(Source_Balance(0,17)))"

definition completion_change :: sourced_environment where
  "completion_change=View_Environment(Replace_Current_Context 0(sample_source_context ACTIVE))"

definition completion_ready :: sourced_observation_state where
  "completion_ready=fst(linked.execute_sourced_request completion_refresh source_raw_start)"

definition completion_changed :: sourced_observation_state where
  "completion_changed=fst(linked.execute_sourced_environment completion_change completion_ready)"

definition completion_ready_again :: sourced_observation_state where
  "completion_ready_again=fst(linked.execute_sourced_request completion_refresh completion_changed)"

lemmas completion_current_calculation =
  source_attestation.execute_observed.simps(1)[OF linked.source_attestation_axioms]

lemmas completion_historical_calculation =
  source_attestation.execute_observed.simps(3)[OF linked.source_attestation_axioms]

lemmas completion_callback_data =
  source_refresh_calculation completion_current_calculation completion_historical_calculation
  completion_read_def completion_refresh_def completion_history_def completion_change_def
  completion_ready_def completion_changed_def completion_ready_again_def
  source_raw_start_def initial_sourced_observations_def initial_source_coupling_def
  initial_controlled_source_def initial_source_boundary_def initial_finality_core_def
  initial_reservation_machine_def initial_reservation_state_def empty_message_state_def
  initial_observed_finality_def sourced_view_def install_sourced_view_def store_core_result_def
  source_view_is_reconciled_def source_debit_gap_def source_return_gap_def
  boundary_debited_def controlled_returned_def source_debits_def
  current_query_reply_def historical_query_reply_def current_cache_valid_def snapshot_query_ready_def
  capture_snapshot_def sample_balances_def
  linked.execute_finality_environment_def linked.finality_step_def

lemma completion_refresh_callbacks:
  "linked.execute_sourced_request completion_refresh source_raw_start=
    (completion_ready,Sourced_Observation Cache_Refreshed)"
  "linked.execute_sourced_request completion_refresh completion_changed=
    (completion_ready_again,Sourced_Observation Cache_Refreshed)"
  by (simp_all add: completion_refresh_def completion_ready_def completion_ready_again_def
    source_refresh_calculation sourced_view_def install_sourced_view_def Let_def)

lemma completion_query_callbacks:
  "linked.execute_sourced_request completion_read completion_ready=
    (completion_ready,Sourced_Observation(Current_Value 0(Units_Value 10)))"
  "linked.execute_sourced_request completion_read completion_changed=
    (completion_changed,Sourced_Observation Observation_Busy)"
  "linked.execute_sourced_request completion_read completion_ready_again=
    (completion_ready_again,Sourced_Observation(Current_Value 1(Units_Value 10)))"
  "linked.execute_sourced_request completion_history completion_ready_again=
    (completion_ready_again,Sourced_Observation(Historical_Value 0(Units_Value 10)))"
  by (simp_all add: completion_callback_data Let_def)

lemma completion_change_callback:
  "linked.execute_sourced_environment completion_change completion_ready=
    (completion_changed,Sourced_Observation(Effect_Reply Context_Installed))"
  by (simp add: completion_change_def completion_changed_def
    install_sourced_view_def linked.execute_finality_environment_def sample_source_context_def Let_def)

lemma completion_current_source_guards_are_true:
  "observation_source_available completion_ready"
  "source_view_is_reconciled(observation_source completion_ready)(0,17)"
  "observation_source_available completion_ready_again"
  "source_view_is_reconciled(observation_source completion_ready_again)(0,17)"
  by (simp_all add: completion_callback_data Let_def)

definition completion_before_program :: "(sourced_request,sourced_environment) client_call_action list" where
  "completion_before_program=complete_call_program(0,1)completion_refresh@
    [Begin_Call(0,2)completion_read,Dispatch_Call(0,2)completion_read,Collect_Response(0,2)completion_read]"

definition completion_gap_program :: "(sourced_request,sourced_environment) client_call_action list" where
  "completion_gap_program=[Apply_Authority_Input completion_change]@
    complete_call_program(0,3)completion_refresh"

definition completion_after_program :: "(sourced_request,sourced_environment) client_call_action list" where
  "completion_after_program=
    [Dispatch_Call(0,4)completion_read,Collect_Response(0,4)completion_read,Complete_Call(0,4)]"

definition completion_program :: "(sourced_request,sourced_environment) client_call_action list" where
  "completion_program=completion_before_program@[Complete_Call(0,2)]@completion_gap_program@
    [Begin_Call(0,4)completion_read]@completion_after_program"

definition completion_before :: completion_machine where
  "completion_before=linked.sourced_calls.run_calls completion_before_program(initial_call_machine source_raw_start)"

definition completion_first :: completion_machine where
  "completion_first=linked.sourced_calls.call_step(Complete_Call(0,2))completion_before"

definition completion_before_begin :: completion_machine where
  "completion_before_begin=linked.sourced_calls.run_calls completion_gap_program completion_first"

definition completion_after_begin :: completion_machine where
  "completion_after_begin=linked.sourced_calls.call_step(Begin_Call(0,4)completion_read)completion_before_begin"

definition completion_finished :: completion_machine where
  "completion_finished=linked.sourced_calls.run_calls completion_program(initial_call_machine source_raw_start)"

lemmas completion_program_data =
  completion_before_program_def completion_gap_program_def completion_after_program_def completion_program_def
  completion_before_def completion_first_def completion_before_begin_def completion_after_begin_def
  completion_finished_def complete_call_program_def initial_call_machine_def
  linked.sourced_calls.call_definitions

lemma completion_actual_checkpoint_facts:
  "call_completions completion_before(0,2)=None"
  "call_completions completion_first(0,2)=Some(Sourced_Observation(Current_Value 0(Units_Value 10)))"
  "call_invocations completion_before_begin(0,4)=None"
  "call_completions completion_finished(0,4)=Some(Sourced_Observation(Current_Value 1(Units_Value 10)))"
  "call_authority_state completion_before_begin=completion_ready_again"
  by (simp_all add: completion_program_data completion_refresh_callbacks completion_query_callbacks
    completion_change_callback Let_def nth_append
    del: linked.execute_sourced_request.simps linked.execute_sourced_environment.simps)

lemma completion_finished_is_the_actual_continuation:
  "completion_finished=linked.sourced_calls.run_calls completion_after_program completion_after_begin"
  by (simp add: completion_finished_def completion_program_def completion_after_begin_def
    completion_before_begin_def completion_first_def completion_before_def linked.sourced_calls.run_calls_append)

theorem actual_nonoverlapping_sourced_completions_activate_revision_order:
  "(0::nat)\<le>1"
proof (rule linked.later_sourced_invocation_cannot_complete_an_older_current_revision
      [where before=completion_before_program and gap=completion_gap_program and after=completion_after_program
        and initial=source_raw_start and before_completion=completion_before and after_completion=completion_first
        and before_begin=completion_before_begin and after_begin=completion_after_begin and finished=completion_finished
        and first_call="(0,2)" and later_call="(0,4)" and later_request=completion_read
        and first_payload="Units_Value 10" and later_payload="Units_Value 10"])
  show "completion_before=linked.sourced_calls.run_calls completion_before_program
    (initial_call_machine source_raw_start)"
    by (simp only: completion_before_def)
  show "completion_first=linked.sourced_calls.call_step(Complete_Call(0,2))completion_before"
    by (simp only: completion_first_def)
  show "call_completions completion_before(0,2)=None"
    by (rule completion_actual_checkpoint_facts(1))
  show "call_completions completion_first(0,2)=Some(Sourced_Observation(Current_Value 0(Units_Value 10)))"
    by (rule completion_actual_checkpoint_facts(2))
  show "completion_before_begin=linked.sourced_calls.run_calls completion_gap_program completion_first"
    by (simp only: completion_before_begin_def)
  show "call_invocations completion_before_begin(0,4)=None"
    by (rule completion_actual_checkpoint_facts(3))
  show "completion_after_begin=linked.sourced_calls.call_step
    (Begin_Call(0,4)completion_read)completion_before_begin"
    by (simp only: completion_after_begin_def)
  show "completion_finished=linked.sourced_calls.run_calls completion_after_program completion_after_begin"
    by (rule completion_finished_is_the_actual_continuation)
  show "call_completions completion_finished(0,4)=Some(Sourced_Observation(Current_Value 1(Units_Value 10)))"
    by (rule completion_actual_checkpoint_facts(4))
qed

theorem actual_current_completion_activates_the_full_response_contract:
  "\<exists>command query index.
    call_authority_results completion_finished(0,4)=
      Some(Endpoint_Request command,Sourced_Observation(Current_Value 1(Units_Value 10)),index) \<and>
    index<length(call_authority_log completion_finished) \<and> command_query command=Some query \<and>
    Units_Value 10=abstract_query_value query(sourced_response_alpha
      (linked.sourced_calls.replay_call_authority(take index(call_authority_log completion_finished))source_raw_start)) \<and>
    1=target_revision(sourced_response_alpha
      (linked.sourced_calls.replay_call_authority(take index(call_authority_log completion_finished))source_raw_start)) \<and>
    (\<forall>account. current_source_query command=Some account \<longrightarrow>
      observation_source_available(linked.sourced_calls.replay_call_authority
        (take index(call_authority_log completion_finished))source_raw_start) \<and>
      source_view_is_reconciled(observation_source(linked.sourced_calls.replay_call_authority
        (take index(call_authority_log completion_finished))source_raw_start))account)"
proof -
  have completed: "call_completions(linked.sourced_calls.run_calls completion_program
      (initial_call_machine source_raw_start))(0,4)=Some(Sourced_Observation(Current_Value 1(Units_Value 10)))"
    using completion_actual_checkpoint_facts(4) by (simp only: completion_finished_def)
  show ?thesis unfolding completion_finished_def
    by (rule linked.completed_sourced_current_preserves_value_revision_and_source_guards[OF completed])
qed

definition completion_history_program :: "(sourced_request,sourced_environment) client_call_action list" where
  "completion_history_program=completion_program@complete_call_program(0,5)completion_history"

definition completion_history_finished :: completion_machine where
  "completion_history_finished=linked.sourced_calls.run_calls completion_history_program
    (initial_call_machine source_raw_start)"

lemma completion_historical_reply_is_completed:
  "call_completions completion_history_finished(0,5)=
    Some(Sourced_Observation(Historical_Value 0(Units_Value 10)))"
  by (simp add: completion_history_finished_def completion_history_program_def completion_program_data
    completion_refresh_callbacks completion_query_callbacks completion_change_callback Let_def nth_append
    del: linked.execute_sourced_request.simps linked.execute_sourced_environment.simps)

theorem actual_historical_completion_activates_the_prior_snapshot_contract:
  "\<exists>command query execution_index snapshot_index.
    call_authority_results completion_history_finished(0,5)=
      Some(Endpoint_Request command,Sourced_Observation(Historical_Value 0(Units_Value 10)),execution_index) \<and>
    execution_index<length(call_authority_log completion_history_finished) \<and> snapshot_index\<le>execution_index \<and>
    command_query command=Some query \<and> requested_history_revision command=Some 0 \<and>
    Units_Value 10=abstract_query_value query(sourced_response_alpha(linked.sourced_calls.replay_call_authority
      (take snapshot_index(call_authority_log completion_history_finished))source_raw_start)) \<and>
    target_revision(sourced_response_alpha(linked.sourced_calls.replay_call_authority
      (take snapshot_index(call_authority_log completion_history_finished))source_raw_start))=0"
proof -
  have completed: "call_completions(linked.sourced_calls.run_calls completion_history_program
      (initial_call_machine(initial_sourced_observations sample_balances(sample_metadata ACTIVE)
        (\<lambda>_.sample_source_context ACTIVE))))(0,5)=Some(Sourced_Observation(Historical_Value 0(Units_Value 10)))"
    using completion_historical_reply_is_completed
    by (simp only: completion_history_finished_def source_raw_start_def)
  show ?thesis unfolding completion_history_finished_def source_raw_start_def
    by (rule linked.completed_sourced_historical_has_a_prior_actual_snapshot[OF completed])
qed

definition completion_busy_program :: "(sourced_request,sourced_environment) client_call_action list" where
  "completion_busy_program=completion_before_program@[Complete_Call(0,2),Apply_Authority_Input completion_change]@
    complete_call_program(0,9)completion_read"

definition completion_catchup_program :: "(sourced_request,sourced_environment) client_call_action list" where
  "completion_catchup_program=complete_call_program(0,10)completion_refresh@
    complete_call_program(0,9)completion_read@complete_call_program(0,11)completion_read"

definition completion_busy :: completion_machine where
  "completion_busy=linked.sourced_calls.run_calls completion_busy_program(initial_call_machine source_raw_start)"

definition completion_caught_up :: completion_machine where
  "completion_caught_up=linked.sourced_calls.run_calls completion_catchup_program completion_busy"

lemma a_real_stale_query_completes_busy:
  "call_completions completion_busy(0,9)=Some(Sourced_Observation Observation_Busy)"
  by (simp add: completion_busy_def completion_busy_program_def completion_program_data
    completion_refresh_callbacks completion_query_callbacks completion_change_callback Let_def nth_append
    del: linked.execute_sourced_request.simps linked.execute_sourced_environment.simps)

theorem old_busy_id_stays_completed_while_a_fresh_id_succeeds:
  "call_completions completion_caught_up(0,9)=Some(Sourced_Observation Observation_Busy) \<and>
    call_completions completion_caught_up(0,11)=Some(Sourced_Observation(Current_Value 1(Units_Value 10)))"
proof -
  have old: "call_completions completion_caught_up(0,9)=Some(Sourced_Observation Observation_Busy)"
    unfolding completion_caught_up_def
    by (rule linked.completed_sourced_busy_and_unavailable_remain_completed(1)[OF a_real_stale_query_completes_busy])
  have fresh: "call_completions completion_caught_up(0,11)=Some(Sourced_Observation(Current_Value 1(Units_Value 10)))"
    by (simp add: completion_caught_up_def completion_catchup_program_def completion_busy_def completion_busy_program_def
      completion_program_data completion_refresh_callbacks completion_query_callbacks completion_change_callback Let_def nth_append
      del: linked.execute_sourced_request.simps linked.execute_sourced_environment.simps)
  show ?thesis using old fresh by blast
qed

text \<open>The first successful current completion precedes the later
  invocation. A real authority context input advances the revision from zero
  to one, and a separate fresh call refreshes the endpoint before the later
  successful read. The historical call returns the earlier revision from
  actual retained snapshot history. On the separate Busy branch, refresh
  changes the endpoint but does not rewrite the durable result of the old
  identifier; a fresh identifier completes the current value.

  These are finite executions of the formal callbacks. They establish
  satisfiable premises for the existing consumer theorems, not physical
  authentication, persistence, network availability or a runtime deployment.\<close>

end
