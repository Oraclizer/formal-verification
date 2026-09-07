(* SPDX-License-Identifier: BSD-3-Clause *)
theory Finality_Progress
  imports Abstract_Observation_Types Finality_Scenarios
begin

definition complete_call_program :: "client_call_id \<Rightarrow> 'command \<Rightarrow>
  ('command,'environment) client_call_action list" where
  "complete_call_program call_id command=[Begin_Call call_id command,Dispatch_Call call_id command,
    Collect_Response call_id command,Complete_Call call_id]"

context durable_call_protocol
begin

theorem an_uninterrupted_fresh_call_completes_its_actual_reply:
  assumes local: "call_local_status m=Endpoint_Up" and connected: "call_connection m=Authority_Connected"
    and invocation: "call_invocations m call_id=None"
    and source: "call_authority_results m call_id=None"
    and incomplete: "call_completions m call_id=None"
  shows "call_completions(run_calls(complete_call_program call_id command)m)call_id=
      Some(snd(execute command(call_authority_state m))) \<and>
    call_authority_state(run_calls(complete_call_program call_id command)m)=
      fst(execute command(call_authority_state m))"
  using assms
  by (simp add: complete_call_program_def call_definitions Let_def nth_append)

theorem a_fresh_initial_call_has_a_four_action_completion:
  "call_completions(run_calls(complete_call_program call_id command)(initial_call_machine state))call_id=
    Some(snd(execute command state))"
  using an_uninterrupted_fresh_call_completes_its_actual_reply[of "initial_call_machine state" call_id command]
  by (simp add: initial_call_machine_def)

end

lemma finite_program_rank_strictly_decreases:
  "length rest<length(action#rest)"
  by simp

context source_attestation
begin

theorem a_ready_read_completes_after_a_quiescent_refresh:
  fixes endpoint :: nat and state :: observed_finality and query :: application_query
  assumes ready: "snapshot_query_ready query(capture_snapshot(observed_core state))"
    and public: "public_balance_query query"
  defines "fresh \<equiv> fst(execute_observed(Refresh_Endpoint endpoint)state)"
  shows "call_completions(observed_calls.run_calls
      (complete_call_program call_id(Read_Current endpoint query))(initial_call_machine fresh))call_id=
    Some(Current_Value(core_epoch(observed_core state))
      (abstract_query_value query(observation_alpha(observed_core state))))"
proof -
  have response: "snd(execute_observed(Read_Current endpoint query)fresh)=
    Current_Value(core_epoch(observed_core state))(stored_query query(capture_snapshot(observed_core state)))"
    unfolding fresh_def by (rule refresh_allows_a_ready_current_query[OF ready public])
  have completed: "call_completions(observed_calls.run_calls
      (complete_call_program call_id(Read_Current endpoint query))(initial_call_machine fresh))call_id=
    Some(snd(execute_observed(Read_Current endpoint query)fresh))"
    by (rule observed_calls.a_fresh_initial_call_has_a_four_action_completion)
  have value_eq: "stored_query query(capture_snapshot(observed_core state))=
    abstract_query_value query(observation_alpha(observed_core state))"
    by (rule independent_stored_and_abstract_query_readers_agree[OF captured_state_supplies_snapshot_correspondence])
  show ?thesis by (simp only: completed response value_eq)
qed

definition interference_cycle :: "nat \<Rightarrow> lock_context \<Rightarrow> application_query \<Rightarrow>
  observed_finality \<Rightarrow> observed_finality \<times> observed_reply" where
  "interference_cycle endpoint c query state=(let
    refreshed=fst(execute_observed(Refresh_Endpoint endpoint)state);
    changed=fst(execute_observed_environment(Replace_Current_Context endpoint c)refreshed)
    in execute_observed(Read_Current endpoint query)changed)"

theorem refresh_and_retry_alone_do_not_force_a_successful_read:
  assumes "public_balance_query query"
  shows "snd(interference_cycle endpoint c query state)=Observation_Busy"
proof -
  let ?fresh = "fst(execute_observed(Refresh_Endpoint endpoint)state)"
  let ?changed = "fst(execute_observed_environment(Replace_Current_Context endpoint c)?fresh)"
  have cache: "endpoint_cache ?changed endpoint=Some(capture_snapshot(observed_core state))"
    by (simp add: store_core_result_def Let_def)
  have revision: "snapshot_revision(capture_snapshot(observed_core state))<core_epoch(observed_core ?changed)"
    by (simp add: store_core_result_def execute_finality_environment_def capture_snapshot_def Let_def)
  have "snd(execute_observed(Read_Current endpoint query)?changed)=Observation_Busy"
    by (rule stale_cache_cannot_complete_as_current[OF cache revision assms])
  then show ?thesis by (simp only: interference_cycle_def Let_def)
qed

fun interference_prefix :: "nat \<Rightarrow> nat \<Rightarrow> lock_context \<Rightarrow> application_query
  \<Rightarrow> observed_finality \<Rightarrow> observed_finality" where
  "interference_prefix 0 endpoint c query state=state"
| "interference_prefix(Suc n)endpoint c query state=
    interference_prefix n endpoint c query(fst(interference_cycle endpoint c query state))"

theorem arbitrarily_long_refresh_and_retry_runs_can_remain_busy:
  "public_balance_query query \<Longrightarrow>
    snd(interference_cycle endpoint c query(interference_prefix n endpoint c query state))=Observation_Busy"
  by (rule refresh_and_retry_alone_do_not_force_a_successful_read)

lemma interference_does_not_change_the_financial_or_regulatory_state:
  "finality_alpha(observed_core(fst(interference_cycle endpoint c query state)))=
    finality_alpha(observed_core state)"
  by (simp add: interference_cycle_def store_core_result_def execute_finality_environment_def
      finality_step_def finality_alpha_def Let_def split: if_splits)

text \<open>Completion progress and terminal progress are different claims.
  The four-action program completes the response computed by the actual
  callback; that response may legitimately be Busy or Rejected. A successful
  current query additionally needs a ready published view and a refresh-to-use
  interval without an intervening authority revision change. Its finite
  program has a strictly decreasing remaining-action count.

  No assumption here forces an unknown source effect to become reversible.
  Eventual authenticated evidence, successful authorization and delivery of
  the required protocol actions remain necessary for terminal progress.
  Ordinary process retry fairness and network connectivity alone are not
  sufficient for this cached current-read algorithm: the explicit cycle
  refreshes and retries indefinitely while an intervening context input
  invalidates every cached revision. A quiescent interval or fairness of the
  successful consumption transition is a stronger, explicit condition.
  The model permits competing updates and exposes this progress limitation;
  it does not forbid all later trading or force a pending refund.\<close>

end

end
