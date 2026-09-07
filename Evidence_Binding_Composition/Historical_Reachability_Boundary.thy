(* SPDX-License-Identifier: BSD-3-Clause *)
theory Historical_Reachability_Boundary
  imports Integration_Examples "Evidence_Atomic_Binding.Historical_Snapshot_Provenance"
begin

section \<open>Original Execution Captures the Current Historical Slot\<close>

definition current_history_is_capture :: "observed_finality \<Rightarrow> bool" where
  "current_history_is_capture state \<longleftrightarrow>
    historical_snapshots state (core_epoch(observed_core state))=
      Some(capture_snapshot(observed_core state))"

lemma initial_current_history_is_capture [simp]:
  "current_history_is_capture(initial_observed_finality core)"
  by (simp add: current_history_is_capture_def initial_observed_finality_def)

lemma store_result_establishes_current_capture [simp]:
  "current_history_is_capture(fst(store_core_result result state))"
  by (simp add: current_history_is_capture_def store_core_result_def Let_def)

lemma local_cache_keeps_current_capture [simp]:
  "current_history_is_capture(state\<lparr>endpoint_cache:=cache\<rparr>)=
    current_history_is_capture state"
  "current_history_is_capture(state\<lparr>secondary_progress:=progress\<rparr>)=
    current_history_is_capture state"
  by (simp_all add: current_history_is_capture_def)

context source_attestation
begin

lemma protected_current_keeps_current_capture:
  assumes "current_history_is_capture state"
  shows "current_history_is_capture(fst(execute_protected_current endpoint index request query state))"
  using assms
  by (auto simp: execute_protected_current_def Let_def
      split: if_splits observed_reply.splits application_query.splits
        finality_reply.splits reservation_reply.splits)

lemma actual_callback_keeps_current_capture:
  assumes "current_history_is_capture state"
  shows "current_history_is_capture(fst(execute_observed command state))"
  using assms by (cases command)
    (auto intro: protected_current_keeps_current_capture)

lemma actual_environment_keeps_current_capture:
  assumes "current_history_is_capture state"
  shows "current_history_is_capture(fst(execute_observed_environment input state))"
  using assms by (cases input) auto

lemma every_original_replay_keeps_current_capture:
  assumes "current_history_is_capture state"
  shows "current_history_is_capture(observed_calls.replay_call_authority entries state)"
  using assms
proof (induction entries arbitrary: state)
  case Nil
  then show ?case by simp
next
  case (Cons entry entries)
  have step: "current_history_is_capture(observed_entry_after entry state)"
    using Cons.prems by (cases entry)
      (simp_all add: actual_callback_keeps_current_capture actual_environment_keeps_current_capture)
  show ?case using Cons.IH[OF step] by (simp only: observed_replay_cons)
qed

theorem every_generated_call_authority_keeps_current_capture:
  "current_history_is_capture(call_authority_state(observed_calls.run_calls actions
    (initial_call_machine(initial_observed_finality core))))"
proof -
  let ?m = "observed_calls.run_calls actions(initial_call_machine(initial_observed_finality core))"
  have replay: "call_authority_state ?m=observed_calls.replay_call_authority
      (call_authority_log ?m)(initial_observed_finality core)"
    using observed_calls.generated_call_contracts[of actions "initial_observed_finality core"]
    by (simp add: observed_calls.authority_replay_contract_def initial_call_machine_def)
  show ?thesis by (simp only: replay)
    (rule every_original_replay_keeps_current_capture, rule initial_current_history_is_capture)
qed

end

section \<open>Reply Preservation Does Not Imply Original-State Reachability\<close>

theorem normalized_actual_history_violates_original_current_capture:
  "\<not>current_history_is_capture(normalize_observed_history(history_example_tick 1))"
proof
  assume capture: "current_history_is_capture(normalize_observed_history(history_example_tick 1))"
  have stored: "historical_snapshots(normalize_observed_history(history_example_tick 1))1=
      Some(capture_snapshot(observed_core(history_example_tick 1)))"
    using capture
    by (simp only: current_history_is_capture_def normalize_observed_history_fields
        history_example_generated_fields)
  have clock: "historical_clock(normalize_observed_history(history_example_tick 1))1=Some 1"
    by (simp only: historical_clock_def stored option.case)
      (simp add: capture_snapshot_def history_example_generated_fields)
  have zero: "historical_clock(normalize_observed_history(history_example_tick 1))1=Some 0"
    by (simp only: normalized_historical_clock history_example_generated_fields(3); simp)
  show False using clock zero by simp
qed

theorem projected_actual_history_is_not_any_original_call_authority:
  "normalize_observed_history(history_example_tick 1)\<noteq>
    call_authority_state(sample.observed_calls.run_calls actions
      (initial_call_machine(initial_observed_finality core)))"
proof
  assume equal: "normalize_observed_history(history_example_tick 1)=
    call_authority_state(sample.observed_calls.run_calls actions
      (initial_call_machine(initial_observed_finality core)))"
  have capture: "current_history_is_capture(normalize_observed_history(history_example_tick 1))"
    using sample.every_generated_call_authority_keeps_current_capture[of actions core]
    by (simp only: equal)
  show False by (rule notE[OF normalized_actual_history_violates_original_current_capture capture])
qed

theorem original_reachability_and_reply_preservation_are_distinct:
  "snd(sample.execute_observed command(normalize_observed_history(history_example_tick 1)))=
      snd(sample.execute_observed command(history_example_tick 1)) \<and>
    normalize_observed_history(history_example_tick 1)\<noteq>
      call_authority_state(sample.observed_calls.run_calls actions
        (initial_call_machine(initial_observed_finality core)))"
  by (rule conjI[OF the_changed_history_preserves_every_actual_callback
      projected_actual_history_is_not_any_original_call_authority])

text \<open>All original calls and environment inputs preserve the current
  snapshot in its historical slot, including cache corruption, crashes,
  retries and completed refusals in the durable call model. The actual
  one-tick state has clock one both in its current core and in that slot.
  Historical normalization changes only the latter clock to zero.
  Its callback replies are still preserved, but the resulting whole state
  is not the authority state of any original call execution from an actual
  initial observed view. The reduced callback system remains a valid
  observational representation. Constructive funding realization is a
  separate result about its stated finite allocation language.\<close>

end
