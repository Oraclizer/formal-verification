(* SPDX-License-Identifier: BSD-3-Clause *)
theory Integration_Examples
  imports Integration_Transport "Evidence_Atomic_Binding.Finality_Scenarios"
begin

section \<open>One Actual Clock Event Makes Historical Normalization Nontrivial\<close>

definition history_example_initial :: observed_finality where
  "history_example_initial=initial_observed_finality finality_sample_initial"

definition history_example_ready :: observed_finality where
  "history_example_ready=fst(sample.execute_observed(Refresh_Endpoint 0)history_example_initial)"

definition history_example_tick :: "nat \<Rightarrow> observed_finality" where
  "history_example_tick amount=fst(sample.execute_observed
    (Execute_Current 0(Client_Protocol 0 0(Time_Intent amount)))history_example_ready)"

definition historical_clock :: "observed_finality \<Rightarrow> nat \<Rightarrow> nat option" where
  "historical_clock state revision=(case historical_snapshots state revision of None \<Rightarrow> None
    | Some snapshot \<Rightarrow> Some(reservation_clock(snapshot_financial snapshot)))"

lemma history_example_is_an_actual_successful_call:
  "snd(sample.execute_observed(Execute_Current 0(Client_Protocol 0 0(Time_Intent amount)))
    history_example_ready)=Effect_Reply Internal_Completed"
  by (simp add: history_example_ready_def current_cache_valid_def store_core_result_def
      sample.execute_finality_client_def sample.invoke_protocol_def Let_def)

lemma history_example_generated_fields:
  "core_epoch(observed_core(history_example_tick amount))=1"
  "reservation_clock(machine_state(core_parent(observed_core(history_example_tick amount))))=amount"
  "historical_snapshots(history_example_tick amount)1=Some(capture_snapshot(observed_core(history_example_tick amount)))"
  "historical_clock(history_example_tick amount)1=Some amount"
  by (simp_all add: history_example_tick_def history_example_ready_def history_example_initial_def
      current_cache_valid_def store_core_result_def sample.execute_finality_client_def
      sample.finality_step_def sample.invoke_protocol_def advance_reservation_time_def
      commit_reservation_event_def initial_observed_finality_def finality_sample_initial_def
      initial_finality_core_def initial_reservation_machine_def initial_reservation_state_def
      capture_snapshot_def historical_clock_def Let_def)

lemma normalized_historical_clock:
  "historical_clock(normalize_observed_history state)revision=
    (case historical_snapshots state revision of None \<Rightarrow> None | Some snapshot \<Rightarrow> Some 0)"
  by (cases "historical_snapshots state revision")
    (simp_all add: historical_clock_def normalize_observed_history_def
      normalize_snapshot_history_def normalize_historical_snapshot_def)

theorem actual_history_projection_changes_a_generated_payload:
  "normalize_observed_history(history_example_tick 1)\<noteq>history_example_tick 1"
proof
  assume same: "normalize_observed_history(history_example_tick 1)=history_example_tick 1"
  have projected: "historical_clock(normalize_observed_history(history_example_tick 1))1=Some 0"
    by (simp only: normalized_historical_clock history_example_generated_fields(3); simp)
  have original: "historical_clock(history_example_tick 1)1=Some 1"
    by (rule history_example_generated_fields)
  show False using projected original by (simp only: same option.inject; simp)
qed

theorem the_changed_history_preserves_every_actual_callback:
  "snd(sample.execute_observed command(normalize_observed_history(history_example_tick 1)))=
    snd(sample.execute_observed command(history_example_tick 1))"
  by (rule sample.observed_callback_reply_preserved)

lemma distinct_clock_inputs_have_the_same_revision:
  "core_epoch(observed_core(history_example_tick 1))=core_epoch(observed_core(history_example_tick 2))"
  by (simp only: history_example_generated_fields)

lemma distinct_clock_inputs_have_different_complete_snapshots:
  "capture_snapshot(observed_core(history_example_tick 1))\<noteq>
    capture_snapshot(observed_core(history_example_tick 2))"
proof
  assume same: "capture_snapshot(observed_core(history_example_tick 1))=
    capture_snapshot(observed_core(history_example_tick 2))"
  have clock:
    "reservation_clock(snapshot_financial(capture_snapshot(observed_core(history_example_tick 1))))=
     reservation_clock(snapshot_financial(capture_snapshot(observed_core(history_example_tick 2))))"
    by (rule arg_cong[OF same])
  show False using clock by (simp add: capture_snapshot_def history_example_generated_fields)
qed

theorem the_actual_current_probe_keeps_the_clock_distinction:
  "snd(sample.execute_observed(current_snapshot_probe 0)
      (sample.install_snapshot_probe 0(capture_snapshot(observed_core(history_example_tick 1)))
        (history_example_tick 1)))=Effect_Reply Internal_Completed \<and>
    snd(sample.execute_observed(current_snapshot_probe 0)
      (sample.install_snapshot_probe 0(capture_snapshot(observed_core(history_example_tick 1)))
        (history_example_tick 2)))=Observation_Busy"
  by (simp del: One_nat_def add: sample.actual_snapshot_probe_reply
      distinct_clock_inputs_have_different_complete_snapshots)

definition execute_current_without_cache_guard :: "nat \<Rightarrow> client_command \<Rightarrow>
  observed_finality \<Rightarrow> observed_finality \<times> observed_reply" where
  "execute_current_without_cache_guard endpoint command state=
    store_core_result(sample.execute_finality_client command(observed_core state))state"

theorem removing_the_current_cache_guard_changes_the_actual_probe_reply:
  "snd(execute_current_without_cache_guard 0(Client_Protocol 0 0(Time_Intent 0))
      (sample.install_snapshot_probe 0(capture_snapshot(observed_core(history_example_tick 1)))
        (history_example_tick 2)))=Effect_Reply Internal_Completed \<and>
    snd(sample.execute_observed(current_snapshot_probe 0)
      (sample.install_snapshot_probe 0(capture_snapshot(observed_core(history_example_tick 1)))
        (history_example_tick 2)))=Observation_Busy"
  by (simp del: One_nat_def add: execute_current_without_cache_guard_def store_core_result_def
      sample.actual_zero_time_client_reply sample.actual_snapshot_probe_reply
      distinct_clock_inputs_have_different_complete_snapshots Let_def)

text \<open>The original modeled environment supplies each cache, and the
  original client executes the clock request. The two executions have the
  same authority revision but different financial clocks. Their historical
  clocks can be normalized without changing historical queries. Their
  complete current snapshots remain distinguishable by the actual cache
  admission interface. Removing that single admission guard allows the
  request that the original consumer completes as Busy.\<close>

end
