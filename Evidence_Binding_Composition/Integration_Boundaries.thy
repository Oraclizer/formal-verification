(* SPDX-License-Identifier: BSD-3-Clause *)
theory Integration_Boundaries
  imports "Evidence_Atomic_Binding.Sourced_Observations"
    "Evidence_Atomic_Binding.Finality_Recovery"
begin

section \<open>The Current Cache Interface Distinguishes Full Snapshots\<close>

definition current_snapshot_probe :: "nat \<Rightarrow> observed_command" where
  "current_snapshot_probe endpoint =
    Execute_Current endpoint(Client_Protocol endpoint 0(Time_Intent 0))"

context source_attestation
begin

lemma actual_zero_time_client_reply:
  "snd(execute_finality_client(Client_Protocol endpoint index(Time_Intent 0))core)=Internal_Completed"
  by (simp add: execute_finality_client_def invoke_protocol_def Let_def)

definition install_snapshot_probe :: "nat \<Rightarrow> endpoint_snapshot \<Rightarrow>
  observed_finality \<Rightarrow> observed_finality" where
  "install_snapshot_probe endpoint snapshot state =
    fst(execute_observed_environment(Corrupt_Endpoint_Cache endpoint(Some snapshot))state)"

theorem actual_snapshot_probe_reply:
  "snd(execute_observed(current_snapshot_probe endpoint)
    (install_snapshot_probe endpoint snapshot state)) =
    (if snapshot=capture_snapshot(observed_core state)
     then Effect_Reply Internal_Completed else Observation_Busy)"
  by (simp add: current_snapshot_probe_def install_snapshot_probe_def
      current_cache_valid_def store_core_result_def actual_zero_time_client_reply Let_def)

theorem current_snapshot_equality_iff_all_actual_cache_probes:
  "capture_snapshot(observed_core first)=capture_snapshot(observed_core second) \<longleftrightarrow>
    (\<forall>snapshot. snd(execute_observed(current_snapshot_probe endpoint)
       (install_snapshot_probe endpoint snapshot first)) =
      snd(execute_observed(current_snapshot_probe endpoint)
       (install_snapshot_probe endpoint snapshot second)))"
proof
  assume same: "capture_snapshot(observed_core first)=capture_snapshot(observed_core second)"
  show "\<forall>snapshot. snd(execute_observed(current_snapshot_probe endpoint)
       (install_snapshot_probe endpoint snapshot first)) =
      snd(execute_observed(current_snapshot_probe endpoint)
       (install_snapshot_probe endpoint snapshot second))"
    by (simp add: actual_snapshot_probe_reply same)
next
  assume same: "\<forall>snapshot. snd(execute_observed(current_snapshot_probe endpoint)
       (install_snapshot_probe endpoint snapshot first)) =
      snd(execute_observed(current_snapshot_probe endpoint)
       (install_snapshot_probe endpoint snapshot second))"
  have at_first:
    "snd(execute_observed(current_snapshot_probe endpoint)
       (install_snapshot_probe endpoint(capture_snapshot(observed_core first))first)) =
      snd(execute_observed(current_snapshot_probe endpoint)
       (install_snapshot_probe endpoint(capture_snapshot(observed_core first))second))"
    using same by blast
  show "capture_snapshot(observed_core first)=capture_snapshot(observed_core second)"
    using at_first by (simp add: actual_snapshot_probe_reply split: if_splits)
qed

theorem an_exact_probe_representation_must_separate_current_snapshots:
  assumes same: "representation first=representation second"
    and reconstructs: "\<And>state snapshot. decision(representation state)snapshot =
      snd(execute_observed(current_snapshot_probe endpoint)
        (install_snapshot_probe endpoint snapshot state))"
  shows "capture_snapshot(observed_core first)=capture_snapshot(observed_core second)"
proof -
  have probes: "\<forall>snapshot. snd(execute_observed(current_snapshot_probe endpoint)
       (install_snapshot_probe endpoint snapshot first)) =
      snd(execute_observed(current_snapshot_probe endpoint)
       (install_snapshot_probe endpoint snapshot second))"
    using same reconstructs by metis
  show ?thesis using current_snapshot_equality_iff_all_actual_cache_probes probes by blast
qed

section \<open>Raw Histories Remain Distinguishable\<close>

theorem actual_raw_journal_equality_iff:
  "snd(execute_observed Read_Raw_Journal first)=snd(execute_observed Read_Raw_Journal second)
    \<longleftrightarrow> machine_journal(core_parent(observed_core first))=
      machine_journal(core_parent(observed_core second))"
  by simp

definition source_effect_probe :: "sourced_observation_state \<Rightarrow> sourced_reply" where
  "source_effect_probe state = snd(execute_sourced_request Inspect_Source_Effects
    (fst(execute_sourced_environment(Set_Source_Availability True)state)))"

theorem actual_source_effect_probe_equality_iff:
  "source_effect_probe first=source_effect_probe second \<longleftrightarrow>
    boundary_effects(controlled_endpoint(coupled_source(observation_source first)))=
    boundary_effects(controlled_endpoint(coupled_source(observation_source second)))"
  by (simp add: source_effect_probe_def)

text \<open>The probes use the existing environment and request constructors.
  They give necessary information for preserving that declared interface,
  including cache-corruption inputs and later source availability. A fixed
  unavailable source or a permanently rejected request has a different
  observation class. These statements do not equate all production APIs with
  the modeled command datatypes.\<close>

end

section \<open>Exact Recovery Admission Reads Genesis and the Entire Journal\<close>

context durable_call_protocol
begin

theorem actual_current_replay_admission_is_exact:
  assumes contract: "authority_replay_contract source"
  shows "checked_current_replay source candidate\<noteq>None \<longleftrightarrow>
    candidate_genesis candidate=call_genesis source \<and>
    candidate_entries candidate=call_authority_log source"
  using contract
  by (auto simp: checked_current_replay_def authority_replay_contract_def)

theorem current_replay_evidence_equality_iff_all_candidate_admissions:
  assumes first: "authority_replay_contract first_source"
    and second: "authority_replay_contract second_source"
  shows "(call_genesis first_source=call_genesis second_source \<and>
      call_authority_log first_source=call_authority_log second_source) \<longleftrightarrow>
    (\<forall>candidate. (checked_current_replay first_source candidate\<noteq>None)=
      (checked_current_replay second_source candidate\<noteq>None))"
proof
  assume same: "call_genesis first_source=call_genesis second_source \<and>
    call_authority_log first_source=call_authority_log second_source"
  show "\<forall>candidate. (checked_current_replay first_source candidate\<noteq>None)=
      (checked_current_replay second_source candidate\<noteq>None)"
    by (simp only: actual_current_replay_admission_is_exact[OF first]
        actual_current_replay_admission_is_exact[OF second]; use same in simp)
next
  assume same: "\<forall>candidate. (checked_current_replay first_source candidate\<noteq>None)=
      (checked_current_replay second_source candidate\<noteq>None)"
  have first_accepts:
    "checked_current_replay first_source(current_source_candidate first_source)\<noteq>None"
    by (simp add: actual_source_produces_a_valid_complete_candidate[OF first])
  have second_accepts:
    "checked_current_replay second_source(current_source_candidate first_source)\<noteq>None"
    using same first_accepts by blast
  have data:
    "candidate_genesis(current_source_candidate first_source)=call_genesis second_source \<and>
      candidate_entries(current_source_candidate first_source)=call_authority_log second_source"
    using actual_current_replay_admission_is_exact[OF second,
      of "current_source_candidate first_source"] second_accepts by blast
  show "call_genesis first_source=call_genesis second_source \<and>
      call_authority_log first_source=call_authority_log second_source"
    using data by (simp add: current_source_candidate_def)
qed

lemma dispatch_always_records_one_call_event:
  "length(call_history(dispatch_client_call call_id command machine))=
    Suc(length(call_history machine))"
  by (auto simp: dispatch_client_call_def execute_authority_once_def Let_def
      split: option.splits prod.splits if_splits)

theorem actual_recovered_dispatch_admission_is_exact:
  "recovery_source(dispatch_from_recovered_replica call_id command runtime)\<noteq>
      recovery_source runtime \<longleftrightarrow>
    recovery_connected runtime \<and>
      recovery_replica runtime=Some(call_authority_state(recovery_source runtime))"
proof -
  have changed:
    "dispatch_client_call call_id command(recovery_source runtime)\<noteq>recovery_source runtime"
  proof
    assume same: "dispatch_client_call call_id command(recovery_source runtime)=recovery_source runtime"
    have "length(call_history(recovery_source runtime))=Suc(length(call_history(recovery_source runtime)))"
      using dispatch_always_records_one_call_event[of call_id command "recovery_source runtime"] same
      by simp
    then show False by simp
  qed
  show ?thesis using changed
    by (simp add: dispatch_from_recovered_replica_def split: if_splits)
qed

theorem a_changed_representation_is_not_an_exact_recovery_replica:
  assumes changed: "represented\<noteq>call_authority_state(recovery_source runtime)"
    and connected: "recovery_connected runtime"
  shows "dispatch_from_recovered_replica call_id command(runtime\<lparr>recovery_replica:=Some represented\<rparr>)=
      runtime\<lparr>recovery_replica:=Some represented\<rparr>"
    "recovery_source(dispatch_from_recovered_replica call_id command
       (runtime\<lparr>recovery_replica:=Some(call_authority_state(recovery_source runtime))\<rparr>))\<noteq>
       recovery_source runtime"
proof -
  show "dispatch_from_recovered_replica call_id command(runtime\<lparr>recovery_replica:=Some represented\<rparr>)=
      runtime\<lparr>recovery_replica:=Some represented\<rparr>"
    using changed by (simp add: dispatch_from_recovered_replica_def)
  show "recovery_source(dispatch_from_recovered_replica call_id command
       (runtime\<lparr>recovery_replica:=Some(call_authority_state(recovery_source runtime))\<rparr>))\<noteq>
       recovery_source runtime"
    using actual_recovered_dispatch_admission_is_exact[of call_id command
      "runtime\<lparr>recovery_replica:=Some(call_authority_state(recovery_source runtime))\<rparr>"] connected
    by simp
qed

text \<open>These are classifications of the current executable recovery
  checks. They do not assert that every correct recovery algorithm must retain
  the same fields. A different representation needs its own decoder and
  comparison proof. The current source supplies complete authenticated input;
  the classifications do not manufacture source authenticity or currentness.\<close>

end

end
