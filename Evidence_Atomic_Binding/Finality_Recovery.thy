(* SPDX-License-Identifier: BSD-3-Clause *)
theory Finality_Recovery
  imports Finality_Calls Finality_Records Transfer_Ledger_Refinement
begin

section \<open>Candidate Journals and the Current Authoritative Source\<close>

record ('state,'command,'reply,'environment) recovery_candidate =
  candidate_genesis :: 'state
  candidate_entries :: "('command,'reply,'environment) authority_call_entry list"

definition current_source_candidate ::
  "('state,'command,'reply,'environment) durable_call_machine \<Rightarrow>
   ('state,'command,'reply,'environment) recovery_candidate" where
  "current_source_candidate m=\<lparr>candidate_genesis=call_genesis m,
    candidate_entries=call_authority_log m\<rparr>"

record ('state,'command,'reply,'environment) recovered_call_runtime =
  recovery_source :: "('state,'command,'reply,'environment) durable_call_machine"
  recovery_replica :: "'state option"
  recovery_connected :: bool

context durable_call_protocol
begin

definition checked_current_replay ::
  "('state,'command,'reply,'environment) durable_call_machine \<Rightarrow>
   ('state,'command,'reply,'environment) recovery_candidate \<Rightarrow> 'state option" where
  "checked_current_replay source candidate=
    (if candidate_genesis candidate=call_genesis source \<and>
        candidate_entries candidate=call_authority_log source \<and>
        authentic_call_history(candidate_entries candidate)(candidate_genesis candidate)
     then Some(replay_call_authority(candidate_entries candidate)(candidate_genesis candidate)) else None)"

definition replay_without_current_source ::
  "('state,'command,'reply,'environment) recovery_candidate \<Rightarrow> 'state option" where
  "replay_without_current_source candidate=
    (if authentic_call_history(candidate_entries candidate)(candidate_genesis candidate)
     then Some(replay_call_authority(candidate_entries candidate)(candidate_genesis candidate)) else None)"

definition restore_current_replica ::
  "('state,'command,'reply,'environment) recovery_candidate \<Rightarrow>
   ('state,'command,'reply,'environment) recovered_call_runtime \<Rightarrow>
   ('state,'command,'reply,'environment) recovered_call_runtime" where
  "restore_current_replica candidate runtime=runtime\<lparr>recovery_replica:=
    if recovery_connected runtime then checked_current_replay(recovery_source runtime)candidate else None\<rparr>"

definition dispatch_from_recovered_replica ::
  "client_call_id \<Rightarrow> 'command \<Rightarrow>
   ('state,'command,'reply,'environment) recovered_call_runtime \<Rightarrow>
   ('state,'command,'reply,'environment) recovered_call_runtime" where
  "dispatch_from_recovered_replica call_id command runtime=
    (if recovery_connected runtime \<and>
        recovery_replica runtime=Some(call_authority_state(recovery_source runtime))
     then runtime\<lparr>recovery_source:=dispatch_client_call call_id command(recovery_source runtime),
       recovery_replica:=None\<rparr> else runtime)"

theorem valid_current_replay_is_the_actual_source_state:
  assumes contract: "authority_replay_contract source"
    and decoded: "checked_current_replay source candidate=Some state"
  shows "state=call_authority_state source"
  using contract decoded
  by (auto simp: checked_current_replay_def authority_replay_contract_def split: if_splits)

theorem actual_source_produces_a_valid_complete_candidate:
  assumes "authority_replay_contract source"
  shows "checked_current_replay source(current_source_candidate source)=Some(call_authority_state source)"
  using assms by (simp add: checked_current_replay_def current_source_candidate_def authority_replay_contract_def)

theorem generated_source_supplies_recovery_without_a_truth_flag:
  "checked_current_replay(run_calls actions(initial_call_machine initial))
      (current_source_candidate(run_calls actions(initial_call_machine initial)))=
    Some(call_authority_state(run_calls actions(initial_call_machine initial)))"
  by (rule actual_source_produces_a_valid_complete_candidate)
    (use generated_call_contracts[of actions initial] in blast)

lemma shortened_journal_is_rejected:
  "length(candidate_entries candidate)<length(call_authority_log source) \<Longrightarrow>
    checked_current_replay source candidate=None"
  by (auto simp: checked_current_replay_def)

lemma duplicate_or_extended_journal_is_rejected:
  "length(call_authority_log source)<length(candidate_entries candidate) \<Longrightarrow>
    checked_current_replay source candidate=None"
  by (auto simp: checked_current_replay_def)

lemma reordered_or_conflicting_journal_is_rejected:
  "candidate_entries candidate\<noteq>call_authority_log source \<Longrightarrow>
    checked_current_replay source candidate=None"
  by (simp add: checked_current_replay_def)

lemma wrong_genesis_is_rejected:
  "candidate_genesis candidate\<noteq>call_genesis source \<Longrightarrow>
    checked_current_replay source candidate=None"
  by (simp add: checked_current_replay_def)

lemma unavailable_source_does_not_reconstruct_a_state:
  "\<not>recovery_connected runtime \<Longrightarrow>
    recovery_replica(restore_current_replica candidate runtime)=None"
  by (simp add: restore_current_replica_def)

lemma restoration_does_not_execute_or_refund:
  "recovery_source(restore_current_replica candidate runtime)=recovery_source runtime"
  by (simp add: restore_current_replica_def)

theorem restored_dispatch_is_the_actual_guarded_call:
  assumes source_contract: "authority_replay_contract(recovery_source runtime)"
    and connected: "recovery_connected runtime"
    and recovered: "checked_current_replay(recovery_source runtime)candidate=Some state"
  shows "recovery_source(dispatch_from_recovered_replica call_id command
      (restore_current_replica candidate runtime))=
    dispatch_client_call call_id command(recovery_source runtime)"
  using valid_current_replay_is_the_actual_source_state[OF source_contract recovered] recovered connected
  by (simp add: dispatch_from_recovered_replica_def restore_current_replica_def)

theorem stale_replica_cannot_bypass_the_current_source:
  "recovery_replica runtime\<noteq>Some(call_authority_state(recovery_source runtime)) \<Longrightarrow>
    dispatch_from_recovered_replica call_id command runtime=runtime"
  by (simp add: dispatch_from_recovered_replica_def)

end

context source_attestation
begin

theorem finality_recovery_keeps_terminal_records_and_financial_lineage:
  assumes contract: "finality_calls.authority_replay_contract source"
    and decoded: "finality_calls.checked_current_replay source candidate=Some state"
  shows "core_records state=core_records(call_authority_state source) \<and>
    core_published state=core_published(call_authority_state source) \<and>
    transfer_projection(core_parent state)=transfer_projection(core_parent(call_authority_state source))"
  using finality_calls.valid_current_replay_is_the_actual_source_state[OF contract decoded] by simp

theorem recovered_continuation_rechecks_the_current_policy:
  assumes contract: "finality_calls.authority_replay_contract source"
    and decoded: "finality_calls.checked_current_replay source candidate=Some state"
  shows "execute_finality_client command state=execute_finality_client command(call_authority_state source)"
  using finality_calls.valid_current_replay_is_the_actual_source_state[OF contract decoded] by simp

end

section \<open>A Real Truncated Descendant History\<close>

definition truncated_descendant_candidate where
  "truncated_descendant_candidate=\<lparr>candidate_genesis=call_example_ready,candidate_entries=[]\<rparr>"

lemma empty_candidate_is_replayable_but_does_not_have_the_descendant:
  "sample.finality_calls.replay_without_current_source truncated_descendant_candidate=Some call_example_ready"
  by (simp add: sample.finality_calls.replay_without_current_source_def truncated_descendant_candidate_def)

lemma actual_descendant_source_rejects_truncated_candidate:
  "sample.finality_calls.checked_current_replay call_example_once truncated_descendant_candidate=None"
  by (simp add: sample.finality_calls.checked_current_replay_def truncated_descendant_candidate_def
      call_example_once_def initial_call_machine_def sample.finality_calls.call_definitions Let_def)

lemma exact_descendant_source_recovers_the_real_completed_effect:
  "sample.finality_calls.checked_current_replay call_example_once(current_source_candidate call_example_once)=
    Some(call_authority_state call_example_once)"
  unfolding call_example_once_def
  by (rule sample.finality_calls.generated_source_supplies_recovery_without_a_truth_flag)

lemma removal_of_current_source_check_loses_actual_descendant_funding:
  "destination_units(machine_state(core_parent call_example_ready))(2,17,4)=0 \<and>
    destination_units(machine_state(core_parent(call_authority_state call_example_once)))(2,17,4)=1"
  using actual_descendant_call_succeeds
  by (simp add: call_example_ready_parent sample_credited_state)

text \<open>A syntactically valid, internally replayable candidate need not
  be the authoritative complete history. The checker reads the current source
  independently of the candidate. Missing prefixes or tails, extra entries,
  changed ordering, conflicts and a wrong genesis are rejected by that exact
  comparison. Identical entries swapped without changing the list are not a
  distinct input. The physical authenticity, durability and freshness of this
  authority read are implementation obligations. When it cannot be obtained,
  recovery returns no state and creates no funds or authority.

  Source execution and its durable result are one modeled boundary. A local
  response may be lost after that boundary, as the call protocol demonstrates.
  An external effect occurring before this authoritative record is a different
  failure model and must be reconciled with authenticated source evidence;
  the source-boundary model retains that unknown outcome rather than treating
  absence in a local journal as a refund instruction.\<close>

end
