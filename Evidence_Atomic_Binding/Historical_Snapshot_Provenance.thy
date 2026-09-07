(* SPDX-License-Identifier: BSD-3-Clause *)
theory Historical_Snapshot_Provenance
  imports Abstract_Observation_Types
begin

lemma captured_snapshot_has_the_source_revision:
  "snapshot_revision(capture_snapshot core)=core_epoch core"
  by (simp add: capture_snapshot_def)

definition history_change_is_capture :: "observed_finality \<Rightarrow> observed_finality \<Rightarrow> bool" where
  "history_change_is_capture before after \<longleftrightarrow>
    (\<forall>revision cache. historical_snapshots after revision=Some cache \<longrightarrow>
      historical_snapshots before revision=Some cache \<or>
      (cache=capture_snapshot(observed_core after) \<and> snapshot_revision cache=revision))"

lemma history_change_refl [simp]: "history_change_is_capture s s"
  by (simp add: history_change_is_capture_def)

lemma cache_update_does_not_invent_history [simp]:
  "history_change_is_capture s(s\<lparr>endpoint_cache:=cache\<rparr>)"
  "history_change_is_capture s(s\<lparr>secondary_progress:=progress\<rparr>)"
  by (simp_all add: history_change_is_capture_def)

lemma stored_core_result_captures_its_actual_history:
  "history_change_is_capture s(fst(store_core_result result s))"
  by (auto simp: history_change_is_capture_def store_core_result_def Let_def
      captured_snapshot_has_the_source_revision split: if_splits)

context source_attestation
begin

lemma protected_read_history_is_created_by_its_actual_core:
  "history_change_is_capture s(fst(execute_protected_current endpoint index r query s))"
  by (auto simp: execute_protected_current_def Let_def
      intro: stored_core_result_captures_its_actual_history
      split: if_splits observed_reply.splits application_query.splits finality_reply.splits reservation_reply.splits)

theorem actual_observed_callback_captures_only_its_own_history:
  "history_change_is_capture s(fst(execute_observed command s))"
  by (cases command)
    (auto intro: protected_read_history_is_created_by_its_actual_core
      stored_core_result_captures_its_actual_history)

theorem actual_environment_callback_captures_only_its_own_history:
  "history_change_is_capture s(fst(execute_observed_environment input s))"
  by (cases input) (auto intro: stored_core_result_captures_its_actual_history)

fun observed_entry_after :: "(observed_command,observed_reply,observed_environment) authority_call_entry
  \<Rightarrow> observed_finality \<Rightarrow> observed_finality" where
  "observed_entry_after(Authority_Executed call_id command reply)s=fst(execute_observed command s)"
| "observed_entry_after(Authority_Input input reply)s=fst(execute_observed_environment input s)"

lemma entry_history_is_capture:
  "history_change_is_capture s(observed_entry_after entry s)"
  by (cases entry)
    (simp_all add: actual_observed_callback_captures_only_its_own_history
      actual_environment_callback_captures_only_its_own_history)

lemma observed_replay_cons:
  "observed_calls.replay_call_authority(entry#entries)s=
    observed_calls.replay_call_authority entries(observed_entry_after entry s)"
  by (cases entry) (simp_all only: observed_calls.replay_call_authority.simps observed_entry_after.simps)

fun observed_source_states :: "(observed_command,observed_reply,observed_environment) authority_call_entry list
  \<Rightarrow> observed_finality \<Rightarrow> observed_finality list" where
  "observed_source_states [] s=[s]"
| "observed_source_states(entry#entries)s=s#observed_source_states entries(observed_entry_after entry s)"

lemma initial_state_is_a_source_cut [simp]: "s\<in>set(observed_source_states entries s)"
  by (cases entries) simp_all

theorem replayed_snapshot_is_initial_or_created_at_an_actual_source_cut:
  assumes "historical_snapshots(observed_calls.replay_call_authority entries initial)revision=Some cache"
  shows "historical_snapshots initial revision=Some cache \<or>
    (\<exists>source_cut\<in>set(observed_source_states entries initial).
      cache=capture_snapshot(observed_core source_cut) \<and> snapshot_revision cache=revision)"
  using assms
proof (induction entries arbitrary:initial)
  case Nil
  then show ?case by simp
next
  case (Cons entry entries)
  let ?next = "observed_entry_after entry initial"
  have following: "historical_snapshots(observed_calls.replay_call_authority entries ?next)revision=Some cache"
    using Cons.prems by (simp only: observed_replay_cons)
  have tail: "historical_snapshots ?next revision=Some cache \<or>
    (\<exists>source_cut\<in>set(observed_source_states entries ?next).
      cache=capture_snapshot(observed_core source_cut) \<and> snapshot_revision cache=revision)"
    by (rule Cons.IH[OF following])
  have created: "historical_snapshots ?next revision=Some cache \<Longrightarrow>
    historical_snapshots initial revision=Some cache \<or>
    (cache=capture_snapshot(observed_core ?next) \<and> snapshot_revision cache=revision)"
    using entry_history_is_capture[of initial entry] unfolding history_change_is_capture_def by blast
  show ?case using tail created initial_state_is_a_source_cut[of ?next entries] by auto
qed

theorem every_source_cut_is_a_real_replay_prefix:
  assumes "source_cut\<in>set(observed_source_states entries initial)"
  shows "\<exists>index\<le>length entries.
    source_cut=observed_calls.replay_call_authority(take index entries)initial"
  using assms
proof (induction entries arbitrary:initial)
  case Nil
  then show ?case by simp
next
  case (Cons entry entries)
  show ?case
  proof (cases "source_cut=initial")
    case True
    show ?thesis by (intro exI[where x=0]) (simp add: True)
  next
    case False
    have member: "source_cut\<in>set(observed_source_states entries(observed_entry_after entry initial))"
      using Cons.prems False by simp
    obtain index where bound: "index\<le>length entries"
      and at: "source_cut=observed_calls.replay_call_authority(take index entries)(observed_entry_after entry initial)"
      using Cons.IH[OF member] by blast
    show ?thesis by (intro exI[where x="Suc index"])
      (simp add: bound at observed_replay_cons)
  qed
qed

theorem snapshots_from_an_actual_initial_view_have_real_history:
  assumes stored: "historical_snapshots(observed_calls.replay_call_authority entries
    (initial_observed_finality initial_core))revision=Some cache"
  shows "\<exists>index\<le>length entries.
    cache=capture_snapshot(observed_core(observed_calls.replay_call_authority(take index entries)
      (initial_observed_finality initial_core))) \<and> snapshot_revision cache=revision"
proof -
  have origin: "historical_snapshots(initial_observed_finality initial_core)revision=Some cache \<or>
    (\<exists>source_cut\<in>set(observed_source_states entries(initial_observed_finality initial_core)).
      cache=capture_snapshot(observed_core source_cut) \<and> snapshot_revision cache=revision)"
    by (rule replayed_snapshot_is_initial_or_created_at_an_actual_source_cut[OF stored])
  show ?thesis
  proof (cases "historical_snapshots(initial_observed_finality initial_core)revision=Some cache")
    case True
    have snapshot: "cache=capture_snapshot initial_core" and revision: "snapshot_revision cache=revision"
      using True by (auto simp: initial_observed_finality_def captured_snapshot_has_the_source_revision split: if_splits)
    have initial_revision: "snapshot_revision(capture_snapshot initial_core)=revision"
      using revision by (simp only: snapshot)
    show ?thesis by (intro exI[where x=0])
      (simp add: snapshot initial_revision initial_observed_finality_def)
  next
    case False
    obtain source_cut where member: "source_cut\<in>set(observed_source_states entries(initial_observed_finality initial_core))"
      and snapshot: "cache=capture_snapshot(observed_core source_cut)" and revision: "snapshot_revision cache=revision"
      using origin False by blast
    obtain index where bound: "index\<le>length entries"
      and at: "source_cut=observed_calls.replay_call_authority(take index entries)(initial_observed_finality initial_core)"
      using every_source_cut_is_a_real_replay_prefix[OF member] by blast
    show ?thesis using bound at snapshot revision by blast
  qed
qed

text \<open>Historical snapshots are produced by actual callback execution,
  not supplied as trusted client history. Every stored snapshot from the
  real initial view belongs to a replay prefix of the authoritative source
  log and has the revision under which it is stored. Local cache corruption
  is allowed by the input alphabet but cannot create historical authority.
  This provenance result is separate from checking the current read role
  and from interpreting the snapshot's query value.\<close>

end

end
