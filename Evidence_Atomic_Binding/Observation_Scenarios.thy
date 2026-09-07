(* SPDX-License-Identifier: BSD-3-Clause *)
theory Observation_Scenarios
  imports Finality_Progress
begin

definition observation_example_initial where
  "observation_example_initial=initial_observed_finality call_example_ready"

definition observation_example_cached where
  "observation_example_cached=fst(sample.execute_observed(Refresh_Endpoint 3)
    (fst(sample.execute_observed(Refresh_Endpoint 2)observation_example_initial)))"

definition observation_example_advanced where
  "observation_example_advanced=fst(sample.execute_observed(Execute_Current 2 call_example_command)
    observation_example_cached)"

definition observation_example_mixed where
  "observation_example_mixed=fst(sample.execute_observed(Refresh_Endpoint 2)observation_example_advanced)"

lemma example_first_core_revision:
  "core_epoch call_example_ready=2" "core_epoch call_example_first_core=3"
  by (simp_all add: call_example_ready_shape call_example_seed_def initial_finality_core_def
      call_example_first_core_def sample.execute_finality_client_def)

lemma observation_example_core_and_caches:
  "observed_core observation_example_mixed=call_example_first_core"
  "endpoint_cache observation_example_mixed 2=Some(capture_snapshot call_example_first_core)"
  "endpoint_cache observation_example_mixed 3=Some(capture_snapshot call_example_ready)"
  by (simp_all add: observation_example_mixed_def observation_example_advanced_def
      observation_example_cached_def observation_example_initial_def initial_observed_finality_def
      current_cache_valid_def store_core_result_def call_example_first_core_def Let_def)

lemma ready_root_views_allow_both_holder_queries:
  "snapshot_query_ready(Destination_Balance(2,17,4))(capture_snapshot call_example_ready)"
  "snapshot_query_ready(Destination_Balance(2,17,4))(capture_snapshot call_example_first_core)"
  by (simp_all add: snapshot_query_ready_def capture_snapshot_def call_example_ready_shape
      call_example_seed_def initial_finality_core_def call_example_terminal_def call_example_first_core_frame
      call_example_first_core_parent call_example_parent_once_def call_example_parent_definitions)

lemma mixed_endpoints_have_a_new_value_and_a_stale_busy_reply:
  "snd(sample.execute_observed(Read_Current 2(Destination_Balance(2,17,4)))observation_example_mixed)=
      Current_Value 3(Units_Value 1) \<and>
    snd(sample.execute_observed(Read_Current 3(Destination_Balance(2,17,4)))observation_example_mixed)=
      Observation_Busy"
proof -
  have queried: "stored_query(Destination_Balance(2,17,4))(capture_snapshot call_example_first_core)=Units_Value 1"
    by (simp add: capture_snapshot_def call_example_first_core_parent call_example_parent_first_amount)
  have queried_units: "destination_units(snapshot_financial(capture_snapshot call_example_first_core))(2,17,4)=1"
    using queried by (simp only: stored_query.simps application_value.inject)
  have current_revision: "snapshot_revision(capture_snapshot call_example_first_core)=3"
    by (simp add: capture_snapshot_def example_first_core_revision)
  have fresh: "snd(sample.execute_observed(Read_Current 2(Destination_Balance(2,17,4)))observation_example_mixed)=
    Current_Value 3(Units_Value 1)"
    by (simp add: current_query_reply_def current_cache_valid_def observation_example_core_and_caches
        ready_root_views_allow_both_holder_queries queried_units current_revision
        example_first_core_revision)
  have old: "snd(sample.execute_observed(Read_Current 3(Destination_Balance(2,17,4)))observation_example_mixed)=Observation_Busy"
    by (rule sample.stale_cache_cannot_complete_as_current[
          where cache="capture_snapshot call_example_ready"])
      (simp_all add: observation_example_core_and_caches capture_snapshot_def example_first_core_revision)
  show ?thesis using fresh old by blast
qed

definition current_read_without_authority_barrier :: "nat \<Rightarrow> application_query \<Rightarrow>
  observed_finality \<Rightarrow> observed_reply" where
  "current_read_without_authority_barrier endpoint query state=(case endpoint_cache state endpoint of
    None \<Rightarrow> Observation_Unavailable
   | Some cache \<Rightarrow> if snapshot_query_ready query cache
     then Current_Value(snapshot_revision cache)(stored_query query cache) else Observation_Busy)"

lemma deleting_the_barrier_accepts_the_real_older_endpoint:
  "current_read_without_authority_barrier 3(Destination_Balance(2,17,4))observation_example_mixed=
    Current_Value 2(Units_Value 0)"
proof -
  have cache_at: "endpoint_cache observation_example_mixed 3=Some(capture_snapshot call_example_ready)"
    by (rule observation_example_core_and_caches(3))
  have old_ready: "snapshot_query_ready(Destination_Balance(2,17,4))(capture_snapshot call_example_ready)"
    by (rule ready_root_views_allow_both_holder_queries(1))
  have old_payload: "stored_query(Destination_Balance(2,17,4))(capture_snapshot call_example_ready)=Units_Value 0"
    by (simp add: capture_snapshot_def call_example_ready_parent sample_credited_state)
  have old_cut: "snapshot_revision(capture_snapshot call_example_ready)=2"
    by (simp add: capture_snapshot_def example_first_core_revision)
  show ?thesis
    by (simp only: current_read_without_authority_barrier_def cache_at option.case old_ready
        if_True old_payload old_cut)
qed

definition revision_only_current_read :: "nat \<Rightarrow> application_query \<Rightarrow>
  observed_finality \<Rightarrow> observed_reply" where
  "revision_only_current_read endpoint query state=(case endpoint_cache state endpoint of
    None \<Rightarrow> Observation_Unavailable
   | Some cache \<Rightarrow> if snapshot_revision cache=core_epoch(observed_core state) \<and>
       snapshot_query_ready query cache
     then Current_Value(snapshot_revision cache)(stored_query query cache) else Observation_Busy)"

definition forged_same_revision where
  "forged_same_revision=(capture_snapshot call_example_ready)\<lparr>snapshot_financial:=
    (machine_state(core_parent call_example_ready))\<lparr>destination_units:=
      (destination_units(machine_state(core_parent call_example_ready)))((2,17,4):=9)\<rparr>\<rparr>"

definition observation_forged where
  "observation_forged=fst(sample.execute_observed_environment
    (Corrupt_Endpoint_Cache 2(Some forged_same_revision))observation_example_initial)"

lemma a_matching_revision_number_does_not_authenticate_the_cached_value:
  "revision_only_current_read 2(Destination_Balance(2,17,4))observation_forged=
      Current_Value 2(Units_Value 9) \<and>
    snd(sample.execute_observed(Read_Current 2(Destination_Balance(2,17,4)))observation_forged)=Observation_Busy"
proof -
  have actual_units: "destination_units(snapshot_financial(capture_snapshot call_example_ready))(2,17,4)=0"
    by (simp add: capture_snapshot_def call_example_ready_parent sample_credited_state)
  have forged_units: "destination_units(snapshot_financial forged_same_revision)(2,17,4)=9"
    by (simp add: forged_same_revision_def capture_snapshot_def)
  have forged_cut: "snapshot_revision forged_same_revision=2"
    by (simp add: forged_same_revision_def capture_snapshot_def example_first_core_revision)
  have ready_frame: "snapshot_query_ready(Destination_Balance(2,17,4))forged_same_revision =
    snapshot_query_ready(Destination_Balance(2,17,4))(capture_snapshot call_example_ready)"
    by (simp add: forged_same_revision_def snapshot_query_ready_def capture_snapshot_def)
  have forged_ready: "snapshot_query_ready(Destination_Balance(2,17,4))forged_same_revision"
    using ready_frame ready_root_views_allow_both_holder_queries(1) by blast
  have view_core: "observed_core observation_forged=call_example_ready"
    and cache_at: "endpoint_cache observation_forged 2=Some forged_same_revision"
    by (simp_all add: observation_forged_def observation_example_initial_def initial_observed_finality_def)
  have different: "forged_same_revision\<noteq>capture_snapshot call_example_ready"
  proof
    assume same: "forged_same_revision=capture_snapshot call_example_ready"
    have scalar_equal: "destination_units(snapshot_financial forged_same_revision)(2,17,4) =
      destination_units(snapshot_financial(capture_snapshot call_example_ready))(2,17,4)"
      by (rule arg_cong[OF same,where f="\<lambda>cache. destination_units(snapshot_financial cache)(2,17,4)"])
    show False using scalar_equal forged_units actual_units by linarith
  qed
  have invalid_cache: "\<not>current_cache_valid observation_forged 2"
    using different by (simp add: current_cache_valid_def cache_at view_core)
  have admitted_by_revision: "revision_only_current_read 2(Destination_Balance(2,17,4))observation_forged =
    Current_Value 2(Units_Value 9)"
    by (simp add: revision_only_current_read_def cache_at view_core forged_cut
        example_first_core_revision forged_ready forged_units)
  have rejected_by_current_source:
    "snd(sample.execute_observed(Read_Current 2(Destination_Balance(2,17,4)))observation_forged)=Observation_Busy"
    by (simp add: current_query_reply_def cache_at invalid_cache)
  show ?thesis using admitted_by_revision rejected_by_current_source by blast
qed

lemma a_completed_busy_value_does_not_change_when_the_endpoint_catches_up:
  assumes "call_completions machine call_id=Some Observation_Busy"
  shows "sample.observed_calls.complete_client_call call_id machine=machine"
  by (rule sample.observed_calls.completed_calls_are_not_completed_twice[OF assms])

text \<open>Both caches were populated from the actual authority before a
  successful descendant transfer. The new endpoint is then refreshed, while
  the old endpoint retains its real older value. Removing only the authority
  barrier accepts that old revision. Separately, an explicitly allowed cache
  corruption preserves the revision number while changing the balance; a
  revision-only comparison accepts it. These are different failure modes.
  The arbitrary nonoverlapping-call theorem binds successful replies to their
  real source order, and completed Busy replies remain completed across later
  endpoint catch-up.\<close>

end
