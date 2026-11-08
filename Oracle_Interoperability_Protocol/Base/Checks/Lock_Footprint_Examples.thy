theory Lock_Footprint_Examples
  imports "../Lock_Footprint"
begin

definition pair_lock_core where
  "pair_lock_core = (initial_finality_core sample_balances (sample_metadata ACTIVE) (\<lambda>_. sample_pair_context))
    \<lparr>core_parent := sample_pair_held\<rparr>"

lemma pair_lock_has_authoritative_dependency:
  "\<exists>res. reservation_at (machine_state (core_parent pair_lock_core)) (binding_key (request_binding (sample_request 17))) = Some res \<and>
    30 \<in> set (reservation_footprint res) \<and> asset_version (machine_state (core_parent pair_lock_core)) 30 = 0"
  by (simp add: pair_lock_core_def sample_pair_held_def sample_pair_context_def sample_data_defs
      acquire_reservation_def record_observation_def commit_reservation_event_def Let_def)

lemma stale_dependency_version_rejects_pair_dispatch:
  "let result = sample.invoke_protocol 0 (core_epoch pair_lock_core) 0
      (Dispatch_Intent (sample_request 17) 0 [(17,0),(30,1)]) pair_lock_core
    in snd result = Protocol_Response Request_Rejected \<and>
       machine_state (core_parent (fst result)) = machine_state (core_parent pair_lock_core)"
proof -
  obtain res where at: "reservation_at (machine_state (core_parent pair_lock_core)) (binding_key (request_binding (sample_request 17))) = Some res"
    and footprint: "30 \<in> set (reservation_footprint res)"
    and current: "asset_version (machine_state (core_parent pair_lock_core)) 30 = 0"
    using pair_lock_has_authoritative_dependency by blast
  have stale: "vector_lookup [(17,0),(30,1)] 30 \<noteq> asset_version (machine_state (core_parent pair_lock_core)) 30"
    by (simp add: vector_lookup_def current)
  show ?thesis by (rule sample.actual_dispatch_rejects_a_stale_footprint_member[where asset=30 and res=res])
    (rule at, rule footprint, rule stale)
qed

lemma current_dependency_version_activates_pair_dispatch:
  "snd (sample.invoke_protocol 0 (core_epoch pair_lock_core) 0
      (Dispatch_Intent (sample_request 17) 0 [(17,0),(30,0)]) pair_lock_core) =
    Protocol_Response Source_Dispatched"
  by (simp add: pair_lock_core_def sample_pair_held_def sample_pair_context_def sample_data_defs
      initial_finality_core_def current_lock_view_def sample.invoke_protocol_def acquire_reservation_def
      dispatch_source_def lift_protocol_result_def vector_lookup_def record_observation_def commit_reservation_event_def Let_def)

end
