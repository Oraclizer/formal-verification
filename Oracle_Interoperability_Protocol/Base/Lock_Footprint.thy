theory Lock_Footprint
  imports Lock_Release "Preemptive_Lock_Correctness.Reservation_Progress"
begin

lemma recorded_lock_rejects_a_stale_version_in_any_footprint_member:
  assumes "reservation_at s (binding_key (request_binding r)) = Some res"
    and "asset \<in> set (reservation_footprint res)" "versions asset \<noteq> asset_version s asset"
  shows "\<not> owns_recorded_reservation c r generation versions s"
  using assms by (auto simp: owns_recorded_reservation_def)

context source_attestation
begin

lemma actual_dispatch_rejects_a_stale_footprint_member:
  assumes "reservation_at (machine_state (core_parent s)) (binding_key (request_binding r)) = Some res"
    and "asset \<in> set (reservation_footprint res)"
    and "vector_lookup versions asset \<noteq> asset_version (machine_state (core_parent s)) asset"
  shows "let result = invoke_protocol endpoint (core_epoch s) index (Dispatch_Intent r generation versions) s
    in snd result = Protocol_Response Request_Rejected \<and>
       machine_state (core_parent (fst result)) = machine_state (core_parent s)"
proof -
  have recorded: "\<not> owns_recorded_reservation (current_lock_view s endpoint) r generation (vector_lookup versions)
     (machine_state (core_parent s))"
    by (rule recorded_lock_rejects_a_stale_version_in_any_footprint_member[where asset=asset and res=res])
      (rule assms(1), rule assms(2), rule assms(3))
  have current: "\<not> owns_current_reservation (current_lock_view s endpoint) r generation (vector_lookup versions)
     (machine_state (core_parent s))"
    using recorded by (simp add: owns_current_reservation_def)
  show ?thesis using current
    by (simp add: Let_def invoke_protocol_def dispatch_source_def lift_protocol_result_def record_observation_def)
qed

end

lemmas opposite_order_pair_cannot_take_a_partial_lock = opposite_order_acquisition_keeps_no_partial_reservation

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    recorded_lock_rejects_a_stale_version_in_any_footprint_member
    source_attestation.actual_dispatch_rejects_a_stale_footprint_member
    opposite_order_pair_cannot_take_a_partial_lock})
  then () else error "Unexpected oracle in footprint proofs"
\<close>

end
