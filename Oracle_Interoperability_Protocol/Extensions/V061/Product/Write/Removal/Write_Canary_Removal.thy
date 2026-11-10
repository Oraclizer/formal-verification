theory Write_Canary_Removal
  imports "OIP_Write_Canary_Base.Write_Canary_Base"
begin

lemma removing_that_test_reaches_the_same_actual_write:
  "call_authority_results (product_calls (write_canary_submit
    (write_canary_denied_context\<lparr>lock_write_permissions := UNIV\<rparr>))) (7,1) =
    Some (write_canary_command, Protocol_Response Data_Updated, 0)"
  "asset_value (authoritative_reservation_state (write_canary_submit
    (write_canary_denied_context\<lparr>lock_write_permissions := UNIV\<rparr>))) 17 = 9"
  "asset_version (authoritative_reservation_state (write_canary_submit
    (write_canary_denied_context\<lparr>lock_write_permissions := UNIV\<rparr>))) 17 = 1"
proof -
  let ?active = "current_lock_view (write_canary_core (sample_source_context ACTIVE)) 0"
  let ?mutated = "write_canary_denied_context\<lparr>lock_write_permissions := UNIV\<rparr>"
  have held: "owns_current_reservation ?active (sample_request 17) 0 (vector_lookup [(17,0)])
      (machine_state lock_example_held) \<and>
    phase_at (machine_state lock_example_held) (binding_key (request_binding (sample_request 17))) = Some Reservation_Held"
    using successful_write_guard[THEN iffD1, OF write_canary_fixture_success[unfolded write_canary_effect_def]]
    by blast
  have value_only: "current_lock_view (write_canary_core ?mutated) 0 = ?active\<lparr>lock_write_permissions := UNIV\<rparr>"
    by (simp add: write_canary_current_context write_canary_denied_context_def sample_source_context_def sample_context_def)
  have updated: "snd (write_canary_effect ?mutated) = Data_Updated"
    unfolding write_canary_effect_def value_only
    by (rule weakening_only_the_value_membership_test[THEN iffD2, OF held])
  note projected = write_canary_success_projects[OF updated]
  show "call_authority_results (product_calls (write_canary_submit ?mutated)) (7,1) =
    Some (write_canary_command, Protocol_Response Data_Updated, 0)"
    by (rule projected(1))
  show "asset_value (authoritative_reservation_state (write_canary_submit ?mutated)) 17 = 9"
    by (rule projected(2))
  show "asset_version (authoritative_reservation_state (write_canary_submit ?mutated)) 17 = 1"
    by (simp only: projected(3) write_canary_initial_version One_nat_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms removing_that_test_reaches_the_same_actual_write})
  then () else error "Unexpected oracle in the Write permission removal canary"
\<close>

end
