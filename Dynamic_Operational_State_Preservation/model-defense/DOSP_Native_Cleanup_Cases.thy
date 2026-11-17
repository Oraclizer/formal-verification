theory DOSP_Native_Cleanup_Cases
  imports DOSP_Classified_Entry
begin

abbreviation early_reserve where
  "early_reserve \<equiv> Client_Protocol 0 0 (Reserve_Intent (sample_request 17) [] 10)"

abbreviation early_dispatch where
  "early_dispatch \<equiv> Client_Protocol 0 0 (Dispatch_Intent (sample_request 17) 0 [])"

abbreviation early_cancel where
  "early_cancel \<equiv> Client_Protocol 0 0 (Cancel_Intent (sample_request 17) 0 [])"

abbreviation early_fence where
  "early_fence \<equiv> Client_Protocol 0 0 (Fence_Intent (sample_request 17) 0 [])"

lemma early_native_request_fields:
  "request_binding (sample_request 17) = sample_binding 17"
  "binding_key (sample_binding 17) = (0,17)"
  "binding_asset (sample_binding 17) = 17"
  "binding_destination (sample_binding 17) = 2"
  by (simp_all add: sample_request_def sample_binding_def example_binding_def)

definition early_held_core where
  "early_held_core = fst (sample.execute_finality_client early_reserve finality_sample_initial)"

definition early_submitted_core where
  "early_submitted_core = fst (sample.execute_finality_client early_dispatch early_held_core)"

lemmas early_native_protocol = sample.execute_finality_client_def sample.finality_step_def sample.invoke_protocol_def
  finality_sample_initial_def initial_finality_core_def initial_reservation_machine_def early_held_core_def
  early_submitted_core_def current_lock_view_def empty_vector_represents_zero_versions lift_protocol_result_def
  sample_data_defs staged_trace_defs

lemma early_native_replies:
  "snd (sample.execute_finality_client early_reserve finality_sample_initial) = Protocol_Response Reservation_Acquired"
  "snd (sample.execute_finality_client early_dispatch early_held_core) = Protocol_Response Source_Dispatched"
  "snd (sample.execute_finality_client early_cancel early_held_core) = Protocol_Response Reservation_Released"
  "snd (sample.execute_finality_client early_fence early_submitted_core) = Protocol_Response Source_Fenced"
  by (simp_all add: early_native_protocol)

lemma early_native_balances:
  "phase_at (machine_state (core_parent early_held_core)) (0,17) = Some Reservation_Held"
  "phase_at (machine_state (core_parent early_submitted_core)) (0,17) = Some Source_Submitted"
  "\<not> source_was_debited (machine_state (core_parent early_held_core)) (0,17)"
  "\<not> source_was_debited (machine_state (core_parent early_submitted_core)) (0,17)"
  "asset_owner (machine_state (core_parent (fst (sample.execute_finality_client early_cancel early_held_core)))) 17 = None"
  "asset_owner (machine_state (core_parent (fst (sample.execute_finality_client early_fence early_submitted_core)))) 17 = None"
  by (simp_all add: early_native_protocol)

definition cleanup_cycle :: cycle_request where
  "cleanup_cycle = \<lparr>cycle_attempt_id = (17,0), cycle_session_id = (17,7,3), cycle_binding_id = prod_encode (0,17),
     cycle_ticket = joined_ticket 0 coupling_ticket, cycle_source = 0, cycle_target = 2,
     cycle_value = binding_amount (sample_binding 17)\<rparr>"

abbreviation cleanup_grant where
  "cleanup_grant \<equiv> {(Leave_Domain (0::nat) 4,2,86399)}"

abbreviation early_recovery where
  "early_recovery \<equiv> first_unpublished_recovery\<lparr>replica := (\<lambda>_. 0)\<rparr>"

abbreviation early_product where
  "early_product core phase recovery \<equiv> classified_first_state\<lparr>
    source_consensus := with_finality_core core joined_initial,
    source_lifecycle := (source_lifecycle classified_first_state)\<lparr>lifecycle_phase := phase\<rparr>,
    source_recovery := recovery\<rparr>"

abbreviation early_retired where
  "early_retired \<equiv> early_recovery\<lparr>active_domains := {2,4},route_epoch := 2\<rparr>"

lemma the_native_reservation_is_taken_by_the_classified_product_before_bind:
  "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    {} (early_product finality_sample_initial Idle_Cycle early_recovery) (Prepare_Native early_reserve)
    (Preparation_Outcome (Protocol_Response Reservation_Acquired)) (early_product early_held_core Idle_Cycle early_recovery)"
proof -
  let ?p = "early_product finality_sample_initial Idle_Cycle early_recovery"
  let ?q = "early_product early_held_core Idle_Cycle early_recovery"
  have eligible: "joined_dosp.native_preparation_ready ?p early_reserve (sample_binding 17)"
    unfolding joined_dosp.native_preparation_ready_def
    by (simp add: recovery_permits_native_credit_def recovery_permits_existing_native_credit_def pending_ids_def
        Let_def sample_binding_def example_binding_def
        sample_request_def episode_initial_def joined_initial_def cycle_fixture_def meter_fixture_def
        with_finality_core_def with_operational_state_def coupling_ticket_def coupling_policy_def)
  have before: "credit_core (current_operational (source_consensus ?p)) = finality_sample_initial"
    by (simp add: with_finality_core_def with_operational_state_def)
  have after: "credit_core (current_operational (source_consensus ?q)) = early_held_core"
    by (simp add: with_finality_core_def with_operational_state_def)
  have installed: "with_finality_core early_held_core (source_consensus ?p) = source_consensus ?q"
    by (simp add: with_finality_core_def with_operational_state_def)
  have core_step: "sample.execute_finality_client early_reserve finality_sample_initial =
    (early_held_core, Protocol_Response Reservation_Acquired)"
    using early_native_replies(1) by (metis early_held_core_def prod.collapse)
  have step: "joined_dosp.execute_integrated_client (Prepare_Credit early_reserve) (source_consensus ?p) =
    (source_consensus ?q, Preparation_Result (Protocol_Response Reservation_Acquired))"
    by (simp only: joined_dosp.execute_integrated_client.simps(1) credit_preparation.simps if_True
        Let_def before core_step fst_conv snd_conv installed)
  have held_phase: "phase_at (machine_state (core_parent (credit_core (current_operational (source_consensus ?q)))))
    (binding_key (sample_binding 17)) = Some Reservation_Held"
    by (simp only: after early_native_request_fields(2) early_native_balances(1))
  have preparation: "joined_dosp.prepare_product_credit ?p early_reserve (Protocol_Response Reservation_Acquired) ?q"
    unfolding joined_dosp.prepare_product_credit_def
  proof (intro exI[of _ "sample_binding 17"] exI[of _ "source_consensus ?q"] conjI)
    show "joined_dosp.native_preparation_ready ?p early_reserve (sample_binding 17)" by (rule eligible)
    show "joined_dosp.execute_integrated_client (Prepare_Credit early_reserve) (source_consensus ?p) =
      (source_consensus ?q, Preparation_Result (Protocol_Response Reservation_Acquired))" by (rule step)
    let ?state = "machine_state (core_parent (credit_core (current_operational (source_consensus ?q))))"
    let ?key = "binding_key (sample_binding 17)"
    show "(let state = ?state;
            exists_debit = phase_at state ?key = Some Source_Pending \<and> source_was_debited state ?key;
            previous = source_lifecycle ?p;
            s = (if exists_debit then previous\<lparr>cycle_custody := Native_Debit_Pending ?key\<rparr> else previous)
        in ?q = ?p\<lparr>source_lifecycle := s, source_consensus := source_consensus ?q\<rparr>)"
      by (simp only: Let_def held_phase; simp)
  qed
  show ?thesis using preparation
    by (auto simp: joined_dosp.product_source_step_def route_activation_is_due_def current_grant_def Let_def)
qed

lemma the_same_product_grant_exits_the_route_with_unexecuted_custody:
  "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    cleanup_grant (early_product core phase early_recovery) (Update_Recovery (Activate_Route (Leave_Domain 0 4) 2 86399))
    (Recovery_Outcome (transition_result.Accepted (Left 0 4))) (early_product core phase early_retired)"
proof -
  have empty: "carry_owner (0::nat) 4 Map.empty = Map.empty"
    by (rule ext) (simp add: carry_owner_def)
  have leave: "recovery_step cleanup_grant {} early_recovery (Activate (Leave_Domain 0 4) 2 86399 86399)
      (transition_result.Accepted (Left 0 4)) early_retired"
    using recovery_step.Leave_Route[where s=early_recovery and old=0 and successor=4 and epoch=2 and boundary=86399
      and root_time=86399 and grants=cleanup_grant and governance="{}"]
    by (simp add: current_grant_def empty)
  show ?thesis using leave
    by (auto simp: joined_dosp.product_source_step_def joined_dosp.product_recovery_step_def
      joined_dosp.consensus_membership_step_def joined_dosp.activation_uses_the_existing_grant_and_handoff
      earlier_route_update_is_pending_def route_grant_matches_its_epoch_def
      with_finality_core_def with_operational_state_def joined_initial_def Let_def)
qed

lemma the_native_reservation_and_dispatched_unexecuted_binding_can_be_released_after_exit:
  fixes p q :: product_source_state
  defines "p \<equiv> early_product early_held_core Idle_Cycle early_retired"
    and "q \<equiv> early_product early_submitted_core (Bound_Cycle cleanup_cycle) early_retired"
  shows "\<exists>t. joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
      cleanup_grant p (Abort_Unexecuted_Native (Live_Lease 0 []) 0 (sample_request 17)) (Released_Outcome True) t \<and>
      lifecycle_phase (source_lifecycle t) = Idle_Cycle \<and>
      asset_owner (machine_state (core_parent (credit_core (current_operational (source_consensus t))))) 17 = None \<and>
      lifecycle_invoice (source_lifecycle t) = lifecycle_invoice (source_lifecycle p)"
    "\<exists>t. joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
      cleanup_grant q (Abort_Unexecuted_Native (Live_Lease 0 []) 0 (sample_request 17)) (Released_Outcome True) t \<and>
      lifecycle_phase (source_lifecycle t) = Idle_Cycle \<and>
      asset_owner (machine_state (core_parent (credit_core (current_operational (source_consensus t))))) 17 = None \<and>
      lifecycle_invoice (source_lifecycle t) = lifecycle_invoice (source_lifecycle q)"
proof -
  let ?held = "early_product (fst (sample.execute_finality_client early_cancel early_held_core)) Idle_Cycle early_retired"
  let ?fenced = "early_product (fst (sample.execute_finality_client early_fence early_submitted_core)) Idle_Cycle early_retired"
  have run_held: "joined_dosp.run_predebit_cancellation early_held_core (Live_Lease 0 []) 0 (sample_request 17) =
    sample.execute_finality_client early_cancel early_held_core"
    unfolding joined_dosp.run_predebit_cancellation_def
    by (simp add: early_native_request_fields early_native_balances(1) Let_def)
  have run_fence: "joined_dosp.run_predebit_cancellation early_submitted_core (Live_Lease 0 []) 0 (sample_request 17) =
    sample.execute_finality_client early_fence early_submitted_core"
    unfolding joined_dosp.run_predebit_cancellation_def
    by (simp add: early_native_request_fields early_native_balances(2) Let_def)
  have held_abort: "joined_dosp.abort_unexecuted_credit p (Live_Lease 0 []) 0 (sample_request 17) True ?held"
    unfolding p_def joined_dosp.abort_unexecuted_credit_def
    by (simp add: run_held early_native_replies(3) early_native_balances(1,3) Let_def early_native_request_fields
      episode_initial_def joined_initial_def cycle_fixture_def meter_fixture_def
      with_finality_core_def with_operational_state_def)
  have fenced_abort: "joined_dosp.abort_unexecuted_credit q (Live_Lease 0 []) 0 (sample_request 17) True ?fenced"
    unfolding q_def joined_dosp.abort_unexecuted_credit_def
    by (auto simp: run_fence early_native_replies(4) early_native_balances(2,4) Let_def early_native_request_fields
      episode_initial_def joined_initial_def cycle_fixture_def meter_fixture_def with_finality_core_def with_operational_state_def
      names_prepared_binding_def cleanup_cycle_def request_flow_def)
  show "\<exists>t. joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
      cleanup_grant p (Abort_Unexecuted_Native (Live_Lease 0 []) 0 (sample_request 17)) (Released_Outcome True) t \<and>
      lifecycle_phase (source_lifecycle t) = Idle_Cycle \<and>
      asset_owner (machine_state (core_parent (credit_core (current_operational (source_consensus t))))) 17 = None \<and>
      lifecycle_invoice (source_lifecycle t) = lifecycle_invoice (source_lifecycle p)"
    using held_abort by (intro exI[of _ ?held])
      (auto simp: p_def joined_dosp.product_source_step_def Let_def early_native_balances(5) with_finality_core_def with_operational_state_def)
  show "\<exists>t. joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
      cleanup_grant q (Abort_Unexecuted_Native (Live_Lease 0 []) 0 (sample_request 17)) (Released_Outcome True) t \<and>
      lifecycle_phase (source_lifecycle t) = Idle_Cycle \<and>
      asset_owner (machine_state (core_parent (credit_core (current_operational (source_consensus t))))) 17 = None \<and>
      lifecycle_invoice (source_lifecycle t) = lifecycle_invoice (source_lifecycle q)"
    using fenced_abort by (intro exI[of _ ?fenced])
      (auto simp: q_def joined_dosp.product_source_step_def Let_def early_native_balances(6) with_finality_core_def with_operational_state_def)
qed

end
