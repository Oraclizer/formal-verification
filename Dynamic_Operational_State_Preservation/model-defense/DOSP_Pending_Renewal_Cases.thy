theory DOSP_Pending_Renewal_Cases
  imports DOSP_Native_Cleanup_Cases
begin

definition expired_confirmed_core where
  "expired_confirmed_core = (finality_sample_certified 17)\<lparr>core_parent :=
    advance_reservation_time 10 (core_parent (finality_sample_certified 17))\<rparr>"

abbreviation renew_confirmed_command where
  "renew_confirmed_command \<equiv> Client_Protocol 0 0 (Reassign_Intent (sample_request 17) 5)"

definition renewed_confirmed_core where
  "renewed_confirmed_core = fst (sample.execute_finality_client renew_confirmed_command expired_confirmed_core)"

lemma expired_confirmed_parent_lease:
  "core_parent expired_confirmed_core =
    advance_reservation_time 10 (sample.publish_source_certificate (sample_certificate 17) (sample_burnt 17))"
  "current_lock_view expired_confirmed_core 0 = sample_source_context ACTIVE"
  "exact_record_reference expired_confirmed_core 0 (request_binding (sample_request 17))
    Confirmed_Decision (request_certificate (sample_request 17))"
  by (simp_all add: expired_confirmed_core_def terminal_certificate_publishes_the_actual_parent_evidence
      finality_sample_current_contexts first_record_reference)

lemmas expired_confirmed_lease_steps =
  expired_confirmed_parent_lease sample_burnt_def sample_initial_def initial_reservation_machine_def
  advance_reservation_time_def staged_trace_defs empty_vector_represents_zero_versions

lemma expired_confirmed_parent_reassignment:
  "snd (sample.execute_finality_client renew_confirmed_command expired_confirmed_core) =
      Protocol_Response Worker_Reassigned"
  by (simp add: sample.execute_finality_client_def sample.invoke_protocol_def
      lift_protocol_result_def expired_confirmed_lease_steps)

lemma exact_renewed_pending_binding:
  "core_parent renewed_confirmed_core =
      fst (reassign_worker (sample_source_context ACTIVE) (sample_request 17) 5 (core_parent expired_confirmed_core))"
  "current_lock_view renewed_confirmed_core 0 = sample_source_context ACTIVE"
  "exact_record_reference renewed_confirmed_core 0 (request_binding (sample_request 17))
     Confirmed_Decision (request_certificate (sample_request 17))"
  unfolding renewed_confirmed_core_def
  using sample_protocol_updates_the_parent_through_its_actual_action[of expired_confirmed_core 0
      "Reassign_Intent (sample_request 17) 5" 0]
  by (simp_all add: expired_confirmed_parent_lease)

abbreviation partial_confirmed_product where
  "partial_confirmed_product core \<equiv>
    (let p = early_product core (Partial_Cycle cleanup_cycle (binding_state (lifecycle_cutover (source_lifecycle classified_first_state)))) early_retired
     in p\<lparr>source_lifecycle := (source_lifecycle p)\<lparr>cycle_custody := Native_Debit_Pending (0,17)\<rparr>\<rparr>)"

lemma an_expired_confirmed_debit_is_renewed_in_the_same_product_binding_after_exit:
  fixes p q :: product_source_state
  defines "p \<equiv> partial_confirmed_product expired_confirmed_core"
    and "q \<equiv> partial_confirmed_product renewed_confirmed_core"
  shows "\<not> protected_retry_is_current p cleanup_cycle 0 (sample_request 17)"
    "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
      cleanup_grant p (Renew_Pending_Native 0 (sample_request 17) 5) (Released_Outcome True) q"
    "protected_retry_is_current q cleanup_cycle 0 (sample_request 17)"
    "lifecycle_invoice (source_lifecycle q) = lifecycle_invoice (source_lifecycle p)"
    "source_recovery q = source_recovery p"
proof -
  have original_native: "credit_core (current_operational (source_consensus p)) = expired_confirmed_core"
    by (simp add: p_def Let_def with_finality_core_def with_operational_state_def)
  have renewed_native: "credit_core (current_operational (source_consensus q)) = renewed_confirmed_core"
    by (simp add: q_def Let_def with_finality_core_def with_operational_state_def)
  have expired: "\<not> current_binding_holds_its_native_lock (current_operational (source_consensus p)) (sample_request 17)"
    unfolding current_binding_holds_its_native_lock_def
    by (simp add: original_native expired_confirmed_lease_steps)
  have fresh: "current_binding_holds_its_native_lock (current_operational (source_consensus q)) (sample_request 17)"
    unfolding current_binding_holds_its_native_lock_def
    by (simp add: renewed_native exact_renewed_pending_binding expired_confirmed_lease_steps)
  have prior: "native_source_pending (current_operational (source_consensus p)) (sample_request 17)"
    "source_was_debited (machine_state (core_parent expired_confirmed_core)) (0,17)"
    by (simp_all add: native_source_pending_def original_native expired_confirmed_lease_steps)
  have pending: "native_source_pending (current_operational (source_consensus q)) (sample_request 17)"
    by (simp add: native_source_pending_def renewed_native exact_renewed_pending_binding expired_confirmed_lease_steps)
  have binding: "cycle_names_native_binding cleanup_cycle (sample_request 17)"
    by (simp add: cycle_names_native_binding_def cleanup_cycle_def request_flow_def sample_request_def
      sample_binding_def example_binding_def Let_def)
  have key: "binding_key (request_binding (sample_request 17)) = (0,17)"
    by (simp add: sample_request_def sample_binding_def example_binding_def)
  have safe: "names_prepared_binding (source_lifecycle p) (request_binding (sample_request 17))"
    using binding by (auto simp: p_def names_prepared_binding_def cleanup_cycle_def
      cycle_names_native_binding_def sample_request_def sample_binding_def example_binding_def episode_initial_def Let_def)
  have renewed: "joined_dosp.reassign_pending_product_debit p 0 (sample_request 17) 5 True q"
    unfolding joined_dosp.reassign_pending_product_debit_def
    using prior safe expired_confirmed_parent_reassignment key
    by (simp add: p_def q_def renewed_confirmed_core_def Let_def sample_request_def sample_binding_def
      example_binding_def episode_initial_def joined_initial_def cycle_fixture_def meter_fixture_def
      with_finality_core_def with_operational_state_def)
  show "\<not> protected_retry_is_current p cleanup_cycle 0 (sample_request 17)"
    using expired by (simp add: protected_retry_is_current_def Let_def)
  show "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    cleanup_grant p (Renew_Pending_Native 0 (sample_request 17) 5) (Released_Outcome True) q"
    using renewed by (auto simp: joined_dosp.product_source_step_def Let_def)
  show "protected_retry_is_current q cleanup_cycle 0 (sample_request 17)"
    unfolding protected_retry_is_current_def
    using fresh pending binding key exact_renewed_pending_binding(3)
    by (auto simp: q_def Let_def with_finality_core_def with_operational_state_def)
  show "lifecycle_invoice (source_lifecycle q) = lifecycle_invoice (source_lifecycle p)"
    "source_recovery q = source_recovery p"
    using joined_dosp.a_reassigned_pending_debit_keeps_the_binding_and_both_bills[OF renewed] by simp_all
qed

end
