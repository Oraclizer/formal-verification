theory EAB_Lifecycle_Cases
  imports DOSP_EAB_Coupling_Cases.EAB_Adapter_Cases
begin

lemma clock_update_keeps_authority_view [simp]:
  "current_lock_view (core\<lparr>core_parent := m\<rparr>) endpoint = current_lock_view core endpoint"
  by (simp add: current_lock_view_def)

lemma clock_update_keeps_terminal_reference [simp]:
  "exact_record_reference (core\<lparr>core_parent := m\<rparr>) index b kind cert =
    exact_record_reference core index b kind cert"
  by (simp add: exact_record_reference_def record_reference_def)

definition expired_credit_fixture :: "bool \<Rightarrow> metered_source_state" where
  "expired_credit_fixture recorded =
    meter_fixture\<lparr>source_authority := (source_authority meter_fixture)\<lparr>terminal_authority :=
      (credit_core meter_fixture)\<lparr>core_parent := advance_reservation_time 10
        (if recorded then sample_credit_before_ack else core_parent (credit_core meter_fixture))\<rparr>\<rparr>\<rparr>"

lemma the_terminal_reference_is_already_known:
  "exact_record_reference (finality_sample_certified 17) 0 (request_binding (sample_request 17))
    Confirmed_Decision (request_certificate (sample_request 17))"
  by (simp add: exact_record_reference_def record_reference_def
      fixture_before_publication fixture_binding sample_request_def)

lemma expired_credit_fixture_cannot_promote_without_the_real_credit:
  fixes s :: metered_source_state
  defines "s \<equiv> expired_credit_fixture False"
    and "attempt \<equiv> sample.resolve_cutover_lock Reconcile_Credit fixture_epoch 0 (sample_request 17) 5 s"
  shows "snd attempt = Request_Rejected \<and>
    promote_settled_asset coupling_policy {(12, 4)} 12 4 (fst attempt) =
      (fst attempt, transition_result.Rejected Ineligible_Promotion)"
  by (simp add: attempt_def s_def sample.resolve_cutover_lock_def sample.settle_expired_reservation_def
      sample.lock_resolution_word_def sample.execute_lock_word_def sample.finality_step_def sample.invoke_protocol_def
      lift_protocol_result_def recorded_versions_def vector_lookup_def
      expired_credit_fixture_def the_terminal_reference_is_already_known meter_fixture_def
      exact_record_reference_def record_reference_def fixture_before_publication
      terminal_certificate_publishes_the_actual_parent_evidence finality_sample_current_contexts
      sample_data_defs sample_auth_defs sample.protocol_definitions sample.run_reservations.simps
      sample.reservation_step.simps record_observation_def commit_reservation_event_def
      empty_message_state_def promote_settled_asset_def promotion_locks_clear_def promotion_assets_def
      coupling_policy_def Let_def)

theorem recorded_credit_allows_the_same_asset_to_release_then_promote:
  fixes s :: metered_source_state
  defines "s \<equiv> expired_credit_fixture True"
    and "release \<equiv> sample.resolve_cutover_lock Reconcile_Credit fixture_epoch 0 (sample_request 17) 5 s"
  shows "snd release = Reservation_Released \<and>
    core_epoch (credit_core (fst release)) = fixture_epoch + 2 \<and>
    snd (promote_settled_asset coupling_policy {(12, 4)} 12 4 (fst release)) =
      transition_result.Accepted Promotion_Finalized"
  by (simp add: release_def s_def sample.resolve_cutover_lock_def sample.settle_expired_reservation_def
      sample.lock_resolution_word_def sample.execute_lock_word_def sample.finality_step_def sample.invoke_protocol_def
      lift_protocol_result_def recorded_versions_def vector_lookup_def
      expired_credit_fixture_def the_terminal_reference_is_already_known meter_fixture_def
      exact_record_reference_def record_reference_def fixture_before_publication
      finality_sample_current_contexts sample_credit_before_ack_def sample_data_defs sample_auth_defs
      sample.protocol_definitions sample.published_receive_expansion sample.run_reservations.simps
      sample.reservation_step.simps record_observation_def commit_reservation_event_def record_credit_def
      empty_message_state_def promote_settled_asset_def promotion_locks_clear_def promotion_assets_def
      promotion_allowed_def coupling_policy_def coupling_ticket_def Let_def)

end
