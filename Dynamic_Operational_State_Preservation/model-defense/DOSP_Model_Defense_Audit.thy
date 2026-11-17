theory DOSP_Model_Defense_Audit
  imports DOSP_Route_And_Recovery_Cases DOSP_Retained_Failure_Case DOSP_Central_Router_Defense DOSP_Same_Sequence_Cases DOSP_Repin_Cases DOSP_Soft_Retry_Cases
begin

ML \<open>
  val obligations =
    [("hub observation", @{thms observed_hub_reads_and_overprovision_cannot_write
         joined_dosp.registry_observation_does_not_publish_a_charge_or_primary_record}),
     ("initiator degrees", @{thms an_initiator_cannot_use_another_initiators_path
         the_two_origins_have_their_own_legal_committing_degrees
         joined_dosp.a_joint_credit_consumes_the_degree_at_its_actual_initiator}),
     ("route projection", @{thms routed_flow_naturality_uses_the_same_ticket_and_result
         joined_dosp.a_joint_native_credit_gives_the_same_routed_update_when_participants_are_kept
         omitting_an_initiator_does_not_preserve_the_router_result
         same_routed_commit_distinguishes_soft_failure_and_atomic_rollback}),
     ("in-flight promotion", @{thms lifecycle_promotion_has_the_exact_safe_boundary
         an_actual_partial_commit_blocks_promotion_until_the_exact_restoration
         actual_atomic_failure_preserves_the_committed_cells
         bare_retry_and_restore_cannot_clear_a_pending_native_debit
         actual_native_pending_cannot_be_discharged_by_local_restoration
         guarded_promotion_blocks_a_bound_phase_before_the_native_step
         guarded_promotion_cannot_change_another_registry_asset
         joined_dosp.an_inflight_binding_blocks_the_products_ordinary_trade
         joined_dosp.native_reservation_blocks_trade_even_if_the_local_phase_is_idle
         joined_dosp.a_protected_retry_without_current_confirmation_keeps_both_states
         joined_dosp.retained_settlement_requires_the_preexisting_debit_and_current_confirmation
         joined_dosp.retained_settlement_is_bound_to_the_actual_debit
         guarded_promotion_consumes_native_lock_and_registry_checks
         native_bind_cannot_pass_without_the_live_exact_lock
         native_verification_cannot_pass_without_an_exact_current_confirmation
         stale_native_credentials_cannot_bind_or_verify
         joined_dosp.preparation_cannot_smuggle_an_operation_past_native_admission
         joined_dosp.a_post_reserve_preparation_cannot_change_the_bound_identity
         joined_dosp.aborting_an_unexecuted_binding_never_releases_a_pending_native_debit
         joined_dosp.an_actual_source_debit_cannot_be_canceled_as_an_unexecuted_command
         joined_dosp.a_new_native_preparation_waits_for_required_recovery
         joined_dosp.a_source_preparation_uses_the_exact_active_endpoint
         an_unrelated_endpoint_cannot_take_the_actual_reservation
         joined_dosp.a_required_pending_debit_is_reported_as_awaiting_settlement
         a_failed_retained_commit_is_publicly_pending_and_records_the_failure
         failed_commit_keeps_the_exact_binding_while_the_native_debit_is_pending
         joined_dosp.a_reassigned_pending_debit_keeps_the_binding_and_both_bills
         the_native_reservation_and_dispatched_unexecuted_binding_can_be_released_after_exit
         an_expired_confirmed_debit_is_renewed_in_the_same_product_binding_after_exit
         joined_dosp.live_reversal_requires_exact_terminal_evidence_and_leaves_billing_unchanged
         the_actual_native_refund_releases_a_bound_debit_without_a_local_write
         joined_dosp.accepted_custody_cleanup_preserves_the_public_and_native_bills
         actual_confirmed_credit_releases_its_own_custody_without_rebilling
         a_native_verification_retains_cutover_and_invoice
         a_restoration_cannot_be_reused_for_another_routing_ticket
         a_failed_soft_commit_can_retry_the_same_binding_forward
         source_attestation.native_partially_applied_binding_cannot_restore_without_reversal
         source_attestation.verified_reversal_before_commit_releases_the_debit_without_local_writes}),
     ("cutover accounting", @{thms client_report_is_authenticated_for_this_commit
         accepted_invoice_row_has_one_registry_policy_and_one_commit_time
         historical_failed_attempt_survives_cutover_without_repricing
         public_epoch_log_reconstructs_a_session_bill the_public_bill_keeps_the_old_rows_after_the_tariff_repin
         a_new_tariff_cannot_reprice_an_archived_session_bill
         only_an_accepted_promotion_repins_the_session_tariff
         the_next_commit_uses_the_repinned_registry_entry_and_rate
         metered_leaf_count_has_a_verified_final_write_set missing_measurement_cannot_publish_a_commit_or_clear_the_phase
         source_attestation.the_native_credit_consumes_the_same_binding_and_public_meter_row
         the_actual_second_credit_uses_consensus_day_one_even_if_the_local_clock_lags
         joined_dosp.a_missing_final_measurement_cannot_publish_either_ledger
         joined_dosp.a_missing_native_success_history_blocks_the_joint_publication
         joined_dosp.missing_or_changed_historical_tariff_blocks_a_new_joint_credit
         joined_dosp.a_replaced_issued_tariff_cannot_enter_the_classified_trace
         joined_dosp.a_session_cannot_open_with_an_unissued_tariff
         joined_dosp.a_classified_trace_replays_the_original_public_bill_at_every_later_input
         a_real_native_success_proposal_does_not_escape_without_measurement
         the_actual_eab_credit_and_matching_public_row_commit_together
         failed_product_commit_preserves_native_publication_and_lock_history
         a_verified_timeout_is_network_liability
         an_accepted_failed_commit_publishes_its_charge_cause_on_the_consensus_day
         a_published_binding_cannot_be_metered_as_an_abort
         joined_dosp.a_confirmed_joint_credit_requires_both_linked_effects
         adding_a_new_tariff_extends_the_archive
         source_attestation.the_consensus_commit_drives_the_same_public_billing_day}),
     ("registry routing", @{thms classified_registry_asset_reaches_the_recorded_native_usage
         joined_dosp.a_false_registry_classification_cannot_seed_a_product_execution
         joined_dosp.native_reservation_requires_a_degree_that_permits_commit
         joined_dosp.a_read_only_registered_degree_refuses_the_native_reservation
         the_native_reservation_is_taken_by_the_classified_product_before_bind
         joined_dosp.current_supply_cannot_override_wrong_seed_classification
         the_initial_recovery_facts_are_the_native_published_facts
         the_actual_registry_seed_consumes_the_first_matching_classification
         joined_dosp.product_metering_uses_the_updated_membership_in_the_same_state
         joined_dosp.registry_routing_and_billing_use_the_same_request
         router_rejects_same_path_but_superseded_ticket_and_initiator}),
     ("membership activation", @{thms membership_uses_the_consensus_boundary_and_current_grant native_clock_is_consumed_at_the_membership_boundary
         joined_dosp.an_accepted_clock_input_updates_the_same_product_state
         joined_dosp.an_exited_origin_cannot_start_a_new_native_credit
         joined_dosp.observations_after_departure_use_the_current_membership
         joined_dosp.fresh_native_preparation_waits_for_due_route_activation
         joined_dosp.a_later_activation_cannot_skip_an_outstanding_authorized_epoch
         two_due_leaves_apply_in_epoch_order_and_then_refuse_the_old_origin
         joined_dosp.conflicting_grants_cannot_both_supply_one_routing_epoch
         joined_dosp.a_current_supply_cannot_drop_an_unapplied_routing_grant
         an_accepted_approval_checks_the_whole_order_and_keeps_outstanding_grants
         a_conflicting_route_plan_is_refused_and_keeps_the_previous_approvals
         an_approved_plan_reserves_only_finitely_many_job_ids
         a_routing_approval_rejects_a_successor_removed_by_an_earlier_approved_leave
         joined_dosp.a_changed_routing_supply_has_passed_approval_before_it_can_be_used
         joined_dosp.a_newly_issued_route_cannot_be_backdated_behind_processed_work
         stale_observations_get_new_jobs_without_using_the_scheduled_join_id
         an_observation_can_replace_a_reserved_id_when_used_ids_are_finite
         joined_dosp.recorded_replica_divergence_blocks_ordinary_trade
         joined_dosp.a_joint_credit_cannot_use_an_outstanding_join_job_as_fresh_work
         joined_dosp.a_valid_credit_can_allocate_fresh_jobs_outside_a_finite_reservation
         at_the_effective_second_the_old_route_cannot_take_the_native_lock
         the_same_product_grant_exits_the_route_with_unexecuted_custody
         retired_origin_can_only_settle_its_already_debited_binding}),
     ("membership frame", @{thms membership_keeps_the_handed_off_pending_ids_and_historical_facts
         joined_dosp.an_offered_leave_preserves_the_actual_handed_off_job
         joined_dosp.joining_initializes_the_new_cell_and_frames_existing_replica_and_work
         the_actual_join_exposes_the_new_replica_and_keeps_the_old_cells
         every_active_replica_requires_verification_of_the_new_publication
         an_initial_publication_preserves_any_work_already_admitted
         a_real_nonfinal_install_has_a_raw_replica_counterexample}),
     ("recovery convergence", @{thms joined_dosp.authenticated_recovery_finishes_under_finite_interference
         joined_dosp.verified_product_repairs_finish_after_finite_interference
         joined_dosp.an_accepted_product_recovery_consumes_the_same_available_authority
         joined_dosp.recorded_divergence_blocks_new_native_credit_even_before_first_publication
         an_observed_divergence_before_the_first_publication_blocks_reserve
         only_unpublished_genesis_can_start_without_the_current_primary_anchor
         joined_dosp.a_first_publication_can_adopt_work_already_admitted_at_bootstrap
         joined_dosp.ordinary_trade_reopens_when_native_custody_and_repair_work_are_settled
         joined_dosp.product_recovery_rejects_a_duplicate_join_and_a_completed_install
         joined_dosp.an_authorized_governance_retry_with_no_pending_job_returns_refusal
         current_publication_retry_completes_the_carried_job_and_restores_trading
         repeated_refusal_of_an_old_publisher_is_not_recovery_progress}),
     ("current receipt recovery", @{thms current_source_chosen_from_two_actual_histories
         an_actual_competing_issuer_at_the_same_sequence_cannot_replace_the_current_record
         joined_dosp.published_credit_installs_the_actual_current_recovery_anchor
         joined_dosp.product_repair_cannot_install_a_receipt_missing_from_current_consensus
         joined_dosp.an_older_issued_publication_cannot_become_the_current_product_repair
         joined_dosp.a_receipt_regression_opens_work_even_when_its_replica_value_matches
         joined_dosp.observing_the_current_receipt_cannot_create_divergent_work
         the_two_actual_equal_valued_receipts_have_different_recovery_observations
         a_competing_issued_receipt_at_the_same_number_opens_replica_work
         joined_dosp.a_receipt_for_another_asset_cannot_open_a_replica_job
         a_retained_old_receipt_is_not_used_after_the_next_actual_publication
         the_promoted_router_bill_names_the_publication_used_by_handed_off_recovery
         joined_dosp.projection_keeps_authenticated_recovery_when_it_keeps_the_current_issuer
         joined_dosp.hiding_the_current_issuer_cannot_simulate_a_current_install}),
     ("irreversibility", @{thms joined_dosp.prepared_governance_repair_uses_the_verified_record
         joined_dosp.offered_recovery_cannot_install_an_unapproved_rollback
         joined_dosp.mismatched_authority_or_asset_rejects_the_governance_command
         joined_dosp.accepted_governance_requires_the_exact_scope_and_preserves_irreversibility
         even_a_confirmed_other_asset_approval_cannot_resolve_the_job
         a_caller_cannot_select_another_assets_approval_scope
         joined_dosp.product_rollback_uses_the_registry_asset_and_the_issued_receipt
         correct_resolution_respects_the_same_registry_after_membership_handoff
         exact_governance_can_resync_the_same_pending_job_and_leaves_the_other_pending
         joined_dosp.accepted_recovery_use_cannot_substitute_an_action_or_reopen_a_completed_job})];

  fun audit (requirement, theorems) =
    if null (Thm_Deps.all_oracles theorems) then ()
    else error ("Unexpected oracle in DOSP requirement " ^ requirement);

  val _ = List.app audit obligations;
\<close>

end
