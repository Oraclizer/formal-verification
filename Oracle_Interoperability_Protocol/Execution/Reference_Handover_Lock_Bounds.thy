theory Reference_Handover_Lock_Bounds
  imports Reference_Trace_Consumers "OIP_Product_Base.Lock_Settlement"
begin

context reference_trace_consumer
begin

theorem the_actual_public_continuation_of_a_reference_prefix_preserves_pending_across_lock_control:
  fixes before core prefix initial
  defines "before \<equiv> run_reference_word execute prefix initial"
    and "core \<equiv> retained_core (retained_source (reference_product before))"
  assumes start: "reference_service_contract registered (initial_finality_core balances regulatory contexts) initial"
    and pending: "phase_at (machine_state (core_parent core)) (binding_key (request_binding request)) = Some Source_Pending"
    and debited: "source_was_debited (machine_state (core_parent core)) (binding_key (request_binding request))"
  shows "core = run_finality (call_operations (retained_log (retained_source (reference_product before)))
        (initial_finality_core balances regulatory contexts)) (initial_finality_core balances regulatory contexts)"
    "let (updated,reply) = invoke_protocol endpoint (core_epoch core) index (Cancel_Intent request generation versions) core
     in reply = Protocol_Response Request_Rejected \<and> machine_state (core_parent updated) = machine_state (core_parent core)"
    "let (updated,reply) = invoke_protocol endpoint (core_epoch core) index (Fence_Intent request generation versions) core
     in reply = Protocol_Response Request_Rejected \<and> machine_state (core_parent updated) = machine_state (core_parent core)"
    "let updated = fst (invoke_protocol endpoint (core_epoch core) index (Reassign_Intent request duration) core)
     in unresolved_source_obligations (machine_state (core_parent updated)) = unresolved_source_obligations (machine_state (core_parent core)) \<and>
        issued_certificates (machine_state (core_parent updated)) = issued_certificates (machine_state (core_parent core))"
proof -
  have contract: "reference_service_contract registered (initial_finality_core balances regulatory contexts) before"
    unfolding before_def by (rule every_reference_prefix_keeps_the_central_authority_contract[OF start])
  show "core = run_finality (call_operations (retained_log (retained_source (reference_product before)))
        (initial_finality_core balances regulatory contexts)) (initial_finality_core balances regulatory contexts)"
    unfolding core_def by (rule actual_reference_history_consumes_the_public_replay_and_single_origin_settlement(1)[OF contract])
  show "let (updated,reply) = invoke_protocol endpoint (core_epoch core) index (Cancel_Intent request generation versions) core
     in reply = Protocol_Response Request_Rejected \<and> machine_state (core_parent updated) = machine_state (core_parent core)"
    using actual_cancel_cannot_release_a_pending_source[OF pending, where endpoint=endpoint and index=index and g=generation and versions=versions]
    by (simp add: Let_def split_def)
  show "let (updated,reply) = invoke_protocol endpoint (core_epoch core) index (Fence_Intent request generation versions) core
     in reply = Protocol_Response Request_Rejected \<and> machine_state (core_parent updated) = machine_state (core_parent core)"
    using actual_fence_cannot_release_a_debited_source[OF debited, where endpoint=endpoint and index=index and g=generation and versions=versions]
    by (simp add: Let_def split_def)
  show "let updated = fst (invoke_protocol endpoint (core_epoch core) index (Reassign_Intent request duration) core)
     in unresolved_source_obligations (machine_state (core_parent updated)) = unresolved_source_obligations (machine_state (core_parent core)) \<and>
        issued_certificates (machine_state (core_parent updated)) = issued_certificates (machine_state (core_parent core))"
    using actual_reassignment_preserves_pending_and_source_evidence[where s=core and endpoint=endpoint and index=index and r=request and duration=duration]
    by (simp add: Let_def)
qed

theorem the_old_session_of_an_actual_handover_cannot_retry_cancel_or_execute_any_later_immediate_call:
  fixes before prefix initial
  defines "before \<equiv> run_reference_word execute prefix initial"
  assumes changed: "serve connection (Service_Handover owner_token successor_token maintainer proposal) supplied before =
      (after,Some (Scheduled_Endpoint (Service_Handover_Result True)))"
    and old: "proof_session proof = transfer_old_session proposal"
  shows "serve follow_connection (Service_Execute route old_token proof target action authorization) follow_supplied after =
        (after,Some (Scheduled_Endpoint (Service_Execution_Result Durable_Execution_Reject)))"
proof -
  let ?live = "reopen_retained_product follow_connection (reference_product after)"
  note handover = changed[unfolded actual_execute reference_service_input.select_convs]
  have current: "reference_grants_fit registered (reference_product after) (reference_inputs after)"
    by (rule reference_service_success_preserves_epoch_and_grant_binding[OF handover])
  have absent: "product_sessions (product_durable (identity_source ?live)) (proof_session proof) = None"
    using old the_actual_reference_handover_updates_owner_sessions_and_grants_at_one_epoch(2)[OF handover]
    by (simp add: recovery_projection_supplies_the_exact_source reopen_retained_source_def)
  have denied: "\<not> authorized_endpoint_action directory policy authenticate verify route old_token proof target action ?live"
    using absent by (auto simp: authorized_endpoint_action_def endpoint_call_allowed_on_def endpoint_call_allowed_def
      endpoint_call_identity_def active_identity_def Let_def split: option.splits prod.splits)
  have rejected: "durable_execute directory policy authenticate verify endorse route old_token proof target action authorization
      legal_grant order_verified spend_grant spend_verified read_permitted (reference_permitted_at (reference_inputs after))
      verified maintainers registered verified_ack ?live = (?live,Durable_Execution_Reject)"
    using denied by (auto simp: durable_execute_def split: option.splits prod.splits)
  show ?thesis using current
    by (simp add: actual_execute service_at_reference_snapshot_def schedule_at_retained_state_def schedule_service_step_def
       select_reference_grants_def rejected product_round_trip_preserves_the_durable_projection Let_def)
qed

theorem an_actual_handover_keeps_the_pending_claim_and_moves_its_recovery_controller:
  fixes before prior current prefix initial after connection
  defines "before \<equiv> run_reference_word execute prefix initial"
    and "prior \<equiv> identity_source (reopen_retained_product connection (reference_product before))"
    and "current \<equiv> identity_source (reopen_retained_product connection (reference_product after))"
  assumes step: "serve connection (Service_Handover owner_token successor_token maintainer proposal) supplied before =
       (after, Some (Scheduled_Endpoint (Service_Handover_Result True)))"
    and open_claim: "recoverable_reservation prior key = Some claim"
    and asset: "binding_asset (reservation_binding claim) = transfer_asset proposal"
  shows "recoverable_reservation current key = Some claim"
    "recovery_controller current key = Some (transfer_successor proposal)"
    "issued_certificates (authoritative_reservation_state current) = issued_certificates (authoritative_reservation_state prior)"
proof -
  note handover = the_actual_reference_handover_updates_owner_sessions_and_grants_at_one_epoch
    [OF step[unfolded actual_execute reference_service_input.select_convs]]
  have reservations: "authoritative_reservation_state current = authoritative_reservation_state prior"
    using handover(5)
    by (simp add: current_def prior_def recovery_projection_supplies_the_exact_source
      authoritative_reservation_state_def reopen_retained_source_def)
  show pending: "recoverable_reservation current key = Some claim"
    using open_claim by (simp add: recoverable_reservation_def reservations)
  have owner: "owner_of_product current (transfer_asset proposal) = Some (transfer_successor proposal)"
    using handover(1) by (simp add: current_def recovery_projection_supplies_the_exact_source
      reopen_retained_source_def owner_of_product_def)
  show "recovery_controller current key = Some (transfer_successor proposal)"
    using owner by (simp add: recovery_controller_def pending asset)
  show "issued_certificates (authoritative_reservation_state current) = issued_certificates (authoritative_reservation_state prior)"
    by (simp only: reservations)
qed

theorem an_actual_fresh_recovery_reply_consumes_the_endorsement_of_the_current_controller:
  fixes before live prefix initial connection
  defines "before \<equiv> run_reference_word execute prefix initial"
    and "live \<equiv> reopen_retained_product connection (reference_product before)"
  assumes step: "serve connection (Service_Execute route token proof target action authorization) supplied before =
       (after, Some (Scheduled_Endpoint (Service_Execution_Result (Durable_Execution_Reply result))))"
    and claim: "external_call_claim action = Some (Execute_Ordinary,actor,call_id,payload)"
    and recovery: "owner_claim_origin (envelope_command (payload_envelope payload)) = Some key"
    and fresh: "\<not> authority_has_call_id call_id live"
  shows "\<exists>signed identity scope. authorization = Some signed \<and> authenticate (endorsement_token signed) = Some identity \<and>
      scope = endorsement_session signed \<and> active_identity directory identity scope (identity_source live) \<and>
      recovery_controller (identity_source live) key = Some (identity_principal identity) \<and>
      endorse identity scope target key call_id payload"
proof -
  note actual = a_reference_step_uses_the_actual_service_with_the_retained_grants[OF step[unfolded actual_execute reference_service_input.select_convs]]
  have reply: "snd (durable_execute directory policy authenticate verify endorse route token proof target action authorization
      legal_grant order_verified spend_grant spend_verified read_permitted (reference_permitted_at (reference_inputs before))
      verified maintainers registered verified_ack live) = Durable_Execution_Reply result"
    using actual by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def live_def)
  have requirement: "recovery_requirements directory policy authenticate endorse target action authorization (identity_source live)"
    using claim fresh reply by (cases "execution_receipt_request action") (auto simp: durable_execute_def split: if_splits)
  show ?thesis using requirement claim recovery by (cases authorization)
    (auto simp: recovery_requirements_def recovery_has_current_endorsement_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms reference_trace_consumer.the_actual_public_continuation_of_a_reference_prefix_preserves_pending_across_lock_control
    reference_trace_consumer.the_old_session_of_an_actual_handover_cannot_retry_cancel_or_execute_any_later_immediate_call
    reference_trace_consumer.an_actual_handover_keeps_the_pending_claim_and_moves_its_recovery_controller
    reference_trace_consumer.an_actual_fresh_recovery_reply_consumes_the_endorsement_of_the_current_controller})
  then () else error "Unexpected oracle in handover and lock bounds"
\<close>

end
