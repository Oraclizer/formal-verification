theory Refund_Origin_Link
  imports "OIP_V062_Handover_Recovery_Control_Base.Control_Recovery_Base"
    "OIP_Terminal_Record_G0.Terminal_Record_G0"
    "OIP_Product.Owner_Recovery_Effect"
    "Evidence_Atomic_Binding.Finality_Terminal_Progress"
begin

text \<open>
  The authenticated source and the retained authority decision are separate.
  The wire reference names the exact evidence entry. Index zero below is the
  first entry of the logical evidence list, not a wire reference number.
  Publication gates visibility of a stored successful result. A receipt
  observation consumes the result without performing another release.
\<close>

context source_attestation
begin

lemma ror_first_record_supplies_exact_reversal:
  fixes s :: finality_core and cert :: source_certificate
  assumes checked: "certificate_ok cert" "source_origin_present cert s"
    and selected: "statement_binding (certificate_statement cert) = b"
      "statement_status (certificate_statement cert) = Reversed"
    and fresh: "core_records s (binding_key b) = None"
  defines "recorded \<equiv> fst (record_terminal cert s)"
  shows "snd (record_terminal cert s) = Terminal_Recorded"
    "exact_record_reference recorded 0 b Reversed_Decision cert"
    "core_parent recorded = core_parent s"
  using checked selected fresh
  by (simp_all add: recorded_def record_terminal_def exact_record_reference_def record_reference_def Let_def)

lemma ror_record_activates_only_the_same_origin_decision:
  fixes origins :: origin_world and s :: finality_core and cert :: source_certificate
    and position :: nat
  assumes checked: "certificate_ok cert" "source_origin_present cert s"
    and selected: "statement_binding (certificate_statement cert) = request_binding request"
      "statement_status (certificate_statement cert) = Reversed"
    and fresh: "core_records s (binding_key (request_binding request)) = None"
      "origin_decisions origins (binding_key (request_binding request)) = None"
    and debit: "binding_operation (request_binding request) = Destination_Credit"
      "origin_debits origins (binding_key (request_binding request)) = Some (request_binding request, recorded_epoch)"
  defines "after \<equiv> retain_actual_origin_result (Client_Terminal cert)
    (snd (record_terminal cert s)) recorded_epoch position origins"
  shows "origin_command_allowed origins envelope recorded_epoch (Client_Terminal cert)"
    "origin_command_allowed after envelope requested_epoch
       (Client_Protocol endpoint index (Return_Intent request generation versions)) \<longleftrightarrow>
       requested_epoch = recorded_epoch"
proof -
  have accepted: "snd (record_terminal cert s) = Terminal_Recorded"
    by (rule ror_first_record_supplies_exact_reversal(1)[OF checked selected fresh(1)])
  show "origin_command_allowed origins envelope recorded_epoch (Client_Terminal cert)"
    using selected fresh(2) debit by (simp add: terminal_admission_def Let_def)
  show "origin_command_allowed after envelope requested_epoch
       (Client_Protocol endpoint index (Return_Intent request generation versions)) \<longleftrightarrow>
       requested_epoch = recorded_epoch"
    using accepted selected fresh(2)
    by (simp add: after_def retain_actual_origin_result_def retain_first_origin_decision_def
        existing_decision_matches_def decision_matches_def Let_def eq_commute)
qed

lemma ror_missing_exact_reference_leaves_financial_state:
  fixes s :: finality_core and request :: execution_request
    and endpoint index generation :: nat and versions :: version_vector
  assumes absent: "\<not> exact_record_reference s index (request_binding request)
    Reversed_Decision (request_certificate request)"
  defines "result \<equiv> invoke_protocol endpoint (core_epoch s) index
    (Return_Intent request generation versions) s"
  shows "snd result = Finality_Rejected"
    "machine_state (core_parent (fst result)) = machine_state (core_parent s)"
  using absent by (simp_all add: result_def invoke_protocol_def reject_protocol_intent_def record_observation_def)

lemma ror_exact_first_refund_can_publish:
  fixes s :: finality_core and request :: execution_request
    and endpoint index generation :: nat and versions :: version_vector
  assumes exact: "exact_record_reference s index (request_binding request)
    Reversed_Decision (request_certificate request)"
    and fence: "owns_recorded_reservation (current_lock_view s endpoint) request generation
      (vector_lookup versions) (machine_state (core_parent s))"
    and pending: "phase_at (machine_state (core_parent s)) (binding_key (request_binding request)) = Some Source_Pending"
    and verified: "reversed_source_evidence (lock_authority (current_lock_view s endpoint))
      request (machine_state (core_parent s))"
    and retained: "core_records s (binding_key (request_binding request)) = Some record"
      "terminal_binding record = request_binding request" "terminal_kind record = Reversed_Decision"
  defines "result \<equiv> execute_finality_client
    (Client_Protocol endpoint index (Return_Intent request generation versions)) s"
  shows "snd result = Protocol_Response Reservation_Released"
    "source_units (machine_state (core_parent (fst result))) (source_account_of (request_binding request)) =
      source_units (machine_state (core_parent s)) (source_account_of (request_binding request)) + binding_amount (request_binding request)"
    "snd (publish_primary (binding_key (request_binding request)) (fst result)) = Primary_Published"
    "binding_key (request_binding request) \<in> core_published
      (fst (publish_primary (binding_key (request_binding request)) (fst result)))"
proof -
  have effect: "snd result = Protocol_Response Reservation_Released \<and>
    source_units (machine_state (core_parent (fst result))) (source_account_of (request_binding request)) =
      source_units (machine_state (core_parent s)) (source_account_of (request_binding request)) + binding_amount (request_binding request) \<and>
    phase_at (machine_state (core_parent (fst result))) (binding_key (request_binding request)) = Some Source_Returned"
    unfolding result_def
    by (rule exact_return_guard_moves_only_the_committed_pending_amount[unfolded Let_def, OF exact fence pending verified])
  then show "snd result = Protocol_Response Reservation_Released"
    and "source_units (machine_state (core_parent (fst result))) (source_account_of (request_binding request)) =
      source_units (machine_state (core_parent s)) (source_account_of (request_binding request)) + binding_amount (request_binding request)"
    by blast+
  have frame: "core_parent (fst result) = fst (release_to_source (current_lock_view s endpoint)
    request generation (vector_lookup versions) (core_parent s))"
    and record_preserved: "core_records (fst result) (binding_key (request_binding request)) = Some record"
    using exact retained(1)
    by (simp_all add: result_def execute_finality_client_def finality_step_def invoke_protocol_def lift_protocol_result_def Let_def)
  have registered: "binding_is_registered (machine_state (core_parent (fst result))) (request_binding request)"
    unfolding frame by (rule actual_return_preserves_registration[OF fence])
  have complete: "terminal_effect_completed (fst result) record"
    using retained(2,3) registered effect by (simp add: terminal_effect_completed_def Let_def)
  show "snd (publish_primary (binding_key (request_binding request)) (fst result)) = Primary_Published"
    "binding_key (request_binding request) \<in> core_published
      (fst (publish_primary (binding_key (request_binding request)) (fst result)))"
    using record_preserved complete by (simp_all add: publish_primary_def)
qed

end

lemma ror_former_controller_cannot_endorse_even_with_a_valid_reversal:
  "\<not> recovery_has_current_endorsement identity_case_directory policy hc_typed_authenticate
    endorse target (0,17) call_id payload (hc_endorsement 7 2) hc_post_source"
  using hc_actual_controller_is_the_successor
  by (auto simp: recovery_has_current_endorsement_def hc_typed_authenticate_def
      hc_endorsement_def identity_case_user_def)

lemma ror_retained_refund_waits_for_publication_and_reads_exactly:
  fixes payload :: product_call_payload
  defines "stored \<equiv> \<lparr>result_payload = payload,
    result_outcome = Authority_Reply (Protocol_Response Reservation_Released)\<rparr>"
    and "core_of \<equiv> \<lambda>s. call_authority_state (product_calls (outcome_source s))"
  assumes command: "envelope_command (payload_envelope payload) =
    Client_Protocol endpoint index (Return_Intent request generation versions)"
    and live: "call_local_status (product_calls (outcome_source before)) = Endpoint_Up"
      "call_local_status (product_calls (outcome_source after)) = Endpoint_Up"
    and access: "result_access_bound verified who call_id payload before"
      "result_access_bound verified who call_id payload after"
    and entry: "outcome_entries before call_id = Some stored" "outcome_entries after call_id = Some stored"
    and publication: "binding_key (request_binding request) \<notin> core_published (core_of before)"
      "binding_key (request_binding request) \<in> core_published (core_of after)"
    and released: "asset_owner (machine_state (core_parent (core_of after)))
      (envelope_asset (payload_envelope payload)) \<noteq> Some (binding_key (request_binding request))"
  shows "observe_collection verified who call_id payload before = Collection_Waiting"
    "observe_collection verified who call_id payload after =
      Collected (Authority_Reply (Protocol_Response Reservation_Released))"
    "read_authoritative_result verified who call_id payload after =
      Some (Authority_Reply (Protocol_Response Reservation_Released))"
  using command live access entry publication released
  by (simp_all add: core_of_def stored_def observe_collection_def result_completion_ready_def
      read_authoritative_result_def Let_def)

context source_attestation
begin

lemma ror_exact_submit_reuses_the_retained_result:
  assumes "outcome_entries (origin_outcomes s) call_id = Some stored"
  shows "submit_origin_call permitted verified maintainers registered
    route who call_id payload s = s"
  by (rule exact_origin_retry_does_not_repeat_an_effect) (simp add: assms)

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.ror_first_record_supplies_exact_reversal
      source_attestation.ror_record_activates_only_the_same_origin_decision
      source_attestation.ror_missing_exact_reference_leaves_financial_state
      source_attestation.ror_exact_first_refund_can_publish
      ror_former_controller_cannot_endorse_even_with_a_valid_reversal
      ror_retained_refund_waits_for_publication_and_reads_exactly
      source_attestation.ror_exact_submit_reuses_the_retained_result})
  then () else error "Unexpected oracle in Refund origin and retained-result link"
\<close>

end
