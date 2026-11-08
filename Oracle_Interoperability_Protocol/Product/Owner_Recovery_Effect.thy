theory Owner_Recovery_Effect
  imports Identity_Receipts
begin

context source_attestation
begin

lemma exact_return_guard_moves_only_the_committed_pending_amount:
  fixes authority endpoint index request generation versions before
  defines "before \<equiv> core_parent authority"
  assumes ref: "exact_record_reference authority index (request_binding request) Reversed_Decision (request_certificate request)"
    and fence: "owns_recorded_reservation (current_lock_view authority endpoint) request generation
      (vector_lookup versions) (machine_state before)"
    and pending: "phase_at (machine_state before) (binding_key (request_binding request)) = Some Source_Pending"
    and evidence: "reversed_source_evidence (lock_authority (current_lock_view authority endpoint)) request (machine_state before)"
  shows "let result = execute_finality_client (Client_Protocol endpoint index (Return_Intent request generation versions)) authority;
             account = source_account_of (request_binding request);
             after = machine_state (core_parent (fst result))
         in snd result = Protocol_Response Reservation_Released \<and>
            source_units after account = source_units (machine_state before) account + binding_amount (request_binding request) \<and>
            phase_at after (binding_key (request_binding request)) = Some Source_Returned"
proof -
  let ?context = "current_lock_view authority endpoint"
  let ?parent = "release_to_source ?context request generation (vector_lookup versions) before"
  have accepted: "snd ?parent = Reservation_Released"
    using fence pending evidence by (simp add: release_to_source_def record_observation_def)
  have amount: "source_units (machine_state (fst ?parent)) (source_account_of (request_binding request)) =
        source_units (machine_state before) (source_account_of (request_binding request)) + binding_amount (request_binding request)"
    and phase: "phase_at (machine_state (fst ?parent)) (binding_key (request_binding request)) = Some Source_Returned"
    using successful_release_restores_exact_amount_and_closes[OF accepted] by blast+
  show ?thesis using accepted amount phase ref
    by (simp add: Let_def before_def execute_finality_client_def finality_step_def invoke_protocol_def
        lift_protocol_result_def)
qed

theorem approved_recovery_returns_the_exact_pending_amount_and_records_the_result:
  fixes s payload entry who call_id endpoint index request generation versions
    action reads authority origins outcomes source envelope command
  defines "reads \<equiv> regulated_read_world s"
    and "authority \<equiv> read_authority reads"
    and "origins \<equiv> settlement_primary authority"
    and "outcomes \<equiv> origin_outcomes origins"
    and "source \<equiv> outcome_source outcomes"
    and "envelope \<equiv> payload_envelope payload"
    and "command \<equiv> envelope_command envelope"
    and "action \<equiv> Ordinary_Product_Action (Execute_Checked entry who (observed_product_cut authority) call_id payload)"
  assumes command: "command = Client_Protocol endpoint index (Return_Intent request generation versions)"
    and admitted: "authorized_endpoint_action directory policy authenticate verify route token session target action s"
      "recovery_requirements directory policy authenticate endorse target action authorization source"
    and fresh: "product_new_call who call_id envelope source" "outcome_entries outcomes call_id = None"
      "unclaimed_regulated_call s call_id"
    and authentic: "verified who call_id payload"
    and scope: "permitted Normal_Lock_Entry who command" "registered_lock_envelope registered envelope"
      "lock_envelope_admitted who envelope (payload_credential payload) source"
      "origin_command_allowed origins envelope (payload_origin_epoch payload) command"
    and ref: "exact_record_reference (authoritative_read_core authority) index
      (request_binding request) Reversed_Decision (request_certificate request)"
    and fence: "owns_recorded_reservation (current_lock_view (authoritative_read_core authority) endpoint) request generation
      (vector_lookup versions) (authoritative_reservation_state source)"
    and pending: "phase_at (authoritative_reservation_state source) (binding_key (request_binding request)) = Some Source_Pending"
    and evidence: "reversed_source_evidence (lock_authority (current_lock_view (authoritative_read_core authority) endpoint))
      request (authoritative_reservation_state source)"
  shows "let after = endpoint_with_owner_control directory policy authenticate verify endorse route token session target action authorization
                legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s;
             recorded = legal_underlying_outcomes (governed_legal (regulated_orders after));
             new = authoritative_reservation_state (outcome_source recorded);
             account = source_account_of (request_binding request)
         in outcome_entries recorded call_id = Some
              \<lparr>result_payload = payload, result_outcome = Authority_Reply (Protocol_Response Reservation_Released)\<rparr> \<and>
            source_units new account = source_units (authoritative_reservation_state source) account + binding_amount (request_binding request) \<and>
            phase_at new (binding_key (request_binding request)) = Some Source_Returned"
proof -
  let ?core = "authoritative_read_core authority"
  let ?checked = "execute_at_checked_cut permitted verified maintainers registered verified_ack
    Normal_Lock_Entry who (observed_product_cut authority) call_id payload reads"
  let ?updated = "origin_outcomes (settlement_primary (read_authority (fst ?checked)))"
  let ?result = "execute_finality_client command ?core"
  note unfold_path = source_def outcomes_def origins_def authority_def envelope_def command_def
  have current: "authoritative_reservation_state source = machine_state (core_parent ?core)"
    by (simp add: authoritative_reservation_state_def authoritative_read_core_def exact_calls_def outcome_calls_def unfold_path)
  have selected: "identity_source s = source"
    by (simp add: identity_source_def observed_product_source_def unfold_path reads_def)
  have ungoverned: "\<not> governed_command (envelope_command (payload_envelope payload))"
    using command by (simp add: unfold_path)
  have right: "recovery_requirements directory policy authenticate endorse target action authorization (identity_source s)"
    unfolding selected by (rule admitted(2))
  have "endpoint_with_owner_control directory policy authenticate verify endorse route token session target action authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s =
      replace_regulated_reads (fst ?checked) s"
    unfolding action_def reads_def
    by (rule approved_recovery_reaches_the_real_checked_consumer[OF admitted(1)[unfolded action_def]
          right[unfolded action_def] ungoverned fresh(3)])
  then have mapped: "legal_underlying_outcomes (governed_legal (regulated_orders
      (endpoint_with_owner_control directory policy authenticate verify endorse route token session target action authorization
        legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s))) =
      ?updated"
    by (simp add: legal_underlying_outcomes_def replace_regulated_reads_def)
  have recorded: "snd ?checked = Forwarded_At_Checked_Cut \<and>
    outcome_entries ?updated call_id = Some \<lparr>result_payload = payload, result_outcome = normalized_authority_reply (snd ?result)\<rparr> \<and>
    call_authority_state (outcome_calls ?updated) = fst ?result"
    unfolding unfold_path
    by (rule checked_fresh_execution_uses_the_authority_outcome)
      (use fresh(1,2) authentic scope in \<open>simp_all only: unfold_path\<close>)
  have effect: "let after = machine_state (core_parent (fst ?result)); account = source_account_of (request_binding request)
         in snd ?result = Protocol_Response Reservation_Released \<and>
            source_units after account = source_units (authoritative_reservation_state source) account + binding_amount (request_binding request) \<and>
            phase_at after (binding_key (request_binding request)) = Some Source_Returned"
    unfolding Let_def command current
    by (rule exact_return_guard_moves_only_the_committed_pending_amount[unfolded Let_def, OF ref])
      (use fence pending evidence in \<open>simp_all only: current\<close>)
  show ?thesis unfolding Let_def mapped
    using recorded effect by (simp add: Let_def authoritative_reservation_state_def outcome_calls_def)
qed

end

end
