theory Reference_Freeze_Spender
  imports Reference_Frozen_Consumption
begin

context source_attestation
begin

theorem an_actual_reference_spend_during_freeze_preserves_money_and_records_refusal:
  fixes connection before live actor call_id payload action
    legal reads authority origins outcomes source envelope command expected cfg
  defines "live \<equiv> reopen_retained_product connection (reference_product before)"
    and "legal \<equiv> governed_legal (regulated_orders live)"
    and "reads \<equiv> legal_reads legal"
    and "authority \<equiv> read_authority reads"
    and "origins \<equiv> settlement_primary authority"
    and "outcomes \<equiv> origin_outcomes origins"
    and "source \<equiv> outcome_source outcomes"
    and "envelope \<equiv> payload_envelope payload"
    and "command \<equiv> envelope_command envelope"
    and "expected \<equiv> observed_product_cut authority"
    and "cfg \<equiv> authoritative_read_core authority"
    and "action \<equiv> Apply_Governed_Spend Regulatory_Normal actor expected call_id payload None"
  assumes step: "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
    authenticated connection (Service_Execute route token proof target action endorsement) supplied before = (after, Some reply)"
    and admitted: "authorized_endpoint_action directory policy authenticate verify route token proof target action live"
    and up: "call_local_status (product_calls (identity_source live)) = Endpoint_Up"
    and available_id: "\<not> authority_has_call_id call_id live"
    and endorsed: "recovery_requirements directory policy authenticate endorse target action endorsement (identity_source live)"
    and ordinary: "command = Client_Protocol endpoint index (Descendant_Intent r root sender recipient amount)"
      "binding_operation (request_binding r) = Ordinary_Transfer_Effect"
    and valid: "valid_state (receiver_snapshot (core_regulatory cfg))"
    and frozen: "get_reg_state (receiver_snapshot (core_regulatory cfg))
      (binding_destination root) (binding_asset (request_binding r)) = Some FROZEN"
    and fresh: "product_new_call actor call_id envelope source"
    and authentic: "verified actor call_id payload"
    and unrecorded: "outcome_entries outcomes call_id = None"
      "legal_receipts (regulated_orders live) call_id = None" "spend_receipts live call_id = None"
    and scope: "reference_permitted_at (reference_inputs before) (regulatory_lock_entry Regulatory_Normal) actor command"
      "registered_lock_envelope registered envelope" "lock_envelope_admitted actor envelope (payload_credential payload) source"
      "origin_command_allowed origins envelope (payload_origin_epoch payload) command"
  shows "retained_outcomes (reference_product after) call_id =
      Some \<lparr>result_payload = payload, result_outcome = Authority_Rejected\<rparr>"
    "machine_state (core_parent (retained_core (retained_source (reference_product after)))) =
      machine_state (core_parent cfg)"
proof -
  let ?permitted = "reference_permitted_at (reference_inputs before)"
  let ?checked = "execute_at_checked_cut ?permitted verified maintainers registered verified_ack
      (regulatory_lock_entry Regulatory_Normal) actor expected call_id payload reads"
  let ?checked_outcomes = "origin_outcomes (settlement_primary (read_authority (fst ?checked)))"
  let ?next = "fst (submit_governed_spend spend_grant spend_verified ?permitted verified maintainers registered verified_ack
      Regulatory_Normal actor expected call_id payload None live)"
  note cut_path = source_def outcomes_def origins_def authority_def envelope_def command_def
  note base = cut_path reads_def legal_def
  have selected: "reference_regulatory_write action"
    "external_call_claim action = Some (Spend_Protected_Root, actor, call_id, payload)"
    by (simp_all add: action_def)
  have actual: "reference_product after = capture_retained_product ?next"
    using a_fresh_regulatory_service_uses_the_actual_governed_product_step
      [OF step selected(1) admitted[unfolded live_def] up[unfolded live_def] selected(2)
        available_id[unfolded live_def] endorsed[unfolded live_def]]
    by (simp add: action_def live_def)
  have allowed: "governed_spend_is_admitted spend_grant spend_verified actor payload None legal"
    using ordinary by (simp add: governed_spend_is_admitted_def command_def envelope_def)
  have access: "result_access_bound verified actor call_id payload outcomes"
    using fresh authentic by (simp add: result_access_bound_def product_new_call_def envelope_def source_def)
  have ready: "call_local_status (product_calls source) = Endpoint_Up"
    "call_connection (product_calls source) = Authority_Connected"
    using fresh by (simp_all add: product_new_call_def)
  have available: "read_authority_available reads"
    using ready by (simp add: read_authority_available_def exact_calls_def outcome_calls_def base)
  have nested: "legal_underlying_outcomes legal = outcomes"
    by (simp add: legal_underlying_outcomes_def base)
  have actual_outcomes: "legal_underlying_outcomes (governed_legal (regulated_orders ?next)) = ?checked_outcomes"
    using access available allowed unrecorded nested
    by (simp add: submit_governed_spend_def run_spend_effect_def Let_def
        replace_regulated_reads_def legal_underlying_outcomes_def read_authority_available_def
        legal_def reads_def)
  have actual_refusal: "outcome_entries ?checked_outcomes call_id =
      Some \<lparr>result_payload = payload, result_outcome = Authority_Rejected\<rparr> \<and>
       machine_state (core_parent (call_authority_state (outcome_calls ?checked_outcomes))) = machine_state (core_parent cfg)"
    unfolding expected_def cfg_def cut_path
    using the_checked_frozen_spend_records_refusal_and_preserves_the_ledger
      [where permitted="?permitted" and entry="regulatory_lock_entry Regulatory_Normal" and reads=reads
          and verified=verified and verified_ack=verified_ack,
       OF ordinary[unfolded cut_path] valid[unfolded cfg_def cut_path] frozen[unfolded cfg_def cut_path]
          fresh[unfolded cut_path] authentic unrecorded(1)[unfolded cut_path] scope[unfolded cut_path]]
    by (simp add: Let_def)
  show "retained_outcomes (reference_product after) call_id =
      Some \<lparr>result_payload = payload, result_outcome = Authority_Rejected\<rparr>"
    using actual_refusal actual_outcomes by (simp add: actual capture_retained_product_def legal_underlying_outcomes_def Let_def)
  show "machine_state (core_parent (retained_core (retained_source (reference_product after)))) =
      machine_state (core_parent cfg)"
    using actual_refusal actual_outcomes
    by (simp add: actual capture_retained_product_def capture_retained_source_def legal_underlying_outcomes_def outcome_calls_def Let_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.an_actual_reference_spend_during_freeze_preserves_money_and_records_refusal})
  then () else error "Unexpected oracle in reference frozen spend consumption"
\<close>

end
