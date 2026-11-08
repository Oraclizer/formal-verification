theory Reference_Frozen_Consumption
  imports Reference_Regulatory_Consumption "OIP_Product.Regulated_Acceptance"
begin

context source_attestation
begin

lemma the_checked_frozen_spend_records_refusal_and_preserves_the_ledger:
  fixes reads payload actor call_id entry permitted verified maintainers registered verified_ack
    authority origins outcomes source envelope command cfg
  defines "authority \<equiv> read_authority reads"
    and "origins \<equiv> settlement_primary authority"
    and "outcomes \<equiv> origin_outcomes origins"
    and "source \<equiv> outcome_source outcomes"
    and "envelope \<equiv> payload_envelope payload"
    and "command \<equiv> envelope_command envelope"
    and "cfg \<equiv> authoritative_read_core authority"
  assumes ordinary: "command = Client_Protocol endpoint index (Descendant_Intent r root sender recipient amount)"
    "binding_operation (request_binding r) = Ordinary_Transfer_Effect"
    and valid: "valid_state (receiver_snapshot (core_regulatory cfg))"
    and frozen: "get_reg_state (receiver_snapshot (core_regulatory cfg))
      (binding_destination root) (binding_asset (request_binding r)) = Some FROZEN"
    and fresh: "product_new_call actor call_id envelope source"
    and authentic: "verified actor call_id payload"
    and unrecorded: "outcome_entries outcomes call_id = None"
    and admitted: "permitted entry actor command" "registered_lock_envelope registered envelope"
      "lock_envelope_admitted actor envelope (payload_credential payload) source"
      "origin_command_allowed origins envelope (payload_origin_epoch payload) command"
  shows "let checked = execute_at_checked_cut permitted verified maintainers registered verified_ack
        entry actor (observed_product_cut authority) call_id payload reads;
       next = origin_outcomes (settlement_primary (read_authority (fst checked)))
    in outcome_entries next call_id = Some \<lparr>result_payload = payload, result_outcome = Authority_Rejected\<rparr> \<and>
       machine_state (core_parent (call_authority_state (outcome_calls next))) = machine_state (core_parent cfg)"
proof -
  let ?checked = "execute_at_checked_cut permitted verified maintainers registered verified_ack
        entry actor (observed_product_cut authority) call_id payload reads"
  let ?next = "origin_outcomes (settlement_primary (read_authority (fst ?checked)))"
  let ?result = "execute_finality_client command (authoritative_read_core authority)"
  let ?invoke = "invoke_protocol endpoint (core_epoch cfg) index (Descendant_Intent r root sender recipient amount) cfg"
  note unfold_path = source_def outcomes_def origins_def authority_def envelope_def command_def
  have no_thaw: "continuation_has_no_thaw (binding_asset (request_binding r)) [] cfg"
    by simp
  have refused: "snd ?invoke \<in> {Finality_Rejected, Protocol_Response Request_Rejected} \<and>
      machine_state (core_parent (fst ?invoke)) = machine_state (core_parent cfg)"
    using ordinary_spend_after_freeze_without_thaw_is_rejected[OF valid frozen no_thaw ordinary(2)]
    by (simp add: Let_def)
  have actual: "snd ?result = snd ?invoke" "core_parent (fst ?result) = core_parent (fst ?invoke)"
    using ordinary(1) by (simp_all add: cfg_def execute_finality_client_def finality_step_def)
  have checked: "snd ?checked = Forwarded_At_Checked_Cut \<and>
     outcome_entries ?next call_id = Some \<lparr>result_payload = payload, result_outcome = normalized_authority_reply (snd ?result)\<rparr> \<and>
     call_authority_state (outcome_calls ?next) = fst ?result"
    unfolding unfold_path
    by (rule checked_fresh_execution_uses_the_authority_outcome)
       (use fresh authentic unrecorded admitted in \<open>simp_all only: unfold_path\<close>)
  have result: "normalized_authority_reply (snd ?result) = Authority_Rejected"
    using refused actual(1) by auto
  show ?thesis using checked refused actual result by (simp add: Let_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.the_checked_frozen_spend_records_refusal_and_preserves_the_ledger})
  then () else error "Unexpected oracle in reference frozen spending"
\<close>

end
