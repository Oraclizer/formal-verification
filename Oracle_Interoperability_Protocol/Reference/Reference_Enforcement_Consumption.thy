theory Reference_Enforcement_Consumption
  imports Reference_Regulatory_Consumption "OIP_Product.Regulated_Acceptance"
begin

context source_attestation
begin

theorem the_actual_reference_spend_records_the_exact_enforcement_effect:
  fixes connection before live actor call_id payload authorization action
    legal reads authority origins outcomes source envelope command expected
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
    and "action \<equiv> Apply_Governed_Spend Regulatory_Normal actor expected call_id payload authorization"
  assumes step: "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
    authenticated connection (Service_Execute route token proof target action endorsement) supplied before = (after, Some reply)"
    and admitted: "authorized_endpoint_action directory policy authenticate verify route token proof target action live"
    and up: "call_local_status (product_calls (identity_source live)) = Endpoint_Up"
    and available_id: "\<not> authority_has_call_id call_id live"
    and endorsed: "recovery_requirements directory policy authenticate endorse target action endorsement (identity_source live)"
    and intent: "command = Client_Protocol endpoint index (Descendant_Intent r root sender recipient amount)"
    and lawful: "lawful_enforcement_preconditions (authoritative_read_core authority) endpoint index r root sender recipient amount kind"
    and governed: "governed_spend_is_admitted spend_grant spend_verified actor payload authorization legal"
    and fresh: "product_new_call actor call_id envelope source"
    and authentic: "verified actor call_id payload"
    and unrecorded: "outcome_entries outcomes call_id = None"
      "legal_receipts (regulated_orders live) call_id = None" "spend_receipts live call_id = None"
    and scope: "reference_permitted_at (reference_inputs before) (regulatory_lock_entry Regulatory_Normal) actor command"
      "registered_lock_envelope registered envelope" "lock_envelope_admitted actor envelope (payload_credential payload) source"
      "origin_command_allowed origins envelope (payload_origin_epoch payload) command"
  shows "retained_outcomes (reference_product after) call_id =
     Some \<lparr>result_payload = payload, result_outcome = Authority_Reply (Protocol_Response Descendant_Executed)\<rparr>"
proof -
  let ?permitted = "reference_permitted_at (reference_inputs before)"
  let ?next = "fst (submit_governed_spend spend_grant spend_verified ?permitted verified maintainers registered verified_ack
     Regulatory_Normal actor expected call_id payload authorization live)"
  have regulated: "reference_regulatory_write action" by (simp add: action_def)
  have selected: "external_call_claim action = Some (Spend_Protected_Root, actor, call_id, payload)"
    by (simp add: action_def)
  have actual: "reference_product after = capture_retained_product ?next"
    using a_fresh_regulatory_service_uses_the_actual_governed_product_step
      [OF step regulated admitted[unfolded live_def] up[unfolded live_def]
        selected available_id[unfolded live_def] endorsed[unfolded live_def]]
    by (simp add: action_def live_def)
  have accepted: "outcome_entries (legal_underlying_outcomes (governed_legal (regulated_orders ?next))) call_id =
     Some \<lparr>result_payload = payload, result_outcome = Authority_Reply (Protocol_Response Descendant_Executed)\<rparr>"
    using admitted_enforcement_executes_and_records_the_exact_funded_spend
      [where permitted="?permitted" and entry=Regulatory_Normal and s=live and verified=verified
        and grant=spend_grant and spend_verified=spend_verified and verified_ack=verified_ack,
      OF intent[unfolded command_def envelope_def] lawful[unfolded authority_def reads_def legal_def]
        governed[unfolded legal_def] fresh[unfolded envelope_def source_def outcomes_def origins_def authority_def reads_def legal_def]
        authentic unrecorded(1)[unfolded outcomes_def origins_def authority_def reads_def legal_def]
        unrecorded(2,3) scope(1)[unfolded command_def envelope_def] scope(2)[unfolded envelope_def]
        scope(3)[unfolded envelope_def source_def outcomes_def origins_def authority_def reads_def legal_def]
        scope(4)[unfolded origins_def authority_def reads_def legal_def envelope_def command_def]]
    by (simp add: expected_def authority_def reads_def legal_def Let_def)
  show ?thesis using accepted by (simp add: actual capture_retained_product_def legal_underlying_outcomes_def Let_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.the_actual_reference_spend_records_the_exact_enforcement_effect})
  then () else error "Unexpected oracle in actual reference enforcement"
\<close>

end
