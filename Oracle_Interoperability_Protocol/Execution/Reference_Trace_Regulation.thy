theory Reference_Trace_Regulation
  imports Reference_Trace_Consumers "OIP_Reference_Profile.Reference_Freeze_Spender"
    "OIP_Reference_Profile.Reference_Enforcement_Consumption" "OIP_Reference_Profile.Reference_Confiscation_Consumption"
begin

context reference_trace_consumer
begin

theorem the_actual_reference_trace_consumes_the_frozen_ordinary_and_lawful_enforcement_branches:
  fixes before live legal reads authority origins outcomes source envelope command action
    prefix initial connection actor call_id payload authorization
  defines "before \<equiv> run_reference_word execute prefix initial"
    and "live \<equiv> reopen_retained_product connection (reference_product before)"
    and "legal \<equiv> governed_legal (regulated_orders live)"
    and "reads \<equiv> legal_reads legal"
    and "authority \<equiv> read_authority reads"
    and "origins \<equiv> settlement_primary authority"
    and "outcomes \<equiv> origin_outcomes origins"
    and "source \<equiv> outcome_source outcomes"
    and "envelope \<equiv> payload_envelope payload"
    and "command \<equiv> envelope_command envelope"
    and "action \<equiv> Apply_Governed_Spend Regulatory_Normal actor (observed_product_cut authority) call_id payload authorization"
  assumes step: "serve connection (Service_Execute route token proof target action endorsement) supplied before = (after,Some reply)"
    and admitted: "authorized_endpoint_action directory policy authenticate verify route token proof target action live"
    and up: "call_local_status (product_calls (identity_source live)) = Endpoint_Up"
    and available: "\<not> authority_has_call_id call_id live"
    and endorsed: "recovery_requirements directory policy authenticate endorse target action endorsement (identity_source live)"
    and intent: "command = Client_Protocol endpoint index (Descendant_Intent request root sender recipient amount)"
    and fresh: "product_new_call actor call_id envelope source"
    and authentic: "verified actor call_id payload"
    and unrecorded: "outcome_entries outcomes call_id = None"
      "legal_receipts (regulated_orders live) call_id = None" "spend_receipts live call_id = None"
    and scope: "reference_permitted_at (reference_inputs before) (regulatory_lock_entry Regulatory_Normal) actor command"
      "registered_lock_envelope registered envelope" "lock_envelope_admitted actor envelope (payload_credential payload) source"
      "origin_command_allowed origins envelope (payload_origin_epoch payload) command"
  shows "\<lbrakk>authorization = None; binding_operation (request_binding request) = Ordinary_Transfer_Effect;
     valid_state (receiver_snapshot (core_regulatory (authoritative_read_core authority)));
     get_reg_state (receiver_snapshot (core_regulatory (authoritative_read_core authority)))
       (binding_destination root) (binding_asset (request_binding request)) = Some FROZEN\<rbrakk> \<Longrightarrow>
     retained_outcomes (reference_product after) call_id =
       Some \<lparr>result_payload = payload, result_outcome = Authority_Rejected\<rparr> \<and>
     machine_state (core_parent (retained_core (retained_source (reference_product after)))) =
       machine_state (core_parent (authoritative_read_core authority))"
    "\<lbrakk>lawful_enforcement_preconditions (authoritative_read_core authority) endpoint index request root sender recipient amount kind;
      governed_spend_is_admitted spend_grant spend_verified actor payload authorization legal\<rbrakk> \<Longrightarrow>
      retained_outcomes (reference_product after) call_id =
       Some \<lparr>result_payload = payload, result_outcome = Authority_Reply (Protocol_Response Descendant_Executed)\<rparr>"
proof -
  note model = step[unfolded actual_execute reference_service_input.select_convs]
  note path = action_def command_def envelope_def source_def outcomes_def origins_def authority_def reads_def legal_def live_def
  have frozen: "retained_outcomes (reference_product after) call_id =
       Some \<lparr>result_payload = payload, result_outcome = Authority_Rejected\<rparr>"
    "machine_state (core_parent (retained_core (retained_source (reference_product after)))) =
       machine_state (core_parent (authoritative_read_core authority))"
    if none: "authorization = None" and ordinary: "binding_operation (request_binding request) = Ordinary_Transfer_Effect"
    and valid: "valid_state (receiver_snapshot (core_regulatory (authoritative_read_core authority)))"
    and protected: "get_reg_state (receiver_snapshot (core_regulatory (authoritative_read_core authority)))
       (binding_destination root) (binding_asset (request_binding request)) = Some FROZEN"
    unfolding path
    by (rule an_actual_reference_spend_during_freeze_preserves_money_and_records_refusal
      [OF model[unfolded path none] admitted[unfolded path none] up[unfolded path] available[unfolded path]
       endorsed[unfolded path none] intent[unfolded path] ordinary valid[unfolded path] protected[unfolded path]
       fresh[unfolded path] authentic unrecorded[unfolded path] scope[unfolded path]])+
  then show "\<lbrakk>authorization = None; binding_operation (request_binding request) = Ordinary_Transfer_Effect;
     valid_state (receiver_snapshot (core_regulatory (authoritative_read_core authority)));
     get_reg_state (receiver_snapshot (core_regulatory (authoritative_read_core authority)))
       (binding_destination root) (binding_asset (request_binding request)) = Some FROZEN\<rbrakk> \<Longrightarrow>
     retained_outcomes (reference_product after) call_id =
       Some \<lparr>result_payload = payload, result_outcome = Authority_Rejected\<rparr> \<and>
     machine_state (core_parent (retained_core (retained_source (reference_product after)))) =
       machine_state (core_parent (authoritative_read_core authority))" by blast
  show "retained_outcomes (reference_product after) call_id =
       Some \<lparr>result_payload = payload, result_outcome = Authority_Reply (Protocol_Response Descendant_Executed)\<rparr>"
    if lawful: "lawful_enforcement_preconditions (authoritative_read_core authority) endpoint index request root sender recipient amount kind"
    and governed: "governed_spend_is_admitted spend_grant spend_verified actor payload authorization legal"
    by (rule the_actual_reference_spend_records_the_exact_enforcement_effect
      [OF model[unfolded path] admitted[unfolded path] up[unfolded path] available[unfolded path] endorsed[unfolded path]
       intent[unfolded path] lawful[unfolded path] governed[unfolded path] fresh[unfolded path]
       authentic unrecorded[unfolded path] scope[unfolded path]])
qed

theorem an_actual_reference_confiscation_receipt_at_a_prefix_consumes_the_issuer_clock_and_seizure:
  fixes before live action governed legal prefix initial connection stage entry actor expected call_id order payload
  defines "before \<equiv> run_reference_word execute prefix initial"
    and "live \<equiv> reopen_retained_product connection (reference_product before)"
    and "action \<equiv> Apply_Governed_Order stage entry actor expected call_id order payload"
    and "governed \<equiv> regulated_orders live"
    and "legal \<equiv> governed_legal governed"
  assumes step: "serve connection (Service_Execute route token proof target action authorization) supplied before = (after, Some reply)"
    and admitted: "authorized_endpoint_action directory policy authenticate verify route token proof target action live"
    and up: "call_local_status (product_calls (identity_source live)) = Endpoint_Up"
    and fresh: "\<not> authority_has_call_id call_id live"
    and endorsed: "recovery_requirements directory policy authenticate endorse target action authorization (identity_source live)"
    and saved: "retained_legal_receipts (reference_product after) call_id = Some receipt"
    and forwarded: "legal_result receipt = Legal_Checked Forwarded_At_Checked_Cut"
    and kind: "legal_action order = CONFISCATE"
  shows "order_verified stage Regulatory_Normal actor order"
    "legal_grant stage Regulatory_Normal actor (legal_jurisdiction order) (legal_asset order) (legal_action order)
       (cut_authority_epoch (legal_current_cut legal))"
    "legal_payload_is_exact stage order payload"
    "legal_current_state legal (fst (legal_origin order)) (legal_asset order) = Some SEIZED \<and>
     exact_legal_predecessor legal order (active_seizure_event legal (legal_asset order)) SEIZE \<and>
     appeal_has_elapsed legal order \<and> legal_destination order \<noteq> None"
proof -
  let ?permitted = "reference_permitted_at (reference_inputs before)"
  let ?run = "submit_governed_order legal_grant order_verified ?permitted verified maintainers registered verified_ack
        stage Regulatory_Normal actor expected call_id order payload governed"
  have selected: "reference_regulatory_write action" by (simp add: action_def)
  obtain operation where call: "external_call_claim action = Some (operation,actor,call_id,payload)"
    by (cases stage) (auto simp: action_def)
  have product: "reference_product after = capture_retained_product
     (regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted ?permitted
       verified maintainers registered verified_ack (canonical_consumer_action action) live)"
    by (rule a_fresh_regulatory_service_uses_the_actual_governed_product_step
      [OF step[unfolded actual_execute reference_service_input.select_convs] selected admitted[unfolded live_def]
       up[unfolded live_def] call fresh[unfolded live_def] endorsed[unfolded live_def], folded live_def])
  have new: "legal_receipts governed call_id = None" and no_spend: "spend_receipts live call_id = None"
    using fresh by (auto simp: governed_def authority_has_call_id_def unclaimed_regulated_call_def)
  have receipt: "legal_receipts (fst ?run) call_id = Some receipt"
    using saved product no_spend by (simp add: action_def governed_def capture_retained_product_def Let_def)
  have runs: "snd (run_legal_effect legal_grant order_verified ?permitted verified maintainers registered verified_ack
        stage Regulatory_Normal actor expected call_id order payload legal) = Legal_Checked Forwarded_At_Checked_Cut"
    unfolding legal_def by (rule a_new_forwarded_legal_receipt_is_from_the_actual_legal_effect[OF new receipt forwarded])
  have actual_gate: "legal_admission_at_cut legal_grant order_verified stage Regulatory_Normal actor order legal = Legal_Admit"
    and bound: "legal_payload_is_exact stage order payload"
    using runs by (cases "legal_admission_at_cut legal_grant order_verified stage Regulatory_Normal actor order legal";
      auto simp: run_legal_effect_def Let_def split: if_splits)+
  show "order_verified stage Regulatory_Normal actor order"
    "legal_grant stage Regulatory_Normal actor (legal_jurisdiction order) (legal_asset order) (legal_action order)
       (cut_authority_epoch (legal_current_cut legal))"
    using actual_gate by (auto simp: legal_admission_at_cut_def split: if_splits)
  show "legal_payload_is_exact stage order payload" by (rule bound)
  show "legal_current_state legal (fst (legal_origin order)) (legal_asset order) = Some SEIZED \<and>
     exact_legal_predecessor legal order (active_seizure_event legal (legal_asset order)) SEIZE \<and>
     appeal_has_elapsed legal order \<and> legal_destination order \<noteq> None"
    by (rule confiscation_forwarding_consumes_the_current_seizure_and_deadline[OF kind runs])
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms reference_trace_consumer.the_actual_reference_trace_consumes_the_frozen_ordinary_and_lawful_enforcement_branches
    reference_trace_consumer.an_actual_reference_confiscation_receipt_at_a_prefix_consumes_the_issuer_clock_and_seizure})
  then () else error "Unexpected oracle in reference trace regulation"
\<close>

end
