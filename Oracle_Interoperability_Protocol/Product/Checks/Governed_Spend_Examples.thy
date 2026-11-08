theory Governed_Spend_Examples
  imports "../Regulated_Acceptance" Freeze_Spend_Examples "OIP_Product_Base.Lock_Endpoint_Examples"
begin

abbreviation funded_product_submit where
  "funded_product_submit \<equiv>
    source_attestation.submit_governed_spend example_roster example_threshold (source_receipt_verifies regulation_receipts)"

definition funded_product_source where
  "funded_product_source = (lock_example_world sample_initial)\<lparr>
    product_calls := initial_call_machine regulation_denied\<rparr>"

definition funded_product_world where
  "funded_product_world = initial_regulated_product (initial_product_reads 100 (initial_settlement_world 99
     ((initial_origin_world funded_product_source)\<lparr>origin_decisions := (\<lambda>_. None)((0,17) :=
        Some \<lparr>origin_binding = regulation_money_binding, origin_kind = Confirmed_Decision, origin_epoch = 9,
          origin_commit_position = 0\<rparr>)\<rparr>)))"

definition funded_product_payload where
  "funded_product_payload = \<lparr>payload_envelope = (lock_example_envelope
      (Client_Protocol 2 0 regulation_enforcement_intent))\<lparr>envelope_asset := 20\<rparr>,
    payload_credential = None, payload_origin_epoch = 9\<rparr>"

definition funded_spend_order where
  "funded_spend_order = \<lparr>spend_root = regulation_money_binding, spend_kind = Legal_Recover, spend_officer = 7,
    spend_sender = 3, spend_recipient = 4, spend_amount = 1, spend_jurisdiction = 1, spend_legal_basis = 1,
    spend_scope = {20}, spend_prior_seizure = None, spend_appeal_deadline = None\<rparr>"

lemmas funded_product_defs = funded_product_world_def funded_product_source_def funded_product_payload_def funded_spend_order_def
  initial_regulated_product_def initial_governed_world_def initial_legal_world_def initial_product_reads_def
  initial_settlement_world_def initial_origin_world_def initial_outcome_world_def lock_example_world_def lock_example_envelope_def
  regulation_enforcement_intent_def regulation_spend_request_def regulation_money_request_def regulation_money_binding_def
  descendant_binding_def example_binding_def initial_call_machine_def

lemma funded_product_exhibits_the_actual_regulated_receipt:
  "let after = fst (funded_product_submit (\<lambda>_ _ _ _ _. True) (\<lambda>_ _ _. True)
         (\<lambda>_ _ _. True) (\<lambda>_ _ _. True) {} {2} (\<lambda>_. False)
         entry 7 \<lparr>cut_authority_epoch = 9, cut_revision = 0\<rparr> (7,1) funded_product_payload
         (Some funded_spend_order) funded_product_world);
       recorded = legal_underlying_outcomes (governed_legal (regulated_orders after))
   in outcome_entries recorded (7,1) = Some
      \<lparr>result_payload = funded_product_payload, result_outcome = Authority_Reply (Protocol_Response Descendant_Executed)\<rparr>"
proof -
  let ?legal = "governed_legal (regulated_orders funded_product_world)"
  let ?authority = "read_authority (legal_reads ?legal)"
  let ?origins = "settlement_primary ?authority"
  let ?source = "outcome_source (origin_outcomes ?origins)"
  let ?envelope = "payload_envelope funded_product_payload"
  have core: "authoritative_read_core ?authority = regulation_denied"
    by (simp add: authoritative_read_core_def exact_calls_def outcome_calls_def funded_product_defs)
  have cut: "observed_product_cut ?authority = \<lparr>cut_authority_epoch = 9, cut_revision = 0\<rparr>"
    by (simp add: observed_product_cut_def observed_product_source_def current_product_cut_def funded_product_defs)
  have lawful: "lawful_enforcement_preconditions (authoritative_read_core ?authority)
    2 0 (regulation_spend_request (Enforcement_Transfer_Effect Legal_Recover)) regulation_money_binding 3 4 1 Legal_Recover"
    unfolding core by (rule the_same_frozen_root_meets_all_lawful_enforcement_preconditions)
  have admitted: "governed_spend_is_admitted (\<lambda>_ _ _ _ _. True) (\<lambda>_ _ _. True) 7
    funded_product_payload (Some funded_spend_order) ?legal"
    by (simp add: governed_spend_is_admitted_def exact_spend_authorization_def funded_product_defs)
  have fresh: "product_new_call 7 (7,1) ?envelope ?source"
    by (simp add: product_new_call_def product_identity_bound_def current_product_cut_def funded_product_defs)
  have lock: "lock_envelope_admitted 7 ?envelope (payload_credential funded_product_payload) ?source"
    by (simp add: lock_envelope_admitted_def envelope_matches_request_def envelope_matches_binding_def funded_product_defs)
  have origin: "origin_command_allowed ?origins ?envelope (payload_origin_epoch funded_product_payload)
    (envelope_command ?envelope)"
    by (simp add: existing_decision_matches_def decision_matches_def funded_product_defs)
  have command: "envelope_command ?envelope = Client_Protocol 2 0
    (Descendant_Intent (regulation_spend_request (Enforcement_Transfer_Effect Legal_Recover)) regulation_money_binding 3 4 1)"
    by (simp add: funded_product_payload_def lock_example_envelope_def regulation_enforcement_intent_def)
  let ?after = "fst (funded_product_submit (\<lambda>_ _ _ _ _. True) (\<lambda>_ _ _. True)
    (\<lambda>_ _ _. True) (\<lambda>_ _ _. True) {} {2} (\<lambda>_. False)
    entry 7 (observed_product_cut ?authority) (7,1) funded_product_payload (Some funded_spend_order) funded_product_world)"
  have "outcome_entries (legal_underlying_outcomes (governed_legal (regulated_orders ?after))) (7,1) =
    Some \<lparr>result_payload = funded_product_payload, result_outcome = Authority_Reply (Protocol_Response Descendant_Executed)\<rparr>"
    by (rule source_attestation.admitted_enforcement_executes_and_records_the_exact_funded_spend[unfolded Let_def,
          THEN conjunct1, OF regulation_case.source_attestation_axioms command lawful admitted fresh])
      (use lock origin in \<open>simp_all add: registered_lock_envelope_def funded_product_defs\<close>)
  then show ?thesis by (simp only: Let_def cut)
qed

end
