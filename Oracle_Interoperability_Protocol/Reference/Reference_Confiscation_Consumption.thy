theory Reference_Confiscation_Consumption
  imports Reference_Regulatory_Consumption
begin

context source_attestation
begin

lemma a_new_forwarded_legal_receipt_is_from_the_actual_legal_effect:
  assumes fresh: "legal_receipts governed call_id = None"
    and stored: "legal_receipts (fst (submit_governed_order legal_grant order_verified permitted verified
      maintainers registered verified_ack stage entry actor expected call_id order payload governed)) call_id = Some receipt"
    and forwarded: "legal_result receipt = Legal_Checked Forwarded_At_Checked_Cut"
  shows "snd (run_legal_effect legal_grant order_verified permitted verified maintainers registered verified_ack
      stage entry actor expected call_id order payload (governed_legal governed)) = Legal_Checked Forwarded_At_Checked_Cut"
  using fresh stored forwarded
  by (auto simp: submit_governed_order_def Let_def split: if_splits)

theorem actual_reference_confiscation_consumes_current_seizure_and_its_exact_deadline:
  assumes step: "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
    authenticated connection
      (Service_Execute route token proof target (Apply_Governed_Order stage entry actor expected call_id order payload) authorization)
      supplied before = (after, Some reply)"
    and admitted: "authorized_endpoint_action directory policy authenticate verify route token proof target
      (Apply_Governed_Order stage entry actor expected call_id order payload)
      (reopen_retained_product connection (reference_product before))"
    and live: "call_local_status (product_calls
      (identity_source (reopen_retained_product connection (reference_product before)))) = Endpoint_Up"
    and fresh: "\<not> authority_has_call_id call_id (reopen_retained_product connection (reference_product before))"
    and endorsed: "recovery_requirements directory policy authenticate endorse target
      (Apply_Governed_Order stage entry actor expected call_id order payload) authorization
      (identity_source (reopen_retained_product connection (reference_product before)))"
    and recorded: "retained_legal_receipts (reference_product after) call_id = Some receipt"
    and forwarded: "legal_result receipt = Legal_Checked Forwarded_At_Checked_Cut"
    and confiscation: "legal_action order = CONFISCATE"
  shows "let authority = governed_legal (regulated_orders (reopen_retained_product connection (reference_product before)))
    in legal_current_state authority (fst (legal_origin order)) (legal_asset order) = Some SEIZED \<and>
       exact_legal_predecessor authority order (active_seizure_event authority (legal_asset order)) SEIZE \<and>
       appeal_has_elapsed authority order \<and> legal_destination order \<noteq> None"
proof -
  let ?live = "reopen_retained_product connection (reference_product before)"
  let ?governed = "regulated_orders ?live"
  let ?permitted = "reference_permitted_at (reference_inputs before)"
  let ?action = "Apply_Governed_Order stage entry actor expected call_id order payload"
  let ?next = "regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted
     ?permitted verified maintainers registered verified_ack
     (Apply_Governed_Order stage Regulatory_Normal actor expected call_id order payload) ?live"
  have regulated: "reference_regulatory_write ?action" by simp
  have "\<exists>operation. external_call_claim ?action = Some (operation, actor, call_id, payload)"
    by (cases stage) auto
  then obtain operation where selected: "external_call_claim ?action = Some (operation, actor, call_id, payload)" by blast
  have actual: "reference_product after = capture_retained_product ?next"
    using a_fresh_regulatory_service_uses_the_actual_governed_product_step[OF step regulated admitted live selected fresh endorsed]
    by simp
  have fresh_legal: "legal_receipts ?governed call_id = None"
    and fresh_spend: "spend_receipts ?live call_id = None"
    using fresh by (auto simp: authority_has_call_id_def unclaimed_regulated_call_def)
  have saved: "legal_receipts (fst (submit_governed_order legal_grant order_verified ?permitted verified
      maintainers registered verified_ack stage Regulatory_Normal actor expected call_id order payload ?governed)) call_id = Some receipt"
    using recorded fresh_spend
    by (simp add: actual capture_retained_product_def Let_def)
  have executed: "snd (run_legal_effect legal_grant order_verified ?permitted verified maintainers registered verified_ack
      stage Regulatory_Normal actor expected call_id order payload (governed_legal ?governed)) =
      Legal_Checked Forwarded_At_Checked_Cut"
    by (rule a_new_forwarded_legal_receipt_is_from_the_actual_legal_effect[OF fresh_legal saved forwarded])
  show ?thesis unfolding Let_def
    by (rule confiscation_forwarding_consumes_the_current_seizure_and_deadline[OF confiscation executed])
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.a_new_forwarded_legal_receipt_is_from_the_actual_legal_effect
      source_attestation.actual_reference_confiscation_consumes_current_seizure_and_its_exact_deadline})
  then () else error "Unexpected oracle in actual reference confiscation"
\<close>

end
