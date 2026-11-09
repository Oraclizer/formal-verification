theory Write_Canary_DurableV6
  imports "OIP_Product.Durable_Execution" "OIP_Product.Recovery_Records"
    "OIP_Reference_Profile.Reference_Response_Codes"
begin

lemma write_has_a_committed_recorded_code:
  "reference_response_compatible Wire_Lock 7 Recorded_Result 20 True"
  "\<not> reference_response_compatible Wire_Lock 7 Recorded_Result 20 False"
  by (simp_all add: reference_response_compatible_def reference_result_codes_def reference_result_targets_def)

context source_attestation
begin

lemma fresh_write_at_an_obsolete_cut_retains_busy_without_effect:
  assumes write_command: "envelope_command (payload_envelope payload) = Client_Protocol endpoint index (Write_Intent request generation versions value)"
    and signed: "expected = envelope_cut (payload_envelope payload)"
    and connected: "call_connection (product_calls (identity_source s)) = Authority_Connected"
    and stale: "expected \<noteq> current_product_cut (identity_source s)"
    and fresh: "\<not> authority_has_call_id call_id s"
  shows "let after = run_fresh_durable_effect permitted verified maintainers registered verified_ack
     legal_grant order_verified spend_grant spend_verified read_permitted
     (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s
    in outcome_source (current_product_outcomes after) = outcome_source (current_product_outcomes s) \<and>
       outcome_entries (current_product_outcomes after) call_id =
         Some \<lparr>result_payload = payload, result_outcome = Authority_Busy\<rparr>"
  using assms by (simp add: Let_def checked_refusal_keeps_the_exact_underlying_source
      fresh_checked_refusal_records_the_exact_request)

lemma authorized_exact_write_retry_reads_before_the_fresh_cut:
  assumes write_command: "envelope_command (payload_envelope payload) = Client_Protocol endpoint index (Write_Intent request generation versions value)"
    and admitted: "authorized_endpoint_action directory policy authenticate verify route token proof target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s"
    and up: "call_local_status (product_calls (identity_source s)) = Endpoint_Up"
    and receipt: "retained_receipt_permission policy authenticate token proof target payload"
    and ordinary: "unclaimed_regulated_call s call_id"
    and bound: "result_access_bound verified actor call_id payload (current_product_outcomes s)"
    and recorded: "outcome_entries (current_product_outcomes s) call_id = Some
      \<lparr>result_payload = payload, result_outcome = Authority_Reply (Protocol_Response Data_Updated)\<rparr>"
  shows "let retry = durable_execute directory policy authenticate verify endorse route token proof target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s
    in snd retry = Durable_Execution_Reply (Observed_Ordinary_Result (Collected (Authority_Reply (Protocol_Response Data_Updated)))) \<and>
       outcome_source (current_product_outcomes (fst retry)) = outcome_source (current_product_outcomes s)"
proof -
  let ?action = "Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)"
  let ?collect = "Ordinary_Product_Action (Read_Authority_Action (Exact_Collect actor call_id payload))"
  have claim: "external_call_claim ?action = Some (Execute_Ordinary, actor, call_id, payload)"
    by simp
  have collect: "execution_receipt_request ?action = Some ?collect"
    by simp
  have known: "authority_has_call_id call_id s"
    using recorded by (simp add: authority_has_call_id_def)
  have retained: "durable_execute directory policy authenticate verify endorse route token proof target ?action authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s =
      finish_durable_execution verified actor ?collect s"
    by (rule an_admitted_exact_retry_checks_the_retained_result_before_fresh_conditions[OF claim collect admitted up known receipt])
  have source_up: "call_local_status (product_calls (outcome_source (current_product_outcomes s))) = Endpoint_Up"
    using up by (simp add: identity_source_def observed_product_source_def regulated_read_world_def
      current_product_outcomes_def legal_underlying_outcomes_def)
  have reply: "snd (finish_durable_execution verified actor ?collect s) =
      Durable_Execution_Reply (Observed_Ordinary_Result (Collected (Authority_Reply (Protocol_Response Data_Updated))))"
    using ordinary bound recorded source_up write_command
    by (simp add: Let_def observe_collection_def result_completion_ready_def)
  show ?thesis by (simp only: Let_def retained reply finishing_does_not_reapply_authority_effects simp_thms)
qed

end

lemma reopening_preserves_the_exact_result_table:
  "outcome_entries (current_product_outcomes (reopen_retained_product connection (capture_retained_product s))) =
    outcome_entries (current_product_outcomes s)"
proof -
  have projection: "retained_outcomes (capture_retained_product p) = outcome_entries (current_product_outcomes p)" for p
    by (simp add: capture_retained_product_def current_product_outcomes_def legal_underlying_outcomes_def Let_def)
  show ?thesis by (simp only: projection[symmetric] product_round_trip_preserves_the_durable_projection)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms write_has_a_committed_recorded_code
      source_attestation.fresh_write_at_an_obsolete_cut_retains_busy_without_effect
      source_attestation.authorized_exact_write_retry_reads_before_the_fresh_cut reopening_preserves_the_exact_result_table})
  then () else error "Unexpected oracle in the Write durable canary"
\<close>

end
