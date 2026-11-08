theory Reference_Entry_Closure
  imports "Reference_Central_Trace" "OIP_Product.Promotion_Endpoint"
begin

lemma clearing_a_process_cache_keeps_the_authoritative_identity_source:
  "identity_source (discard_process_cache live) = identity_source live"
  by (simp add: identity_source_def)

context source_attestation
begin

theorem an_actual_denied_reference_read_preserves_the_snapshot_and_refuses_every_cache:
  assumes ready: "reference_grants_fit registered (reference_product before) (reference_inputs before)"
    and denied: "\<not> identity_read_allowed directory read_policy authenticate verify_read token proof target request
      (identity_source (reopen_retained_product connection (reference_product before)))"
  shows "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
    authenticated connection (Service_Read token proof target request cache) supplied before =
      (before, Some (Scheduled_Endpoint (Service_Read_Result Identity_Read_Rejected)))"
proof -
  let ?live = "reopen_retained_product connection (reference_product before)"
  have reader: "read_with_revalidated_cache directory read_policy authenticate verify_read token proof target request cache ?live =
      Identity_Read_Rejected"
    using denied by (cases request)
      (simp_all add: read_with_revalidated_cache_def read_at_identity_endpoint_def
        clearing_a_process_cache_keeps_the_authoritative_identity_source Let_def)
  show ?thesis using ready reader
    by (cases before) (simp add: service_at_reference_snapshot_def schedule_at_retained_state_def schedule_service_step_def
      reader select_reference_grants_def product_round_trip_preserves_the_durable_projection Let_def)
qed

lemma the_read_gate_depends_on_the_current_identity_supplier:
  assumes active: "active_identity directory claimed proof source"
    and signature: "verify_read claimed proof target request"
    and scope: "policy claimed target request (proof_epoch proof)"
  shows "identity_read_allowed directory policy (\<lambda>_. Some claimed) verify_read token proof target request source"
    "\<not> identity_read_allowed directory policy (\<lambda>_. None) verify_read token proof target request source"
  using assms by (auto simp: identity_read_allowed_def)

lemma the_actual_origin_step_records_a_grant_refusal_without_changing_the_source:
  fixes origins outcomes source envelope payload
  defines "outcomes \<equiv> origin_outcomes origins"
    and "source \<equiv> outcome_source outcomes"
    and "envelope \<equiv> payload_envelope payload"
  assumes denied: "\<not> permitted entry actor (envelope_command envelope)"
    and exact: "result_access_bound verified actor key payload outcomes"
    and fresh: "outcome_entries outcomes key = None" "call_invocations (product_calls source) key = None"
      "call_authority_results (product_calls source) key = None"
    and ready: "call_local_status (product_calls source) = Endpoint_Up"
      "call_connection (product_calls source) = Authority_Connected"
  shows "submit_origin_call permitted verified maintainers registered entry actor key payload origins =
      origins\<lparr>origin_outcomes := store_product_result key payload Authority_Rejected source outcomes\<rparr>"
  using denied exact fresh ready
  by (simp add: submit_origin_call_def submit_authoritative_call_def submit_new_authoritative_call_def
    lock_submission_allowed_def submit_lock_entry_def store_product_result_def outcomes_def source_def envelope_def Let_def)

theorem fresh_checked_debit_with_no_current_grant_preserves_the_source_and_records_refusal:
  fixes reads authority origins outcomes source envelope payload
  defines "authority \<equiv> read_authority reads"
    and "origins \<equiv> settlement_primary authority"
    and "outcomes \<equiv> origin_outcomes origins"
    and "source \<equiv> outcome_source outcomes"
    and "envelope \<equiv> payload_envelope payload"
  assumes command: "envelope_command envelope = Client_Protocol endpoint index (Source_Intent request generation versions)"
    and missing: "(actor,entry,Ref_Debit) \<notin> reference_grants inputs endpoint"
    and exact: "result_access_bound verified actor key payload outcomes" "envelope_cut envelope = observed_product_cut authority"
    and fresh: "outcome_entries outcomes key = None" "call_invocations (product_calls source) key = None"
      "call_authority_results (product_calls source) key = None"
    and ready: "read_authority_available reads" "call_local_status (product_calls source) = Endpoint_Up"
      "call_connection (product_calls source) = Authority_Connected"
  shows "let (after, checked) = execute_at_checked_cut (reference_permitted_at inputs) verified maintainers registered verified_ack
      entry actor (observed_product_cut authority) key payload reads;
      retained = origin_outcomes (settlement_primary (read_authority after))
    in outcome_source retained = source \<and>
       outcome_entries retained key = Some \<lparr>result_payload = payload, result_outcome = Authority_Rejected\<rparr> \<and>
       checked = Forwarded_At_Checked_Cut"
proof -
  have denied: "\<not> reference_permitted_at inputs entry actor (envelope_command envelope)"
    using command missing by (simp add: reference_permitted_at_def)
  have rejected: "submit_origin_call (reference_permitted_at inputs) verified maintainers registered entry actor key payload origins =
      origins\<lparr>origin_outcomes := store_product_result key payload Authority_Rejected source outcomes\<rparr>"
    unfolding outcomes_def source_def envelope_def
    by (rule the_actual_origin_step_records_a_grant_refusal_without_changing_the_source
        [where permitted="reference_permitted_at inputs" and entry=entry and actor=actor and payload=payload and origins=origins,
         OF denied[unfolded envelope_def] exact(1)[unfolded outcomes_def]
            fresh[unfolded outcomes_def source_def] ready(2,3)[unfolded source_def outcomes_def]])
  show ?thesis using rejected exact ready(1)
    by (simp add: execute_at_checked_cut_def authority_def origins_def outcomes_def envelope_def store_product_result_def Let_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.an_actual_denied_reference_read_preserves_the_snapshot_and_refuses_every_cache
      source_attestation.the_read_gate_depends_on_the_current_identity_supplier
      source_attestation.fresh_checked_debit_with_no_current_grant_preserves_the_source_and_records_refusal})
  then () else error "Unexpected oracle in reference entry consumption"
\<close>

end
