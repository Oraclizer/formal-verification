theory Reference_Trace_Read_Execution
  imports Reference_Trace_Consumers "OIP_Reference_Profile.Reference_Lock_Consumption"
begin

context reference_trace_consumer
begin

theorem a_current_read_of_the_actual_reference_trace_uses_the_same_cut_as_checked_execution:
  fixes before live reads authority prefix initial connection
  defines "before \<equiv> run_reference_word execute prefix initial"
    and "live \<equiv> reopen_retained_product connection (reference_product before)"
    and "reads \<equiv> regulated_read_world live"
    and "authority \<equiv> read_authority reads"
  assumes response: "serve connection (Service_Read token proof target (Current_Data query expected) cache) supplied before =
      (after, Some (Scheduled_Endpoint (Service_Read_Result (Authorized_Data (Current_Cut_Value observed value)))))"
    and checked: "execute_at_checked_cut (reference_permitted_at (reference_inputs before)) verified maintainers registered verified_ack
       entry actor observed call_id payload reads = (written,Forwarded_At_Checked_Cut)"
  shows "reference_product after = reference_product before"
    "observed = observed_product_cut authority"
    "value = stored_query query (capture_snapshot (authoritative_read_core authority))"
    "envelope_cut (payload_envelope payload) = observed"
    "read_authority written = exact_step (reference_permitted_at (reference_inputs before)) verified maintainers registered verified_ack
       (Exact_Submit entry actor call_id payload) authority"
proof -
  note actual = a_reference_step_uses_the_actual_service_with_the_retained_grants
    [OF response[unfolded actual_execute reference_service_input.select_convs]]
  have producer: "read_with_revalidated_cache directory read_policy authenticate verify_read token proof target
       (Current_Data query expected) cache live = Authorized_Data (Current_Cut_Value observed value)"
    using actual by (simp add: schedule_at_retained_state_def schedule_service_step_def live_def Let_def)
  show "reference_product after = reference_product before"
    using actual by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def
      product_round_trip_preserves_the_durable_projection)
  show "observed = observed_product_cut authority"
    "value = stored_query query (capture_snapshot (authoritative_read_core authority))"
    using a_current_reply_from_the_actual_wire_ready_endpoint_has_its_exact_cut[OF producer]
    by (simp_all add: reads_def authority_def)
  show "envelope_cut (payload_envelope payload) = observed"
    "read_authority written = exact_step (reference_permitted_at (reference_inputs before)) verified maintainers registered verified_ack
       (Exact_Submit entry actor call_id payload) authority"
    using forwarded_execution_consumes_the_cut_it_checked[OF checked] by (simp_all add: authority_def)
qed

theorem a_historical_read_of_the_actual_reference_trace_uses_only_the_named_authority_prefix:
  fixes before live reads prefix initial connection
  defines "before \<equiv> run_reference_word execute prefix initial"
    and "live \<equiv> reopen_retained_product connection (reference_product before)"
    and "reads \<equiv> regulated_read_world live"
  assumes response: "serve connection (Service_Read token proof target (Historical_Data query requested) cache) supplied before =
    (after,Some (Scheduled_Endpoint (Service_Read_Result (Authorized_Data (Historical_Prefix_Value revision value)))))"
  shows "reference_product after = reference_product before"
    "revision = requested \<and> (\<exists>snapshot. authority_prefix_snapshot requested (read_authority reads) = Some snapshot \<and>
       value = stored_query query snapshot)"
proof -
  note actual = a_reference_step_uses_the_actual_service_with_the_retained_grants
    [OF response[unfolded actual_execute reference_service_input.select_convs]]
  show "reference_product after = reference_product before"
    using actual by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def
      product_round_trip_preserves_the_durable_projection)
  have producer: "read_at_identity_endpoint directory read_policy authenticate verify_read token proof target
       (Historical_Data query requested) (discard_process_cache live) = Authorized_Data (Historical_Prefix_Value revision value)"
    using actual by (simp add: schedule_at_retained_state_def schedule_service_step_def live_def read_with_revalidated_cache_def Let_def)
  have available_identity: "\<exists>identity. authenticate token = Some identity"
    using producer by (cases "authenticate token") (simp_all add: read_at_identity_endpoint_def Let_def split: if_splits)
  then obtain identity where found: "authenticate token = Some identity" by blast
  have named: "read_historical_product (\<lambda>_ _ _. True) (identity_principal identity) (proof_session proof)
       query requested (regulated_read_world (discard_process_cache live)) = Historical_Prefix_Value revision value"
    using producer found by (auto simp: read_at_identity_endpoint_def Let_def split: if_splits)
  show "revision = requested \<and> (\<exists>snapshot. authority_prefix_snapshot requested (read_authority reads) = Some snapshot \<and>
       value = stored_query query snapshot)"
    using successful_historical_product_read_is_the_named_prefix[OF named]
    by (simp add: reads_def)
qed

theorem every_route_at_an_actual_reference_prefix_uses_one_final_caller_gate:
  "serve connection (Service_Execute first token proof target action authorization) supplied (run_reference_word execute prefix initial) =
   serve connection (Service_Execute second token proof target action authorization) supplied (run_reference_word execute prefix initial)"
proof -
  have consumer: "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection (Service_Execute first token proof target action authorization) snapshot =
    schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection (Service_Execute second token proof target action authorization) snapshot" for permitted snapshot
    by (simp add: schedule_at_retained_state_def schedule_service_step_def
      durable_execution_uses_the_same_final_gate_on_every_route[where first=first and second=second] Let_def)
  let ?before = "run_reference_word execute prefix initial"
  let ?schedule = "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted (reference_permitted_at (reference_inputs ?before))
    verified maintainers registered verified_ack connection"
  have equal: "?schedule (Service_Execute first token proof target action authorization) (reference_product ?before) =
       ?schedule (Service_Execute second token proof target action authorization) (reference_product ?before)"
    by (rule consumer)
  have selection: "select_reference_grants registered authenticated (Service_Execute first token proof target action authorization)
        supplied ?before records = select_reference_grants registered authenticated
        (Service_Execute second token proof target action authorization) supplied ?before records" for records
    by (cases supplied) (simp_all add: select_reference_grants_def)
  have service: "serve connection item supplied ?before =
       service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
          legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
          authenticated connection item supplied ?before" for item
    by (simp only: actual_execute reference_service_input.select_convs)
  let ?selected = "fst (?schedule (Service_Execute second token proof target action authorization) (reference_product ?before))"
  note selected = selection[of "?selected"]
  show ?thesis using equal selected
    by (simp only: service service_at_reference_snapshot_def Let_def)
qed

lemma a_checked_submission_without_the_current_lock_credential_keeps_the_actual_source:
  assumes denied: "\<not> lock_envelope_admitted actor (payload_envelope payload) (payload_credential payload)
       (outcome_source (origin_outcomes origins))"
  shows "outcome_source (origin_outcomes (submit_origin_call permitted verified maintainers registered entry actor call_id payload origins)) =
    outcome_source (origin_outcomes origins)"
proof -
  let ?envelope = "payload_envelope payload"
  let ?before = "origin_outcomes origins"
  let ?source = "outcome_source ?before"
  let ?permitted = "\<lambda>route who command. permitted route who command \<and>
      origin_command_allowed origins ?envelope (payload_origin_epoch payload) command"
  have gate: "lock_product_step ?permitted (\<lambda>_ _ _ _. True) maintainers registered
      (Lock_Submit entry actor call_id ?envelope (payload_credential payload)) ?source = ?source"
    using denied by (simp add: submit_lock_entry_def lock_submission_allowed_def)
  have same: "outcome_source (submit_authoritative_call ?permitted verified maintainers registered entry actor call_id payload ?before) = ?source"
    by (auto simp del: lock_product_step.simps simp add: submit_authoritative_call_def submit_new_authoritative_call_def
        gate store_product_result_def Let_def split: option.splits prod.splits if_splits)
  show ?thesis by (simp add: submit_origin_call_def Let_def origin_metadata_retention_keeps_the_authority_result same
       split: option.splits prod.splits if_splits)
qed

theorem an_earlier_epoch_or_replaced_generation_cannot_change_the_checked_lock_source_after_a_reference_prefix:
  fixes before live reads authority origins source
    prefix initial connection
  defines "before \<equiv> run_reference_word execute prefix initial"
    and "live \<equiv> reopen_retained_product connection (reference_product before)"
    and "reads \<equiv> regulated_read_world live"
    and "authority \<equiv> read_authority reads"
    and "origins \<equiv> settlement_primary authority"
    and "source \<equiv> outcome_source (origin_outcomes origins)"
  assumes action: "command_lock_request (envelope_command (payload_envelope payload)) = Some (request,generation)"
    and evidence: "payload_credential payload = Some credential"
    and old: "credential_epoch credential < cut_authority_epoch (current_product_cut source) \<or>
       (\<exists>replacement. authoritative_lock_token source (token_asset (credential_token credential)) = Some replacement \<and>
       token_generation (credential_token credential) < token_generation replacement)"
  shows "let written = fst (execute_at_checked_cut (reference_permitted_at (reference_inputs before)) verified maintainers registered verified_ack
       entry actor expected call_id payload reads)
    in outcome_source (origin_outcomes (settlement_primary (read_authority written))) = source"
proof -
  have unmatched: "\<not> lock_credential_matches actor credential request generation source"
    using old by (auto simp: lock_credential_matches_def product_lock_admitted_def authoritative_lock_view_def
      current_product_cut_def current_lock_token_def Let_def)
  have denied: "\<not> lock_envelope_admitted actor (payload_envelope payload) (payload_credential payload) source"
    using unmatched action evidence by (simp add: lock_envelope_admitted_def)
  have stutter: "outcome_source (origin_outcomes (submit_origin_call (reference_permitted_at (reference_inputs before))
      verified maintainers registered entry actor call_id payload origins)) = source"
    unfolding source_def by (rule a_checked_submission_without_the_current_lock_credential_keeps_the_actual_source[OF denied[unfolded source_def]])
  show ?thesis using stutter
    by (simp add: execute_at_checked_cut_def source_def origins_def authority_def Let_def split: if_splits)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms reference_trace_consumer.a_current_read_of_the_actual_reference_trace_uses_the_same_cut_as_checked_execution
    reference_trace_consumer.a_historical_read_of_the_actual_reference_trace_uses_only_the_named_authority_prefix
    reference_trace_consumer.every_route_at_an_actual_reference_prefix_uses_one_final_caller_gate
    reference_trace_consumer.an_earlier_epoch_or_replaced_generation_cannot_change_the_checked_lock_source_after_a_reference_prefix})
  then () else error "Unexpected oracle in reference trace read and execution"
\<close>

end
