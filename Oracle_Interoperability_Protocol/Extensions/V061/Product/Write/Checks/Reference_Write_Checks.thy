theory Reference_Write_Checks
  imports "OIP_Reference_Write_AuthorityV4.Reference_Write_Authority"
    "OIP_Product.Promotion_Financial"
    "OIP_Write_Canary_Removal.Write_Canary_Removal"
    "OIP_Write_Canary_DurableV6.Write_Canary_DurableV6"
    "HOL-Library.Code_Target_Nat"
begin

definition write_fixture_payload :: product_call_payload where
  "write_fixture_payload = \<lparr>payload_envelope = lock_example_envelope write_canary_command,
    payload_credential = Some lock_example_token, payload_origin_epoch = 9\<rparr>"

definition write_fixture_authority :: "lock_context \<Rightarrow> reference_authority_snapshot" where
  "write_fixture_authority ctxt =
    (let world = write_canary_world ctxt;
         retained = initial_promotable_product sample_balances (sample_metadata ACTIVE) lock_example_contexts
           (product_durable world) 99 100
     in \<lparr>reference_product = retained\<lparr>retained_source := capture_retained_source world\<rparr>,
       reference_inputs = write_canary_grants\<rparr>)"

definition write_fixture_store :: "lock_context \<Rightarrow> unit reference_write_store" where
  "write_fixture_store ctxt =
    (let authority = write_fixture_authority ctxt in
      \<lparr>write_product_image = \<lparr>image_authority = authority,
         image_read_history = initialize_reference_history 9 (capture_reference_view authority),
         image_transport = (\<lambda>_. None), image_ordered_control = \<lparr>control_revision = 0, control_head = None,
           control_writer = 0, control_revoked = {}, control_cancelled = {},
           control_decisions = (\<lambda>_. None), control_latest = (\<lambda>_. None)\<rparr>\<rparr>,
        write_effect_positions = (\<lambda>_. None), write_original_cores = (\<lambda>_. None)\<rparr>)"

lemma write_fixture_projection:
  "write_authority (write_fixture_store ctxt) = write_fixture_authority ctxt"
  "reference_inputs (write_authority (write_fixture_store ctxt)) = write_canary_grants"
  "write_history (write_fixture_store ctxt) = initialize_reference_history 9 (capture_reference_view (write_fixture_authority ctxt))"
  "write_ledger_cut (write_fixture_store ctxt) = \<lparr>cut_authority_epoch = 9, cut_revision = 0\<rparr>"
  "reference_history_prefixes (write_history (write_fixture_store ctxt)) \<noteq> []"
  by (simp_all add: write_fixture_store_def write_fixture_authority_def initialize_reference_history_def
      reference_observed_cut_def Let_def)

lemma write_fixture_source:
  "write_source Authority_Connected (write_fixture_store ctxt) = write_canary_world ctxt"
  by (simp add: reference_lock_source_def recovery_projection_supplies_the_exact_source write_fixture_projection(1)
      write_fixture_authority_def write_canary_world_def lock_example_world_def capture_retained_source_def
      reopen_retained_source_def initial_call_machine_def Let_def)

lemma write_fixture_is_ready:
  "reference_write_ready {0,2} 7 (7,1) write_fixture_payload (write_canary_world ctxt) (write_fixture_store ctxt)"
proof -
  have owner: "product_owners (product_durable (write_canary_world ctxt)) 17 = Some 3"
    by (simp add: write_canary_world_def lock_example_world_def)
  have state: "authoritative_reservation_state (write_canary_world ctxt) = machine_state lock_example_held"
    by (simp add: authoritative_reservation_state_def write_canary_world_def lock_example_world_def
      initial_call_machine_def write_canary_core_def lock_example_core_def)
  have assets: "reference_write_asset_ready {0,2} (write_canary_world ctxt) write_canary_command"
    by (simp add: write_canary_command_def sample_request_def sample_binding_def example_binding_def
        owner state write_canary_initial_version Let_def)
  have command: "envelope_command (lock_example_envelope write_canary_command) = write_canary_command"
    by (simp add: lock_example_envelope_def)
  show ?thesis using assets write_canary_current_entry(1,2)[of ctxt] write_canary_current_entry(3)
    by (simp add: reference_write_ready_def product_new_call_def write_fixture_payload_def command
      write_fixture_projection(2,4) Let_def)
qed

abbreviation write_fixture_dispatch where
  "write_fixture_dispatch ctxt \<equiv> sample.reference_write_dispatch (write_canary_world ctxt) (7,1)
    (payload_envelope write_fixture_payload)"

lemma write_fixture_dispatch_calls:
  "product_calls (write_fixture_dispatch ctxt) = product_calls (write_canary_submit ctxt)"
  unfolding write_canary_dispatches_the_existing_product_command
  by (simp add: sample.reference_write_dispatch_def sample.product_apply_public_def
      write_fixture_payload_def lock_example_envelope_def write_canary_world_def Let_def)

abbreviation run_write_fixture where
  "run_write_fixture ctxt \<equiv> sample.reference_write_fresh {0,2} Authority_Connected 7 (7,1)
    write_fixture_payload (write_fixture_store ctxt)"

lemma write_fixture_runs_the_checked_effect:
  "run_write_fixture ctxt =
    (if snd (write_canary_effect ctxt) = Data_Updated then
       record_reference_write (7,1) write_fixture_payload (Authority_Reply (Protocol_Response Data_Updated))
         (Some (write_fixture_dispatch ctxt)) (write_fixture_store ctxt)
     else record_reference_write (7,1) write_fixture_payload Authority_Rejected (None :: product_world option) (write_fixture_store ctxt))"
proof -
  have connected: "call_connection (product_calls (write_canary_world ctxt)) = Authority_Connected"
    by (simp add: write_canary_world_def initial_call_machine_def)
  have current: "envelope_cut (payload_envelope write_fixture_payload) = write_ledger_cut (write_fixture_store ctxt)"
    by (simp add: write_fixture_payload_def lock_example_envelope_def write_fixture_projection(4))
  have ready: "reference_write_ready {0,2} 7 (7,1) write_fixture_payload (write_canary_world ctxt) (write_fixture_store ctxt)"
    by (rule write_fixture_is_ready)
  let ?raw = "call_authority_results (product_calls (write_fixture_dispatch ctxt)) (7,1)"
  let ?reply = "map_option (\<lambda>(_, reply, _). reply) ?raw"
  let ?success = "record_reference_write (7,1) write_fixture_payload (Authority_Reply (Protocol_Response Data_Updated))
    (Some (write_fixture_dispatch ctxt)) (write_fixture_store ctxt)"
  let ?refusal = "record_reference_write (7,1) write_fixture_payload Authority_Rejected
    (None :: product_world option) (write_fixture_store ctxt)"
  have step: "run_write_fixture ctxt = (if ?reply = Some (Protocol_Response Data_Updated) then ?success else ?refusal)"
    by (simp only: sample.reference_write_fresh_def Let_def write_fixture_source connected current ready simp_thms if_True if_False)
  have row: "?raw = Some (write_canary_command, Protocol_Response (snd (write_canary_effect ctxt)), 0)"
    unfolding write_fixture_dispatch_calls by (rule write_canary_effect_projection(1))
  have reply: "?reply = Some (Protocol_Response (snd (write_canary_effect ctxt)))"
    by (simp only: row map_option_case option.case case_prod_conv)
  show ?thesis by (simp only: step reply option.inject finality_reply.inject)
qed

definition observe_write_fixture where
  "observe_write_fixture result =
    (let snapshot = last (reference_history_prefixes (write_history (fst result)));
         financial = snapshot_financial snapshot
     in (Option.bind (snd result) reference_write_code, asset_value financial 17,
          asset_version financial 17, cut_revision (write_ledger_cut (fst result))))"

lemma a_successful_write_fixture_computes_the_effect_observation:
  assumes success: "snd (write_canary_effect ctxt) = Data_Updated"
  shows "observe_write_fixture (run_write_fixture ctxt) = (Some (20,Some 0),9,1,1)"
proof -
  let ?start = "write_fixture_store ctxt"
  let ?outcome = "Authority_Reply (Protocol_Response Data_Updated)"
  let ?record = "record_reference_write (7,1) write_fixture_payload ?outcome (Some (write_fixture_dispatch ctxt)) ?start"
  have ran: "run_write_fixture ctxt = ?record"
    using success by (simp only: write_fixture_runs_the_checked_effect simp_thms(6) if_True)
  have current: "cut_revision (write_ledger_cut ?start) = 0" by (simp add: write_fixture_projection(4))
  have history: "reference_history_prefixes (write_history ?start) \<noteq> []" by (rule write_fixture_projection(5))
  note effect = a_write_effect_and_observation_share_the_commit_position[
    where call_id="(7,1)" and payload=write_fixture_payload and outcome="?outcome" and ?next="write_fixture_dispatch ctxt",
    OF history refl]
  have reply: "snd ?record = Some (?outcome,Some 0)" by (simp add: record_reference_write_def current Let_def)
  note projection = write_canary_success_projects[OF success]
  have financial: "snapshot_financial (last (reference_history_prefixes (write_history (fst ?record)))) =
    authoritative_reservation_state (write_canary_submit ctxt)"
    unfolding effect(4) write_fixture_dispatch_calls capture_snapshot_def authoritative_reservation_state_def by simp
  show ?thesis
    unfolding ran observe_write_fixture_def Let_def
    unfolding reply financial projection(2,3) write_canary_initial_version effect(2) current
    by simp
qed

lemma a_refused_write_fixture_keeps_its_initial_observation:
  "observe_write_fixture (run_write_fixture write_canary_denied_context) = (Some (1,None),0,0,0)"
proof -
  let ?start = "write_fixture_store write_canary_denied_context"
  let ?record = "record_reference_write (7,1) write_fixture_payload Authority_Rejected (None :: product_world option) ?start"
  have denied: "snd (write_canary_effect write_canary_denied_context) = Request_Rejected"
    using the_same_write_without_the_value_permission_has_no_effect(1)
    by (simp only: write_canary_effect_projection(1) option.inject prod.inject finality_reply.inject simp_thms)
  have ran: "run_write_fixture write_canary_denied_context = ?record"
    by (simp only: write_fixture_runs_the_checked_effect denied reservation_reply.distinct if_False)
  have snapshot: "snapshot_financial (last (reference_history_prefixes (write_history ?start))) = machine_state lock_example_held"
    by (simp add: write_fixture_projection(3) initialize_reference_history_def write_fixture_authority_def
        capture_reference_view_def capture_snapshot_def capture_retained_source_def write_canary_world_def
        initial_call_machine_def write_canary_core_def lock_example_core_def Let_def)
  have initial: "asset_value (machine_state lock_example_held) 17 = 0" by (simp add: lock_example_public_defs)
  show ?thesis
    unfolding ran observe_write_fixture_def Let_def
    unfolding recording_a_write_without_effect_keeps_the_exact_authority_view(1,3) write_fixture_projection(4)
      snapshot initial write_canary_initial_version
    by simp
qed

definition retry_write_fixture where
  "retry_write_fixture =
    (let before = fst (run_write_fixture (sample_source_context ACTIVE));
         verified = (\<lambda>actor call_id payload. actor = 7 \<and> call_id = (7,1) \<and> payload = write_fixture_payload)
     in (before,sample.collect_reference_write verified Authority_Connected 7 (7,1) write_fixture_payload before))"

lemma the_reopened_write_fixture_reuses_the_committed_observation:
  "retry_write_fixture = run_write_fixture (sample_source_context ACTIVE)"
proof -
  let ?ctxt = "sample_source_context ACTIVE"
  let ?outcome = "Authority_Reply (Protocol_Response Data_Updated)"
  let ?after = "fst (run_write_fixture ?ctxt)"
  let ?retained = "reference_product (write_authority ?after)"
  let ?live = "reopen_retained_product Authority_Connected ?retained"
  let ?source = "outcome_source (current_product_outcomes ?live)"
  let ?verified = "\<lambda>(actor::product_principal) (call_id::client_call_id) payload.
    actor = 7 \<and> call_id = (7,1) \<and> payload = write_fixture_payload"
  have ran: "run_write_fixture ?ctxt = record_reference_write (7,1) write_fixture_payload ?outcome
      (Some (write_fixture_dispatch ?ctxt)) (write_fixture_store ?ctxt)"
    by (simp only: write_fixture_runs_the_checked_effect write_canary_fixture_success simp_thms(6) if_True)
  have previous: "snd (run_write_fixture ?ctxt) = Some (?outcome,Some 0)"
    unfolding ran by (simp add: record_reference_write_def write_fixture_projection(4) Let_def)
  have position: "write_effect_positions ?after (7,1) = Some 0"
    unfolding ran by (simp add: record_reference_write_def write_fixture_projection(4) Let_def)
  have saved: "retained_outcomes ?retained (7,1) =
    Some \<lparr>result_payload = write_fixture_payload, result_outcome = ?outcome\<rparr>"
    by (simp only: ran a_write_record_keeps_its_exact_result)
  have captured: "retained_source ?retained = capture_retained_source (write_fixture_dispatch ?ctxt)"
    unfolding ran by (simp add: record_reference_write_def record_reference_product_image_def Let_def)
  have restored: "product_durable ?source = retained_authority (retained_source ?retained)"
    by (simp add: current_product_outcomes_def legal_underlying_outcomes_def reopen_retained_product_def
        initial_product_reads_def reopen_retained_source_def Let_def)
  have durable: "product_durable ?source = product_durable (write_fixture_dispatch ?ctxt)"
    unfolding restored captured by (simp add: capture_retained_source_def Let_def)
  have allowed: "result_access_bound ?verified 7 (7,1) write_fixture_payload (current_product_outcomes ?live)"
    unfolding result_access_bound_def product_identity_bound_def current_product_cut_def durable
    by (simp add: sample.reference_write_dispatch_def sample.product_apply_public_def write_canary_world_def
      lock_example_world_def write_fixture_payload_def lock_example_envelope_def write_canary_command_def sample_request_def Let_def)
  let ?entry = "\<lparr>result_payload = write_fixture_payload, result_outcome = ?outcome\<rparr>"
  have entry: "outcome_entries (current_product_outcomes ?live) (7,1) = Some ?entry"
    by (simp only: reopening_the_write_authority_restores_the_exact_result_table saved)
  have up: "call_local_status (product_calls (outcome_source (current_product_outcomes ?live))) = Endpoint_Up"
    by (rule reopened_write_outcomes_are_available_to_the_endpoint)
  have ready: "result_completion_ready ?entry (current_product_outcomes ?live)"
    by (simp add: result_completion_ready_def write_fixture_payload_def lock_example_envelope_def
        write_canary_command_def Let_def)
  have observed: "observe_collection ?verified 7 (7,1) write_fixture_payload (current_product_outcomes ?live) = Collected ?outcome"
    using allowed entry up ready by (simp add: observe_collection_def)
  have collected: "sample.collect_reference_write ?verified Authority_Connected 7 (7,1) write_fixture_payload ?after =
      snd (run_write_fixture ?ctxt)"
    unfolding sample.collect_reference_write_def observed position previous by simp
  show ?thesis by (simp only: retry_write_fixture_def Let_def collected prod.collapse)
qed

lemma the_value_permission_removal_fixture_computes_the_effect_observation:
  "observe_write_fixture (run_write_fixture (write_canary_denied_context\<lparr>lock_write_permissions := UNIV\<rparr>)) =
    (Some (20,Some 0),9,1,1)"
proof (rule a_successful_write_fixture_computes_the_effect_observation)
  show "snd (write_canary_effect (write_canary_denied_context\<lparr>lock_write_permissions := UNIV\<rparr>)) = Data_Updated"
    using removing_that_test_reaches_the_same_actual_write(1)
    by (simp only: write_canary_effect_projection(1) option.inject prod.inject finality_reply.inject simp_thms)
qed

definition reference_write_observation_table :: "(nat \<times> (nat \<times> nat option) option \<times> nat \<times> nat \<times> nat) list" where
  "reference_write_observation_table = [
     (0,observe_write_fixture (run_write_fixture (sample_source_context ACTIVE))),
     (1,observe_write_fixture (run_write_fixture write_canary_denied_context)),
     (2,observe_write_fixture retry_write_fixture),
     (3,observe_write_fixture (run_write_fixture (write_canary_denied_context\<lparr>lock_write_permissions := UNIV\<rparr>)))]"

declare [[code drop: reference_write_observation_table]]

lemma reference_write_observation_table_exact [code]:
  "reference_write_observation_table = [
    (0, (Some (20,Some 0),9,1,1)),
    (1, (Some (1,None),0,0,0)),
    (2, (Some (20,Some 0),9,1,1)),
    (3, (Some (20,Some 0),9,1,1))]"
  by (simp only: reference_write_observation_table_def
    a_successful_write_fixture_computes_the_effect_observation[OF write_canary_fixture_success]
    a_refused_write_fixture_keeps_its_initial_observation the_reopened_write_fixture_reuses_the_committed_observation
    the_value_permission_removal_fixture_computes_the_effect_observation)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms reference_write_is_the_only_admission_change
      every_other_decoded_operation_keeps_its_admission_and_exact_bytes
      the_new_profile_accepts_the_existing_write_layout a_selected_write_consumes_the_exact_typed_operands
      source_attestation.a_fresh_reference_write_result_passes_current_caller_authorization
      a_ready_write_has_the_current_route_grant_and_exact_lock_credential
      source_attestation.a_fresh_write_commits_when_the_current_guards_pass
      source_attestation.a_fresh_write_commit_binds_the_current_guard_value_and_position
      source_attestation.a_current_write_reservation_carries_the_exact_generation_deadline_and_footprint
      source_attestation.a_fresh_write_without_a_commit_keeps_value_version_and_history
      source_attestation.an_obsolete_fresh_write_records_busy_without_advancing_history
      source_attestation.a_reopened_exact_write_returns_its_retained_result_and_position
      source_attestation.an_existing_write_id_with_changed_payload_cannot_collect_or_execute
      source_attestation.an_existing_write_call_requires_the_same_admitted_core
      source_attestation.a_new_selected_write_retains_the_admitted_core_with_its_result
      source_attestation.authorized_exact_write_retry_reads_before_the_fresh_cut reference_write_observation_table_exact})
  then () else error "Unexpected oracle in the reference Write proofs"
\<close>

export_code reference_write_observation_table
  in SML module_name Reference_Write_Observations file_prefix "reference_write_observations"

end
