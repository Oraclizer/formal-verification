theory Replay_Outcome_Continuation
  imports "OIP_V062_P13_Replay_Stored_Outcome_Repair.Replay_Stored_Outcome"
    "OIP_Product_Base.Outcome_Gates"
begin

text \<open>The second call consumes the credential derived from the reservation
created by the first call. Its reply and new source come from the ordinary
authoritative submit. Fresh completion is separate from a receipt lookup.\<close>

definition prd_credential :: "product_lock_credential option" where
  "prd_credential = map_option
    (\<lambda>token. \<lparr>credential_token = token,
      credential_epoch = cut_authority_epoch (current_product_cut hf_reserved),
      credential_origin = (0,17)\<rparr>)
    (authoritative_lock_token hf_reserved 17)"

definition prd_payload :: product_call_payload where
  "prd_payload = \<lparr>payload_envelope = hf_envelope 2 2 hf_dispatch hf_reserved,
    payload_credential = prd_credential,
    payload_origin_epoch = cut_authority_epoch (current_product_cut hf_reserved)\<rparr>"

definition prd_submitted :: outcome_world where
  "prd_submitted = sample.submit_authoritative_call (reference_permitted_at (pro_inputs 9)) pro_verified
    ({7}::nat set) {0,2} Normal_Lock_Entry 7 ((7,2)::client_call_id) prd_payload pro_completed"

definition prd_outcome :: product_outcome where
  "prd_outcome = normalized_authority_reply
    (snd (sample.execute_finality_client hf_dispatch (call_authority_state (product_calls hf_reserved))))"

definition prd_entry :: product_result_entry where
  "prd_entry = \<lparr>result_payload = prd_payload, result_outcome = prd_outcome\<rparr>"

definition prd_completed :: outcome_world where
  "prd_completed = fst (complete_authoritative_result pro_verified 7 ((7,2)::client_call_id) prd_payload prd_submitted)"

lemma prd_reserved_finality_core:
  "call_authority_state (product_calls hf_reserved) =
    finality_sample_initial\<lparr>core_parent := lock_example_held, core_epoch := 1\<rparr>"
  unfolding prp_actual_reserved_call_machine sample.finality_calls.initial_dispatch_projection(1)
  by (simp add: hf_reserve_def sample.first_protocol_call_uses_the_current_core
      sample.finality_step_def sample.invoke_protocol_def finality_sample_initial_def
      initial_finality_core_def current_lock_view_def sample_source_context_def sample_context_def
      lock_example_held_def empty_vector_represents_zero_versions sample_initial_def
      lift_protocol_result_def Let_def)

lemma prd_reserved_state_comes_from_the_public_hold:
  "authoritative_reservation_state hf_reserved = machine_state lock_example_held"
  unfolding authoritative_reservation_state_def prd_reserved_finality_core by simp

lemma prd_reserved_token_is_current:
  "authoritative_lock_token hf_reserved 17 = Some (credential_token lock_example_token)"
proof -
  have selected:
    "map_option (\<lambda>r. \<lparr>token_asset = 17, token_owner = reservation_worker r,
      token_generation = reservation_generation r\<rparr>)
      (reservation_at (machine_state lock_example_held) (0,17)) = Some (credential_token lock_example_token)"
    using lock_example_current_reservation(2,3)
    by (cases "reservation_at (machine_state lock_example_held) (0,17)") (simp_all add: lock_example_token_def)
  show ?thesis
    unfolding authoritative_lock_token_def Let_def prd_reserved_state_comes_from_the_public_hold
      lock_example_current_reservation(1)
    by (simp only: option.case selected)
qed

lemma prd_dispatch_credential_is_the_actual_fence:
  "prd_credential = Some lock_example_token"
  unfolding prd_credential_def prd_reserved_token_is_current prp_initial_reserved_dispatched_metadata(2)
  by (simp add: lock_example_token_def)

lemma prd_dispatch_passes_the_real_credential_gate:
  "lock_envelope_admitted 7 (payload_envelope prd_payload) (payload_credential prd_payload) hf_reserved"
proof -
  have token_fields:
    "token_asset (credential_token lock_example_token) = 17"
    "token_owner (credential_token lock_example_token) = 7"
    "token_generation (credential_token lock_example_token) = 0"
    "credential_epoch lock_example_token = 9"
    "credential_origin lock_example_token = (0,17)"
    by (simp_all add: lock_example_token_def)
  have current: "current_lock_token (authoritative_lock_view hf_reserved) (credential_token lock_example_token)"
    unfolding current_lock_token_def authoritative_lock_view_def token_fields(1)
    by (simp add: prd_reserved_token_is_current)
  have epoch: "cut_authority_epoch (current_product_cut (authoritative_lock_view hf_reserved)) = 9"
    using prp_initial_reserved_dispatched_metadata(2)
    by (simp add: authoritative_lock_view_def current_product_cut_def)
  show ?thesis
    unfolding prd_payload_def product_call_payload.select_convs prd_dispatch_credential_is_the_actual_fence
    by (simp add: lock_envelope_admitted_def hf_envelope_def hf_dispatch_def envelope_matches_request_def
        envelope_matches_binding_def lock_credential_matches_def product_lock_admitted_def
        prd_reserved_state_comes_from_the_public_hold lock_example_current_reservation(1)
        token_fields current epoch prp_initial_reserved_dispatched_metadata(2)
        sample_request_def sample_binding_def example_binding_def Let_def)
qed

lemma prd_dispatch_is_registered_and_permitted:
  "registered_lock_envelope {0,2} (payload_envelope prd_payload)"
  "reference_permitted_at (pro_inputs 9) Normal_Lock_Entry 7 (envelope_command (payload_envelope prd_payload))"
  by (simp_all add: registered_lock_envelope_def reference_permitted_at_def pro_inputs_def pro_permissions_def
      prd_payload_def hf_envelope_def hf_dispatch_def)

lemma prd_dispatch_uses_the_actual_lock_entry:
  "sample.lock_product_step (reference_permitted_at (pro_inputs 9)) (\<lambda>_ _ _ _. True)
    ({7}::nat set) {0,2}
    (Lock_Submit Normal_Lock_Entry 7 ((7,2)::client_call_id) (payload_envelope prd_payload)
      (payload_credential prd_payload)) (outcome_source pro_completed) = hf_dispatched"
proof -
  let ?permit = "reference_permitted_at (pro_inputs 9)"
  let ?id = "((7,2)::client_call_id)"
  let ?entry = "sample.submit_lock_entry ?permit (\<lambda>_ _ _ _. True)
    Normal_Lock_Entry 7 ?id (payload_envelope prd_payload) (payload_credential prd_payload) hf_reserved"
  let ?submit = "sample.product_submit (\<lambda>_ _ _. True) 7 ?id (payload_envelope prd_payload) hf_reserved"
  have entered: "?entry = ?submit"
    by (rule sample.authorized_current_entry_uses_actual_submission)
      (rule prd_dispatch_is_registered_and_permitted(2), rule TrueI, rule prd_dispatch_passes_the_real_credential_gate)
  have produced:
    "sample.lock_product_step ?permit (\<lambda>_ _ _ _. True) ({7}::nat set) {0,2}
      (Lock_Submit Normal_Lock_Entry 7 ?id (payload_envelope prd_payload)
        (payload_credential prd_payload)) hf_reserved = ?submit"
    by (simp only: sample.lock_product_step.simps prd_dispatch_is_registered_and_permitted(1) if_True entered; rule refl)
  have folded: "?submit = hf_dispatched"
    by (simp only: hf_dispatched_def hf_submit_def prd_payload_def product_call_payload.select_convs; rule refl)
  show ?thesis
    unfolding pro_completed_retains_the_produced_source_and_entry(1)
    by (rule trans[OF produced folded])
qed

lemma prd_second_call_starts_with_fresh_connected_fields:
  "call_invocations (product_calls hf_reserved) (7,2) = None"
  "call_authority_results (product_calls hf_reserved) (7,2) = None"
  "call_connection (product_calls hf_reserved) = Authority_Connected"
  "call_local_status (product_calls hf_reserved) = Endpoint_Up"
proof -
  have invocations: "call_invocations (product_calls hf_reserved) =
    (\<lambda>_. None)((7,1) := Some (hf_reserve,0))"
    unfolding prp_actual_reserved_call_machine
    by (rule sample.finality_calls.initial_dispatch_projection(3))
  have results: "call_authority_results (product_calls hf_reserved) =
    (\<lambda>_. None)((7,1) := Some (hf_reserve,snd (sample.execute_finality_client hf_reserve finality_sample_initial),0))"
    unfolding prp_actual_reserved_call_machine
    by (rule sample.finality_calls.initial_dispatch_projection(2))
  show "call_invocations (product_calls hf_reserved) (7,2) = None"
    unfolding invocations by (simp add: numeral_2_eq_2)
  show "call_authority_results (product_calls hf_reserved) (7,2) = None"
    unfolding results by (simp add: numeral_2_eq_2)
  show "call_connection (product_calls hf_reserved) = Authority_Connected"
    unfolding prp_actual_reserved_call_machine
    by (rule sample.finality_calls.initial_dispatch_projection(7))
  show "call_local_status (product_calls hf_reserved) = Endpoint_Up"
    by (rule pro_reserved_endpoint_is_up)
qed

abbreviation prd_begun_second_call :: product_call_machine where
  "prd_begun_second_call \<equiv>
    sample.finality_calls.begin_client_call (7,2) hf_dispatch (product_calls hf_reserved)"

lemma prd_begun_fields:
  "call_authority_results prd_begun_second_call (7,2) = None"
  "call_authority_state prd_begun_second_call = call_authority_state (product_calls hf_reserved)"
  "call_authority_log prd_begun_second_call = call_authority_log (product_calls hf_reserved)"
  "call_connection prd_begun_second_call = Authority_Connected"
  "call_local_status prd_begun_second_call = Endpoint_Up"
  "map_option fst (call_invocations prd_begun_second_call (7,2)) = Some hf_dispatch"
  unfolding sample.finality_calls.begin_client_call_def prd_second_call_starts_with_fresh_connected_fields(1)
  by (simp_all add: prd_second_call_starts_with_fresh_connected_fields(2,3,4))

lemma prd_dispatch_reaches_the_actual_authority_step:
  "product_calls hf_dispatched =
    sample.finality_calls.execute_authority_once (7,2) hf_dispatch prd_begun_second_call"
  unfolding prp_actual_dispatched_call_machine
  by (simp only: sample.finality_calls.run_calls.simps sample.finality_calls.call_step.simps
      sample.finality_calls.dispatch_client_call_def prd_begun_fields(4,5,6) simp_thms if_True)

lemma prd_actual_dispatch_reply_is_cached:
  "call_authority_results (product_calls hf_dispatched) (7,2) =
    Some (hf_dispatch, snd (sample.execute_finality_client hf_dispatch
      (call_authority_state (product_calls hf_reserved))), 1)"
proof -
  have prior: "length (call_authority_log (product_calls hf_reserved)) = 1"
    using prp_revisions_come_from_actual_submissions(2)
    by (simp add: current_product_cut_def)
  show ?thesis
    unfolding prd_dispatch_reaches_the_actual_authority_step
    by (rule sample.finality_calls.first_dispatch_records_the_actual_execution(2)
        [OF prd_begun_fields(1), unfolded prd_begun_fields(2,3) prior])
qed

lemma prd_the_actual_second_reply_reports_dispatch:
  "prd_outcome = Authority_Reply (Protocol_Response Source_Dispatched)"
proof -
  let ?actual = "call_authority_state (product_calls hf_reserved)"
  let ?fixture = "lock_example_core lock_example_held"
  have parent: "core_parent ?actual = core_parent ?fixture"
    unfolding prd_reserved_finality_core lock_example_core_def by simp
  have same_view: "current_lock_view ?actual 0 = current_lock_view ?fixture 0"
    unfolding prd_reserved_finality_core lock_example_core_def lock_example_contexts_def finality_sample_initial_def
    by (simp add: initial_finality_core_def current_lock_view_def)
  have reply: "snd (sample.execute_finality_client hf_dispatch ?actual) =
    snd (sample.execute_finality_client lock_example_dispatch ?fixture)"
    unfolding hf_dispatch_def lock_example_dispatch_def sample.first_protocol_call_uses_the_current_core
    by (simp only: snd_conv sample.invoke_protocol_def terminal_intent_guard.simps
        simp_thms if_True Let_def parent same_view)
  show ?thesis unfolding prd_outcome_def reply lock_example_public_dispatch_reply by simp
qed

lemma prd_dispatch_access_before_submission:
  "result_access_bound pro_verified 7 ((7,2)::client_call_id) prd_payload pro_completed"
  unfolding result_access_bound_def pro_completed_retains_the_produced_source_and_entry(1)
proof (rule conjI)
  show "pro_verified 7 ((7,2)::client_call_id) prd_payload"
    unfolding pro_verified_def by (rule TrueI)
  show "product_identity_bound 7 ((7,2)::client_call_id) (payload_envelope prd_payload) hf_reserved"
    using hf_dispatch_is_a_fresh_call
    unfolding prd_payload_def product_call_payload.select_convs product_new_call_def
    by blast
qed

lemma prd_dispatch_is_stored_from_the_actual_reply:
  "prd_submitted = store_product_result (7,2) prd_payload prd_outcome hf_dispatched pro_completed"
proof -
  have empty: "outcome_entries pro_completed (7,2) = None"
    unfolding pro_completed_updates_only_the_marker
      pro_submit_constructs_the_entry_from_the_actual_reserve_reply store_product_result_def
    by (simp add: pro_initial_def initial_outcome_world_def numeral_2_eq_2)
  have fresh:
    "call_invocations (product_calls (outcome_source pro_completed)) (7,2) = None \<and>
      call_authority_results (product_calls (outcome_source pro_completed)) (7,2) = None \<and>
      call_connection (product_calls (outcome_source pro_completed)) = Authority_Connected \<and>
      call_local_status (product_calls (outcome_source pro_completed)) = Endpoint_Up"
    unfolding pro_completed_retains_the_produced_source_and_entry(1)
    using prd_second_call_starts_with_fresh_connected_fields by blast
  show ?thesis
    unfolding prd_submitted_def
      sample.first_connected_call_records_its_public_result[OF prd_dispatch_access_before_submission empty fresh, unfolded Let_def]
      prd_dispatch_uses_the_actual_lock_entry prd_actual_dispatch_reply_is_cached
    by (simp only: option.case case_prod_conv prd_outcome_def)
qed

lemma prd_submission_retains_old_entry_and_stores_new_entry:
  "outcome_source prd_submitted = hf_dispatched"
  "outcome_entries prd_submitted (7,1) = Some pro_original_entry"
  "outcome_entries prd_submitted (7,2) = Some prd_entry"
  "outcome_completed prd_submitted = {(7,1)}"
proof -
  show "outcome_entries prd_submitted (7,1) = Some pro_original_entry"
    unfolding prd_submitted_def
    by (rule sample.authoritative_call_keeps_older_results[OF pro_completed_retains_the_produced_source_and_entry(2)])
  show "outcome_source prd_submitted = hf_dispatched"
    "outcome_entries prd_submitted (7,2) = Some prd_entry"
    unfolding prd_dispatch_is_stored_from_the_actual_reply store_product_result_def prd_entry_def
    by simp_all
  have completed: "outcome_completed prd_submitted = outcome_completed pro_completed"
    unfolding prd_dispatch_is_stored_from_the_actual_reply store_product_result_def by simp
  show "outcome_completed prd_submitted = {(7,1)}"
    unfolding completed by (rule pro_completed_retains_the_produced_source_and_entry(3))
qed

lemma prd_dispatched_endpoint_is_up:
  "call_local_status (product_calls hf_dispatched) = Endpoint_Up"
  unfolding prd_dispatch_reaches_the_actual_authority_step sample.finality_calls.execute_authority_once_def
    prd_begun_fields(1) Let_def
  by (simp add: prd_begun_fields(5))

lemma prd_fresh_completion_records_the_actual_dispatch:
  "complete_authoritative_result pro_verified 7 ((7,2)::client_call_id) prd_payload prd_submitted =
    (prd_submitted\<lparr>outcome_completed := {(7,2),(7,1)}\<rparr>, Some prd_outcome)"
proof -
  have identity: "product_identity_bound 7 ((7,2)::client_call_id) (payload_envelope prd_payload) hf_dispatched"
    by (simp add: product_identity_bound_def prd_payload_def hf_envelope_def hf_dispatch_def
        sample_request_def prp_initial_reserved_dispatched_metadata(3,6) hf_sessions_def)
  have access: "result_access_bound pro_verified 7 ((7,2)::client_call_id) prd_payload prd_submitted"
    unfolding result_access_bound_def prd_submission_retains_old_entry_and_stores_new_entry(1) pro_verified_def
    by (rule conjI[OF TrueI identity])
  have exact: "result_payload prd_entry = prd_payload"
    by (simp add: prd_entry_def)
  have ready: "result_completion_ready prd_entry prd_submitted"
    by (simp add: result_completion_ready_def prd_entry_def prd_payload_def hf_envelope_def
        hf_dispatch_def prd_the_actual_second_reply_reports_dispatch Let_def)
  have retained: "read_authoritative_result pro_verified 7 ((7,2)::client_call_id) prd_payload prd_submitted =
    Some (result_outcome prd_entry)"
    by (rule exact_retry_reads_the_committed_outcome[OF access
        prd_submission_retains_old_entry_and_stores_new_entry(3) exact ready])
  show ?thesis
    unfolding complete_authoritative_result_def prd_submission_retains_old_entry_and_stores_new_entry(1,4)
      prd_dispatched_endpoint_is_up retained
    by (simp add: prd_entry_def)
qed

lemma prd_completed_updates_only_the_marker:
  "prd_completed = prd_submitted\<lparr>outcome_completed := {(7,2),(7,1)}\<rparr>"
  unfolding prd_completed_def prd_fresh_completion_records_the_actual_dispatch by simp

lemma prd_completed_dispatch_retains_both_actual_entries:
  "outcome_source prd_completed = hf_dispatched"
  "outcome_entries prd_completed (7,1) = Some pro_original_entry"
  "outcome_entries prd_completed (7,2) = Some prd_entry"
  "outcome_completed prd_completed = {(7,2),(7,1)}"
proof -
  have source: "outcome_source prd_completed = outcome_source prd_submitted"
    unfolding prd_completed_updates_only_the_marker by simp
  have entries: "outcome_entries prd_completed = outcome_entries prd_submitted"
    unfolding prd_completed_updates_only_the_marker by simp
  show "outcome_source prd_completed = hf_dispatched"
    unfolding source by (rule prd_submission_retains_old_entry_and_stores_new_entry(1))
  show "outcome_entries prd_completed (7,1) = Some pro_original_entry"
    unfolding entries by (rule prd_submission_retains_old_entry_and_stores_new_entry(2))
  show "outcome_entries prd_completed (7,2) = Some prd_entry"
    unfolding entries by (rule prd_submission_retains_old_entry_and_stores_new_entry(3))
  show "outcome_completed prd_completed = {(7,2),(7,1)}"
    unfolding prd_completed_updates_only_the_marker by simp
qed

thm_oracles prd_dispatch_is_stored_from_the_actual_reply prd_the_actual_second_reply_reports_dispatch
  prd_fresh_completion_records_the_actual_dispatch prd_completed_dispatch_retains_both_actual_entries

ML \<open>
  if null (Thm_Deps.all_oracles @{thms prd_dispatch_is_stored_from_the_actual_reply
      prd_the_actual_second_reply_reports_dispatch prd_fresh_completion_records_the_actual_dispatch
      prd_completed_dispatch_retains_both_actual_entries})
  then writeln "P13_REPLAY_DISPATCH_ORACLES_EMPTY"
  else error "Unexpected oracle in receipt continuation"
\<close>

end
