theory Call_Outcome_Examples
  imports "../Outcome_Recovery" Lock_Endpoint_Examples
    "../Outcome_Gates"
begin

definition once_example_payload where
  "once_example_payload = \<lparr>payload_envelope = lock_example_envelope lock_example_dispatch,
    payload_credential = Some lock_example_token, payload_origin_epoch = 9\<rparr>"

definition once_example_start where
  "once_example_start = initial_outcome_world (lock_example_world lock_example_held)"

definition once_example_permitted where
  "once_example_permitted entry who command \<longleftrightarrow> entry = Normal_Lock_Entry"

definition once_example_submit where
  "once_example_submit entry s = sample.submit_authoritative_call once_example_permitted
    (\<lambda>_ _ _. True) {} {0,2} entry 7 (7,1) once_example_payload s"

lemma once_example_has_bound_identity:
  "result_access_bound (\<lambda>_ _ _. True) 7 (7,1) once_example_payload once_example_start"
proof -
  have identity: "product_identity_bound 7 (7,1) (lock_example_envelope lock_example_dispatch) (lock_example_world lock_example_held)"
    by (simp add: product_identity_bound_def lock_example_envelope_def lock_example_world_def
      lock_example_dispatch_def current_product_cut_def sample_request_def)
  show ?thesis by (simp add: result_access_bound_def once_example_start_def initial_outcome_world_def once_example_payload_def identity)
qed

lemma exact_first_submission_uses_public_dispatch:
  "sample.lock_product_step once_example_permitted (\<lambda>_ _ _ _. True) {} {0,2}
    (Lock_Submit Normal_Lock_Entry 7 (7,1) (payload_envelope once_example_payload) (payload_credential once_example_payload))
    (outcome_source once_example_start) = lock_example_submit Normal_Lock_Entry (Some lock_example_token)"
  by (simp add: once_example_permitted_def once_example_start_def initial_outcome_world_def once_example_payload_def
      registered_lock_envelope_def lock_example_envelope_def lock_example_dispatch_def lock_example_submit_def
      sample.submit_lock_entry_def sample.lock_submission_allowed_def)

lemma once_example_fresh_public_fields:
  "call_invocations (product_calls (outcome_source once_example_start)) (7,1) = None \<and>
    call_authority_results (product_calls (outcome_source once_example_start)) (7,1) = None \<and>
    call_connection (product_calls (outcome_source once_example_start)) = Authority_Connected \<and>
    call_local_status (product_calls (outcome_source once_example_start)) = Endpoint_Up"
  by (simp add: once_example_start_def initial_outcome_world_def lock_example_world_def initial_call_machine_def)

lemma once_example_has_no_previous_result:
  "outcome_entries once_example_start (7,1) = None"
  by (simp add: once_example_start_def initial_outcome_world_def)

lemma authority_stores_the_bound_source_dispatch_result:
  "outcome_entries (once_example_submit Normal_Lock_Entry once_example_start) (7,1) = Some
    \<lparr>result_payload = once_example_payload, result_outcome = Authority_Reply (Protocol_Response Source_Dispatched)\<rparr>"
proof -
  have raw: "call_authority_results (product_calls (lock_example_submit Normal_Lock_Entry (Some lock_example_token))) (7,1) =
    Some (lock_example_dispatch, Protocol_Response Source_Dispatched, 0)"
    by (rule normal_admin_and_adapter_dispatch_with_current_credential)
  have store: "once_example_submit Normal_Lock_Entry once_example_start =
    store_product_result (7,1) once_example_payload (Authority_Reply (Protocol_Response Source_Dispatched))
      (lock_example_submit Normal_Lock_Entry (Some lock_example_token)) once_example_start"
    unfolding once_example_submit_def
      sample.first_connected_call_records_its_public_result[OF once_example_has_bound_identity
        once_example_has_no_previous_result once_example_fresh_public_fields, unfolded Let_def]
      exact_first_submission_uses_public_dispatch raw
    by simp
  show ?thesis unfolding store by (simp add: store_product_result_def)
qed

lemma denied_admin_call_stores_only_its_result:
  "once_example_submit Administrative_Lock_Entry once_example_start =
    store_product_result (7,1) once_example_payload Authority_Rejected (outcome_source once_example_start) once_example_start"
proof -
  have refused: "sample.lock_product_step once_example_permitted (\<lambda>_ _ _ _. True) {} {0,2}
    (Lock_Submit Administrative_Lock_Entry 7 (7,1) (payload_envelope once_example_payload) (payload_credential once_example_payload))
    (outcome_source once_example_start) = outcome_source once_example_start"
    by (simp add: sample.submit_lock_entry_def sample.lock_submission_allowed_def once_example_permitted_def)
  have raw: "call_authority_results (product_calls (outcome_source once_example_start)) (7,1) = None"
    by (rule conjunct1[OF conjunct2[OF once_example_fresh_public_fields]])
  show ?thesis unfolding once_example_submit_def
      sample.first_connected_call_records_its_public_result[OF once_example_has_bound_identity
        once_example_has_no_previous_result once_example_fresh_public_fields, unfolded Let_def]
      refused raw by simp
qed

lemma denied_admin_call_has_a_stable_rejection:
  "outcome_entries (once_example_submit Administrative_Lock_Entry once_example_start) (7,1) = Some
    \<lparr>result_payload = once_example_payload, result_outcome = Authority_Rejected\<rparr>"
  unfolding denied_admin_call_stores_only_its_result by (simp add: store_product_result_def)

lemma a_same_call_retry_at_an_allowed_entry_cannot_replace_the_denial:
  "once_example_submit Normal_Lock_Entry (once_example_submit Administrative_Lock_Entry once_example_start) =
    once_example_submit Administrative_Lock_Entry once_example_start"
  using denied_admin_call_has_a_stable_rejection
  by (simp add: once_example_submit_def sample.authoritative_call_retry_does_not_repeat_effect)

lemma loss_of_the_stored_denial_allows_a_later_effect:
  "let denied = once_example_submit Administrative_Lock_Entry once_example_start;
       missing = denied\<lparr>outcome_entries := (outcome_entries denied)((7,1) := None)\<rparr>
    in outcome_entries (once_example_submit Normal_Lock_Entry missing) (7,1) = Some
      \<lparr>result_payload = once_example_payload, result_outcome = Authority_Reply (Protocol_Response Source_Dispatched)\<rparr>"
proof -
  have emptied: "(let denied = once_example_submit Administrative_Lock_Entry once_example_start
    in denied\<lparr>outcome_entries := (outcome_entries denied)((7,1) := None)\<rparr>) = once_example_start"
    unfolding denied_admin_call_stores_only_its_result
    by (simp add: once_example_start_def initial_outcome_world_def store_product_result_def Let_def)
  show ?thesis unfolding Let_def emptied[unfolded Let_def]
    by (rule authority_stores_the_bound_source_dispatch_result)
qed

end
