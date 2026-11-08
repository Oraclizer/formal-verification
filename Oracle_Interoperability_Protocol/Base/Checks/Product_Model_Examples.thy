theory Product_Model_Examples
  imports "../Product_Model" Product_Model_Refutation
begin

definition example_product_envelope where
  "example_product_envelope = \<lparr>envelope_message = 1, envelope_origin = (0,17),
    envelope_asset = 4, envelope_caller = 7, envelope_session = 1,
    envelope_cut = \<lparr>cut_authority_epoch = 0, cut_revision = 0\<rparr>,
    envelope_command = call_example_command\<rparr>"

definition example_product_before where
  "example_product_before = \<lparr>product_durable = \<lparr>product_authority_epoch = 0,
      product_owners = (\<lambda>_. None)(4 := Some 7),
      product_sessions = (\<lambda>_. None)(1 := Some \<lparr>session_principal = 7, session_epoch = 0\<rparr>),
      product_locks = (\<lambda>_. None), product_requests = (\<lambda>_. None)\<rparr>,
      product_calls = initial_call_machine call_example_ready\<rparr>"

definition example_product_verified where
  "example_product_verified who call_id envelope \<longleftrightarrow> envelope = example_product_envelope"

lemma example_verifier_accepts_original:
  "example_product_verified 7 refutation_call_id example_product_envelope"
  by (simp add: example_product_verified_def)

lemma example_identity_is_bound:
  "product_identity_bound 7 refutation_call_id example_product_envelope example_product_before"
  by (simp add: product_identity_bound_def example_product_envelope_def example_product_before_def
      current_product_cut_def initial_call_machine_def call_example_command_def
      spend_request_def sample_request_def)

lemma example_new_call_is_enabled:
  "product_new_call 7 refutation_call_id example_product_envelope example_product_before"
  using example_identity_is_bound
  by (simp add: product_new_call_def example_product_envelope_def example_product_before_def
      current_product_cut_def initial_call_machine_def)

definition example_product_dispatched where
  "example_product_dispatched = sample.product_submit example_product_verified
    7 refutation_call_id example_product_envelope example_product_before"

lemma example_product_uses_public_dispatch:
  "product_calls example_product_dispatched = call_example_once"
proof -
  have dispatch: "product_calls example_product_dispatched = sample.finality_calls.run_calls
    [Begin_Call refutation_call_id (envelope_command example_product_envelope),
     Dispatch_Call refutation_call_id (envelope_command example_product_envelope)] (product_calls example_product_before)"
    unfolding example_product_dispatched_def
    by (rule sample.product_new_call_uses_authoritative_dispatch)
      (rule example_verifier_accepts_original, rule example_new_call_is_enabled)
  show ?thesis
    by (simp add: dispatch example_product_envelope_def example_product_before_def call_example_once_def)
qed

lemma example_forged_submission_does_not_change_state:
  "sample.product_submit example_product_verified 8 refutation_call_id
    example_product_envelope example_product_before = example_product_before"
  by (rule sample.product_rejects_unbound_identity) (simp add: product_identity_bound_def)

definition example_product_restarted where
  "example_product_restarted = sample.product_restart (Some (product_durable_snapshot example_product_dispatched))
    (sample.product_crash example_product_dispatched)"

lemma example_current_snapshot_restarts_endpoint:
  "call_local_status (product_calls example_product_restarted) = Endpoint_Up \<and>
   product_durable_snapshot example_product_restarted = product_durable_snapshot example_product_dispatched"
  unfolding example_product_restarted_def
  by (rule sample.product_restart_from_durable_state)
    (simp add: example_product_uses_public_dispatch call_example_once_fields)

lemma example_missing_snapshot_leaves_endpoint_down:
  "call_local_status (product_calls (sample.product_restart None (sample.product_crash example_product_dispatched))) = Endpoint_Down"
  by (simp add: sample.product_restart_def sample.product_crash_def sample.product_apply_public_def)

lemma example_restarted_call_machine:
  "product_calls example_product_restarted = sample.finality_calls.run_calls
    [Crash_Local_Endpoint, Recover_Local_Endpoint] call_example_once"
  by (simp add: example_product_restarted_def example_product_uses_public_dispatch
      sample.product_restart_def sample.product_crash_def sample.product_apply_public_def
      product_durable_snapshot_def call_example_once_fields(7))

lemma example_prior_call_after_restart:
  "product_prior_call 7 refutation_call_id example_product_envelope example_product_restarted"
proof -
  have durable: "product_durable example_product_restarted = product_durable example_product_dispatched"
    using example_current_snapshot_restarts_endpoint by (simp add: product_durable_snapshot_def)
  have binding: "product_durable example_product_dispatched = (product_durable example_product_before)
    \<lparr>product_requests := (product_requests (product_durable example_product_before))
      (refutation_call_id := Some example_product_envelope)\<rparr>"
    unfolding example_product_dispatched_def sample.product_submit_def
    by (simp only: example_verifier_accepts_original example_new_call_is_enabled if_True)
      (simp add: sample.product_apply_public_def)
  show ?thesis
    using example_identity_is_bound
    by (simp add: product_prior_call_def product_identity_bound_def current_product_cut_def
        durable binding)
qed

lemma example_completed_response_is_observed_after_crash:
  "call_completions (product_calls (sample.product_submit example_product_verified 7 refutation_call_id
    example_product_envelope example_product_restarted)) refutation_call_id =
    Some (Protocol_Response Descendant_Executed)"
proof -
  have collect: "product_calls (sample.product_submit example_product_verified 7 refutation_call_id
    example_product_envelope example_product_restarted) = sample.finality_calls.run_calls
    [Collect_Response refutation_call_id (envelope_command example_product_envelope), Complete_Call refutation_call_id]
    (product_calls example_product_restarted)"
    by (rule sample.product_prior_call_uses_authoritative_result_path)
      (rule example_verifier_accepts_original, rule example_prior_call_after_restart)
  show ?thesis
    unfolding collect example_restarted_call_machine
    by (simp add: example_product_envelope_def call_example_once_fields
        sample.finality_calls.collect_client_response_def sample.finality_calls.complete_client_call_def)
qed

end
