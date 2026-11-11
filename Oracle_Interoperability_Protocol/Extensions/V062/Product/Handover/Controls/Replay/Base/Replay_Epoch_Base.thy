theory Replay_Epoch_Base
  imports "OIP_V062_Handover_Typed_Model.Handover_Typed_Model"
    "OIP_Product.Identity_Receipts"
    "OIP_Reference_Execution.Reference_Signed_Replay_Code"
begin

text \<open>This first scope is typed logical receipt replay, not wire-UUID
replay or a Current_Data query. The original request and its cached result
come from Reserve; a different current epoch comes from Lock_Install and a
later same-epoch revision comes from the actual Dispatch.\<close>

definition prp_authenticate :: "registered_identity \<Rightarrow> registered_identity option" where
  "prp_authenticate m_identity = Some m_identity"

definition prp_policy :: endpoint_policy where
  "prp_policy = (\<lambda>_ _ _ _ _. True)"

definition prp_verify :: "registered_identity \<Rightarrow> session_proof \<Rightarrow> nat \<Rightarrow>
    endpoint_use \<Rightarrow> client_call_id \<Rightarrow> product_call_payload \<Rightarrow> bool" where
  "prp_verify = (\<lambda>_ _ _ _ _ _. True)"

definition prp_original_payload :: product_call_payload where
  "prp_original_payload = \<lparr>payload_envelope = hf_envelope 1 1 hf_reserve hf_initial,
    payload_credential = None, payload_origin_epoch = 9\<rparr>"

definition prp_changed_payload :: product_call_payload where
  "prp_changed_payload = prp_original_payload\<lparr>payload_envelope :=
    (payload_envelope prp_original_payload)\<lparr>envelope_command :=
      Client_Protocol 0 0 (Reserve_Intent (sample_request 17) [] 11)\<rparr>\<rparr>"

definition prp_receipt_gate :: "nat \<Rightarrow> product_call_payload \<Rightarrow> product_world \<Rightarrow> bool" where
  "prp_receipt_gate m_epoch m_payload m_world = endpoint_call_allowed identity_case_directory prp_policy
    prp_authenticate prp_verify (identity_case_user 7) (identity_case_proof 1 m_epoch) (0::nat)
    Read_Receipt 7 ((7,1)::client_call_id) m_payload m_world"

definition prp_receipt_without_signed_epoch :: "nat \<Rightarrow> product_call_payload \<Rightarrow> product_world \<Rightarrow> bool" where
  "prp_receipt_without_signed_epoch m_epoch m_payload m_world = endpoint_call_identity identity_case_directory prp_policy
    prp_authenticate prp_verify (identity_case_user 7) (identity_case_proof 1 m_epoch) (0::nat)
    Read_Receipt 7 ((7,1)::client_call_id) m_payload m_world"

definition prp_reissued_source :: product_world where
  "prp_reissued_source = sample.lock_product_step (\<lambda>_ _ _. False) (\<lambda>_ _ _ _. False)
    ({7}::nat set) {0,2} (Lock_Install 7 10 (transfer_contexts hg_proposal) (hf_sessions 10)) hf_reserved"

lemma prp_submit_keeps_authority_and_sessions:
  "product_authority_epoch (product_durable (hf_submit m_session m_sequence m_command m_world)) =
    product_authority_epoch (product_durable m_world)"
  "product_sessions (product_durable (hf_submit m_session m_sequence m_command m_world)) =
    product_sessions (product_durable m_world)"
  by (auto simp: hf_submit_def sample.product_submit_def sample.product_apply_public_def split: if_splits)

lemma prp_initial_reserved_dispatched_metadata:
  "cut_authority_epoch (current_product_cut hf_initial) = 9"
  "cut_authority_epoch (current_product_cut hf_reserved) = 9"
  "cut_authority_epoch (current_product_cut hf_dispatched) = 9"
  "product_sessions (product_durable hf_initial) = hf_sessions 9"
  "product_sessions (product_durable hf_reserved) = hf_sessions 9"
  "product_sessions (product_durable hf_dispatched) = hf_sessions 9"
  by (simp_all add: current_product_cut_def hf_reserved_def hf_dispatched_def
      prp_submit_keeps_authority_and_sessions hf_initial_def lock_example_world_def)

lemma prp_actual_reserved_call_machine:
  "product_calls hf_reserved = sample.finality_calls.run_calls
    [Begin_Call (7,1) hf_reserve, Dispatch_Call (7,1) hf_reserve] (initial_call_machine finality_sample_initial)"
  using hf_a_fresh_submit_uses_the_checked_dispatch[OF hf_reserve_is_a_fresh_call]
  by (simp add: hf_reserved_def hf_initial_call_machine)

lemma prp_actual_dispatched_call_machine:
  "product_calls hf_dispatched = sample.finality_calls.run_calls
    [Begin_Call (7,2) hf_dispatch, Dispatch_Call (7,2) hf_dispatch] (product_calls hf_reserved)"
  unfolding hf_dispatched_def
  by (rule hf_a_fresh_submit_uses_the_checked_dispatch[OF hf_dispatch_is_a_fresh_call])

lemma prp_revisions_come_from_actual_submissions:
  "cut_revision (current_product_cut hf_initial) = 0"
  "cut_revision (current_product_cut hf_reserved) = 1"
  "cut_revision (current_product_cut hf_dispatched) = 2"
  by (simp_all add: current_product_cut_def hf_initial_call_machine
      prp_actual_reserved_call_machine prp_actual_dispatched_call_machine
      initial_call_machine_def sample.finality_calls.call_definitions numeral_2_eq_2 Let_def)

lemma prp_context_install_has_the_actual_new_epoch:
  "lock_context_batch_is_newer {0,2} 10 (transfer_contexts hg_proposal) hf_reserved"
  by (simp add: lock_context_batch_is_newer_def prp_initial_reserved_dispatched_metadata
      hg_proposal_def handover_case_proposal_def handover_case_context_def lock_example_contexts_def
      sample_source_context_def sample_context_def example_context_def Let_def)

lemma prp_reused_numeric_session_is_current:
  "cut_authority_epoch (current_product_cut prp_reissued_source) = 10"
  "product_sessions (product_durable prp_reissued_source) = hf_sessions 10"
  "active_identity identity_case_directory (identity_case_user 7) (identity_case_proof 1 10) prp_reissued_source"
  by (simp_all add: prp_reissued_source_def prp_context_install_has_the_actual_new_epoch
      sample.product_apply_public_def current_product_cut_def active_identity_def hf_sessions_def
      identity_case_user_def identity_case_directory_def identity_case_proof_def Let_def)

lemma prp_original_signed_epoch_is_not_rewritten:
  "cut_authority_epoch (envelope_cut (payload_envelope prp_original_payload)) = 9"
  "cut_revision (envelope_cut (payload_envelope prp_original_payload)) = 0"
  by (simp_all add: prp_original_payload_def hf_envelope_def
      prp_initial_reserved_dispatched_metadata prp_revisions_come_from_actual_submissions)

lemma prp_original_is_admitted_at_the_same_epoch:
  "prp_receipt_gate 9 prp_original_payload hf_reserved"
  by (simp add: prp_receipt_gate_def endpoint_call_allowed_def endpoint_call_identity_def active_identity_def
      product_identity_bound_def prp_authenticate_def prp_policy_def prp_verify_def prp_original_payload_def
      hf_envelope_def hf_reserve_def sample_request_def hf_sessions_def
      prp_initial_reserved_dispatched_metadata identity_case_user_def identity_case_directory_def identity_case_proof_def Let_def)

lemma prp_later_revision_keeps_the_actual_identity_admission:
  "prp_receipt_gate 9 prp_original_payload hf_dispatched"
proof -
  have epoch: "cut_authority_epoch (current_product_cut hf_reserved) = cut_authority_epoch (current_product_cut hf_dispatched)"
    by (simp add: prp_initial_reserved_dispatched_metadata)
  have sessions: "product_sessions (product_durable hf_reserved) = product_sessions (product_durable hf_dispatched)"
    by (simp add: prp_initial_reserved_dispatched_metadata)
  have same: "prp_receipt_gate 9 prp_original_payload hf_reserved = prp_receipt_gate 9 prp_original_payload hf_dispatched"
    unfolding prp_receipt_gate_def
    by (rule advancing_only_the_revision_does_not_revoke_a_signed_request[OF epoch sessions])
  show ?thesis using same prp_original_is_admitted_at_the_same_epoch by blast
qed

lemma prp_reused_number_does_not_revive_an_old_signed_request:
  "\<not> prp_receipt_gate 10 prp_original_payload prp_reissued_source"
  unfolding prp_receipt_gate_def
  by (rule an_older_signed_request_cannot_use_a_reopened_session)
    (simp add: prp_original_signed_epoch_is_not_rewritten prp_reused_numeric_session_is_current)

lemma prp_removing_only_signed_epoch_binding_reaches_admission:
  "prp_receipt_without_signed_epoch 10 prp_original_payload prp_reissued_source"
  using prp_reused_numeric_session_is_current(3)
  by (auto simp: prp_receipt_without_signed_epoch_def endpoint_call_identity_def product_identity_bound_def
      active_identity_def prp_authenticate_def prp_policy_def prp_verify_def prp_original_payload_def hf_envelope_def
      hf_reserve_def sample_request_def prp_reused_numeric_session_is_current(1,2) hf_sessions_def
      identity_case_user_def identity_case_directory_def identity_case_proof_def Let_def)

lemma prp_original_cache_entry_is_computed_by_reserve:
  "call_authority_results (product_calls hf_reserved) (7,1) =
    Some (hf_reserve,snd (sample.execute_finality_client hf_reserve finality_sample_initial),0)"
proof -
  have table: "call_authority_results (product_calls hf_reserved) =
    (\<lambda>_. None)((7,1) := Some (hf_reserve,snd (sample.execute_finality_client hf_reserve finality_sample_initial),0))"
    unfolding prp_actual_reserved_call_machine
    by (rule sample.finality_calls.initial_dispatch_projection(2))
  show ?thesis by (simp only: table fun_upd_same)
qed

lemma prp_dispatch_keeps_that_exact_computed_cache_entry:
  "call_authority_results (product_calls hf_dispatched) (7,1) =
    Some (hf_reserve,snd (sample.execute_finality_client hf_reserve finality_sample_initial),0)"
  unfolding prp_actual_dispatched_call_machine
  by (rule sample.finality_calls.recorded_response_survives_every_finite_run
      [OF prp_original_cache_entry_is_computed_by_reserve])

lemma prp_old_epoch_actions_after_handover_fail_every_route:
  assumes "cut_authority_epoch (envelope_cut (payload_envelope m_payload)) = 9"
  shows "\<not> endpoint_call_allowed_on m_route m_directory m_policy m_authenticate m_verify
    m_token m_proof m_target m_operation m_actor m_call_id m_payload (hg_product_after True True)"
  by (rule hg_any_old_signed_payload_fails_every_route[OF assms])

lemma prp_changed_payload_is_a_distinct_request:
  "prp_changed_payload \<noteq> prp_original_payload"
  by (simp add: prp_changed_payload_def prp_original_payload_def hf_envelope_def hf_reserve_def)

thm_oracles prp_revisions_come_from_actual_submissions prp_reused_numeric_session_is_current
  prp_later_revision_keeps_the_actual_identity_admission prp_reused_number_does_not_revive_an_old_signed_request
  prp_removing_only_signed_epoch_binding_reaches_admission prp_dispatch_keeps_that_exact_computed_cache_entry

ML \<open>
  if null (Thm_Deps.all_oracles @{thms prp_revisions_come_from_actual_submissions
      prp_reused_numeric_session_is_current prp_later_revision_keeps_the_actual_identity_admission
      prp_reused_number_does_not_revive_an_old_signed_request prp_removing_only_signed_epoch_binding_reaches_admission
      prp_dispatch_keeps_that_exact_computed_cache_entry prp_old_epoch_actions_after_handover_fail_every_route
      prp_changed_payload_is_a_distinct_request})
  then writeln "P13_REPLAY_EPOCH_BASE_ORACLES_EMPTY"
  else error "Unexpected oracle in P13 Replay epoch controls"
\<close>

end
