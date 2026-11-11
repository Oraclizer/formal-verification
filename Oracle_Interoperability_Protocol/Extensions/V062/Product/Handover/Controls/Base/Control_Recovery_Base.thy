theory Control_Recovery_Base
  imports "OIP_V062_Handover_Typed_Model.Handover_Typed_Model"
begin

text \<open>These controls reuse the checked typed source after its normal
handover. Endorsement admission and the selected Refund consumer are separate.
No theorem below equates an endorsement with a financial refund, or equates
unchanged financial state with an unchanged request/receipt log.\<close>

definition hc_post_source :: product_world where
  "hc_post_source = hg_product_after True True"

definition hc_post_core :: finality_core where
  "hc_post_core = call_authority_state (product_calls hc_post_source)"

definition hc_typed_authenticate :: "registered_identity \<Rightarrow> registered_identity option" where
  "hc_typed_authenticate m_identity = Some m_identity"

definition hc_typed_policy :: endpoint_policy where
  "hc_typed_policy = (\<lambda>_ _ _ _ _. True)"

definition hc_typed_verify :: "registered_identity \<Rightarrow> session_proof \<Rightarrow> nat \<Rightarrow>
    endpoint_use \<Rightarrow> client_call_id \<Rightarrow> product_call_payload \<Rightarrow> bool" where
  "hc_typed_verify = (\<lambda>_ _ _ _ _ _. True)"

definition hc_typed_endorse :: "registered_identity \<Rightarrow> session_proof \<Rightarrow> nat \<Rightarrow>
    source_key \<Rightarrow> client_call_id \<Rightarrow> product_call_payload \<Rightarrow> bool" where
  "hc_typed_endorse = (\<lambda>_ _ _ _ _ _. True)"

definition hc_refund_request :: execution_request where
  "hc_refund_request = (sample_request 17)\<lparr>request_authority_epoch := 10\<rparr>"

definition hc_refund_command :: client_command where
  "hc_refund_command = Client_Protocol 0 0 (Return_Intent hc_refund_request 0 [])"

definition hc_refund_payload :: product_call_payload where
  "hc_refund_payload = \<lparr>payload_envelope = \<lparr>envelope_message = 10,
    envelope_origin = (0,17), envelope_asset = 17, envelope_caller = 7, envelope_session = 2,
    envelope_cut = current_product_cut hc_post_source, envelope_command = hc_refund_command\<rparr>,
    payload_credential = Some (lock_example_token\<lparr>credential_epoch := 10\<rparr>),
    payload_origin_epoch = 9\<rparr>"

definition hc_endorsement :: "nat \<Rightarrow> nat \<Rightarrow> registered_identity recovery_endorsement" where
  "hc_endorsement m_who m_session = \<lparr>endorsement_token = identity_case_user m_who,
    endorsement_session = identity_case_proof m_session 10\<rparr>"

definition hc_endorsement_allowed :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "hc_endorsement_allowed m_who m_session = recovery_has_current_endorsement identity_case_directory
    hc_typed_policy hc_typed_authenticate hc_typed_endorse (0::nat) (0,17) ((7,10)::client_call_id)
    hc_refund_payload (hc_endorsement m_who m_session) hc_post_source"

lemma hc_post_financial_state_is_the_same_checked_pending_state:
  "authoritative_reservation_state hc_post_source = authoritative_reservation_state hf_source"
  by (simp add: hc_post_source_def hg_product_financial_state_and_phase_are_preserved)

lemma hc_post_owner_and_live_sessions:
  "owner_of_product hc_post_source 17 = Some 8"
  "cut_authority_epoch (current_product_cut hc_post_source) = 10"
  "active_identity identity_case_directory (identity_case_user 7) (identity_case_proof 2 10) hc_post_source"
  "active_identity identity_case_directory (identity_case_user 8) (identity_case_proof 3 10) hc_post_source"
  using hg_normal_reuses_the_checked_native_product_relation(1)
    hg_normal_native_owner_sessions_epoch_and_immutable_ledger(2,7)
    hg_old_proof_is_rejected_but_the_worker_remains_live(2,3)
  by (simp_all add: hc_post_source_def rust_handover_matches_def)

lemma hc_live_claim_is_unchanged:
  "\<exists>m_claim. recoverable_reservation hc_post_source (0,17) = Some m_claim \<and>
    reservation_binding m_claim = sample_binding 17 \<and> reservation_phase m_claim = Source_Pending"
proof -
  obtain m_claim where stored: "reservation_at (authoritative_reservation_state hf_source) (0,17) = Some m_claim"
    and bound: "reservation_binding m_claim = sample_binding 17"
    and phase: "reservation_phase m_claim = Source_Pending"
    using hf_source_phase_is_pending by blast
  have live: "recoverable_reservation hc_post_source (0,17) = Some m_claim"
    by (simp add: recoverable_reservation_def hc_post_financial_state_is_the_same_checked_pending_state stored phase)
  show ?thesis using live bound phase by blast
qed

lemma hc_actual_controller_is_the_successor:
  "recovery_controller hc_post_source (0,17) = Some 8"
proof -
  obtain m_claim where live: "recoverable_reservation hc_post_source (0,17) = Some m_claim"
    and bound: "reservation_binding m_claim = sample_binding 17"
    using hc_live_claim_is_unchanged by blast
  show ?thesis
    by (simp add: recovery_controller_def live bound sample_binding_def example_binding_def hc_post_owner_and_live_sessions(1))
qed

lemma hc_successor_passes_but_the_live_former_worker_does_not_endorse:
  "hc_endorsement_allowed 8 3"
  "\<not> hc_endorsement_allowed 7 2"
  using hc_post_owner_and_live_sessions(3,4)
  by (auto simp: hc_endorsement_allowed_def recovery_has_current_endorsement_def hc_endorsement_def
      hc_typed_authenticate_def hc_typed_policy_def hc_typed_endorse_def hc_actual_controller_is_the_successor
      identity_case_user_def identity_case_proof_def hc_refund_payload_def)

lemma hc_worker_call_is_current_and_bound:
  "endpoint_call_allowed identity_case_directory hc_typed_policy hc_typed_authenticate hc_typed_verify
    (identity_case_user 7) (identity_case_proof 2 10) (0::nat) Execute_Ordinary 7 ((7,10)::client_call_id)
    hc_refund_payload hc_post_source"
  using hc_post_owner_and_live_sessions(2,3)
  by (auto simp: endpoint_call_allowed_def endpoint_call_identity_def product_identity_bound_def active_identity_def
      hc_typed_authenticate_def hc_typed_policy_def hc_typed_verify_def hc_refund_payload_def
      hc_refund_command_def hc_refund_request_def sample_request_def identity_case_user_def identity_case_proof_def Let_def)

lemma hc_context_installation_preserves_every_terminal_record:
  "core_records (call_authority_state (sample.finality_calls.run_calls (map Apply_Authority_Input m_changes) m_calls)) =
    core_records (call_authority_state m_calls)"
  by (induction m_changes arbitrary: m_calls)
    (simp_all add: sample.finality_calls.apply_authority_input_def sample.execute_finality_environment_def
      sample.finality_step_def Let_def split: if_splits)

lemma hc_post_calls_are_only_the_checked_context_installs:
  "product_calls hc_post_source = sample.finality_calls.run_calls
    (map Apply_Authority_Input (transfer_contexts hg_proposal)) (product_calls hf_source)"
proof -
  have batch: "lock_context_batch_is_newer {0,2} (transfer_epoch hg_proposal) (transfer_contexts hg_proposal) hf_source"
    using hg_normal_authorized by (simp add: handover_is_authorized_def Let_def)
  show ?thesis
    by (simp add: hc_post_source_def hg_product_after_def sample.apply_owner_handover_def hg_normal_authorized batch
      sample.product_apply_public_def Let_def)
qed

lemma hc_setup_and_handover_have_no_recorded_terminal_evidence:
  "core_records hc_post_core = (\<lambda>_. None)"
  using finality_source_prefix_is_the_actual_parent_prefix[of 17]
  by (simp add: hc_post_core_def hc_post_calls_are_only_the_checked_context_installs
      hc_context_installation_preserves_every_terminal_record
      hf_three_actual_submissions_produce_the_public_call_word hf_call_word_uses_the_existing_checked_financial_prefix)

lemma hc_reference_zero_is_not_an_exact_reversal:
  "\<not> exact_record_reference hc_post_core 0 (request_binding hc_refund_request)
    Reversed_Decision (request_certificate hc_refund_request)"
  by (simp add: exact_record_reference_def record_reference_def hc_setup_and_handover_have_no_recorded_terminal_evidence)

definition hc_refund_core_result :: "finality_core \<times> finality_reply" where
  "hc_refund_core_result = sample.invoke_protocol 0 (core_epoch hc_post_core) 0
    (Return_Intent hc_refund_request 0 []) hc_post_core"

lemma hc_refund_is_the_exact_rejected_protocol_step:
  "hc_refund_core_result =
    (reject_protocol_intent (Return_Intent hc_refund_request 0 []) hc_post_core, Finality_Rejected)"
  by (simp add: hc_refund_core_result_def sample.invoke_protocol_def hc_reference_zero_is_not_an_exact_reversal)

lemma hc_rejected_refund_observation_keeps_the_financial_state:
  "machine_state (core_parent (reject_protocol_intent (Return_Intent hc_refund_request 0 []) hc_post_core)) =
    machine_state (core_parent hc_post_core)"
  by (simp add: reject_protocol_intent_def record_observation_def)

lemma hc_actual_refund_consumer_rejects_the_missing_record_without_financial_effect:
  "snd hc_refund_core_result = Finality_Rejected"
  "machine_state (core_parent (fst hc_refund_core_result)) = authoritative_reservation_state hc_post_source"
proof -
  show "snd hc_refund_core_result = Finality_Rejected"
    by (simp add: hc_refund_is_the_exact_rejected_protocol_step)
  have frame: "machine_state (core_parent (fst hc_refund_core_result)) = machine_state (core_parent hc_post_core)"
    by (simp add: hc_refund_is_the_exact_rejected_protocol_step hc_rejected_refund_observation_keeps_the_financial_state)
  show "machine_state (core_parent (fst hc_refund_core_result)) = authoritative_reservation_state hc_post_source"
    using frame by (simp only: hc_post_core_def authoritative_reservation_state_def)
qed

definition hc_selected_reply :: "nat \<Rightarrow> nat \<Rightarrow> finality_reply option" where
  "hc_selected_reply m_who m_session =
    (if hc_endorsement_allowed m_who m_session then Some (snd hc_refund_core_result) else None)"

definition hc_selected_financial_state :: "nat \<Rightarrow> nat \<Rightarrow> reservation_state" where
  "hc_selected_financial_state m_who m_session =
    (if hc_endorsement_allowed m_who m_session then machine_state (core_parent (fst hc_refund_core_result))
     else authoritative_reservation_state hc_post_source)"

lemma hc_gate_and_refund_effect_are_distinct_observations:
  "hc_selected_reply 8 3 = Some Finality_Rejected"
  "hc_selected_reply 7 2 = None"
  "hc_selected_financial_state 8 3 = authoritative_reservation_state hf_source"
  "hc_selected_financial_state 7 2 = authoritative_reservation_state hf_source"
  by (simp_all add: hc_selected_reply_def hc_selected_financial_state_def
      hc_successor_passes_but_the_live_former_worker_does_not_endorse
      hc_actual_refund_consumer_rejects_the_missing_record_without_financial_effect
      hc_post_financial_state_is_the_same_checked_pending_state)

thm_oracles hc_actual_controller_is_the_successor
  hc_successor_passes_but_the_live_former_worker_does_not_endorse
  hc_worker_call_is_current_and_bound
  hc_setup_and_handover_have_no_recorded_terminal_evidence
  hc_actual_refund_consumer_rejects_the_missing_record_without_financial_effect
  hc_gate_and_refund_effect_are_distinct_observations

ML \<open>
  if null (Thm_Deps.all_oracles @{thms hc_actual_controller_is_the_successor
      hc_successor_passes_but_the_live_former_worker_does_not_endorse
      hc_worker_call_is_current_and_bound
      hc_setup_and_handover_have_no_recorded_terminal_evidence
      hc_actual_refund_consumer_rejects_the_missing_record_without_financial_effect
      hc_gate_and_refund_effect_are_distinct_observations})
  then writeln "HANDOVER_RECOVERY_CONTROL_ORACLES_EMPTY"
  else error "Unexpected oracle in handover recovery controls"
\<close>

end
