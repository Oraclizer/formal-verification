theory Replay_Receipt_Lookup
  imports "OIP_V062_P13_Replay_Install.Replay_Receipt_Install"
    "OIP_V062_P13_Replay_Dispatch.Replay_Outcome_Continuation"
begin

text \<open>The lookup returns only an observation. The exact-collect constructor
selects the receipt classifier here; fresh completion was already executed
by the producer. Typed endpoint verification remains a premise of the case.
The logical observation excludes an outer wire arrival and its binding record.\<close>

definition prc_request :: "product_call_payload \<Rightarrow> regulated_product_action" where
  "prc_request payload = Ordinary_Product_Action (Read_Authority_Action (Exact_Collect 7 (7,1) payload))"

definition prc_read where
  "prc_read route epoch payload s =
    read_authorized_receipt identity_case_directory prp_policy prp_authenticate prp_verify pro_verified
      route (identity_case_user 7) (identity_case_proof 1 epoch) 0 (prc_request payload) (prc_world s)"

definition prc_observe_with_payload_test where
  "prc_observe_with_payload_test matches payload outcomes =
    (if \<not> result_access_bound pro_verified 7 (7,1) payload outcomes then Collection_Rejected
     else if call_local_status (product_calls (outcome_source outcomes)) \<noteq> Endpoint_Up then Collection_Waiting
     else case outcome_entries outcomes (7,1) of None \<Rightarrow> Collection_Waiting
       | Some recorded \<Rightarrow> if \<not> matches (result_payload recorded) payload then Collection_Rejected
         else if result_completion_ready recorded outcomes then Collected (result_outcome recorded)
         else Collection_Waiting)"

definition prc_read_with_tests where
  "prc_read_with_tests epoch_test matches epoch payload s =
    (if epoch_test \<and> prp_receipt_without_signed_epoch epoch payload (outcome_source (prc_outcomes s)) \<and>
      call_local_status (product_calls (outcome_source (prc_outcomes s))) = Endpoint_Up
     then Some (Observed_Ordinary_Result (prc_observe_with_payload_test matches payload (prc_outcomes s)))
     else None)"

lemma prc_payload_test_is_the_public_observation:
  "prc_observe_with_payload_test (=) payload outcomes = observe_collection pro_verified 7 (7,1) payload outcomes"
  unfolding prc_observe_with_payload_test_def observe_collection_def by (rule refl)

lemma prc_lookup_uses_the_exact_two_tests:
  "prc_read route epoch payload s = prc_read_with_tests
    (epoch = cut_authority_epoch (envelope_cut (payload_envelope payload))) (=) epoch payload s"
proof -
  let ?world = "prc_world s"
  let ?request = "prc_request payload"
  let ?source = "outcome_source (prc_outcomes s)"
  let ?allowed = "authorized_endpoint_action identity_case_directory prp_policy prp_authenticate prp_verify
    route (identity_case_user 7) (identity_case_proof 1 epoch) 0 ?request ?world"
  let ?signed = "epoch = cut_authority_epoch (envelope_cut (payload_envelope payload))"
  let ?identity = "prp_receipt_without_signed_epoch epoch payload ?source"
  let ?live = "call_local_status (product_calls (identity_source ?world)) = Endpoint_Up"
  let ?projected_live = "call_local_status (product_calls ?source) = Endpoint_Up"
  have claim: "external_call_claim ?request = Some (Read_Receipt,7,(7,1),payload)"
    unfolding prc_request_def by (simp only: external_call_claim.simps)
  have admission: "?allowed = (?signed \<and> ?identity)"
    unfolding authorized_endpoint_action_def claim endpoint_call_allowed_on_def endpoint_call_allowed_def
      prc_identity_source_is_the_actual_outcome_source prp_receipt_without_signed_epoch_def identity_case_proof_def
    by (simp only: option.case case_prod_conv session_proof.select_convs)
  have guard: "(?allowed \<and> ?live) = (?signed \<and> ?identity \<and> ?projected_live)"
    unfolding admission prc_identity_source_is_the_actual_outcome_source by (rule conj_assoc)
  have actual: "prc_read route epoch payload s =
    (if ?allowed \<and> ?live then exact_endpoint_receipt pro_verified 7 ?request ?world else None)"
    unfolding prc_read_def read_authorized_receipt_def claim
    by (simp only: option.case case_prod_conv endpoint_use.case)
  have result: "exact_endpoint_receipt pro_verified 7 ?request ?world =
    Some (Observed_Ordinary_Result (prc_observe_with_payload_test (=) payload (prc_outcomes s)))"
    unfolding prc_request_def prc_payload_test_is_the_public_observation
    by (simp only: exact_endpoint_receipt.simps prc_ordinary_receipt_reads_the_actual_outcome_table)
  show ?thesis unfolding actual guard result prc_read_with_tests_def by (rule refl)
qed

lemma prc_typed_gate_supplies_the_identity_test:
  "prp_receipt_gate epoch payload source \<Longrightarrow> prp_receipt_without_signed_epoch epoch payload source"
  unfolding prp_receipt_gate_def prp_receipt_without_signed_epoch_def endpoint_call_allowed_def by blast

lemma prc_typed_gate_supplies_the_signed_epoch_test:
  "prp_receipt_gate epoch payload source \<Longrightarrow>
    (epoch = cut_authority_epoch (envelope_cut (payload_envelope payload))) = True"
  by (simp add: prp_receipt_gate_def endpoint_call_allowed_def identity_case_proof_def)

lemma prc_identity_test_supplies_local_result_access:
  "prp_receipt_without_signed_epoch epoch payload (outcome_source outcomes) \<Longrightarrow>
    result_access_bound pro_verified 7 (7,1) payload outcomes"
  unfolding prp_receipt_without_signed_epoch_def endpoint_call_identity_def Let_def
    result_access_bound_def pro_verified_def
  by blast

lemma prc_lookup_passes_the_retained_table_to_the_public_observer:
  assumes gate: "prp_receipt_gate epoch payload (outcome_source (prc_outcomes s))"
    and live: "call_local_status (product_calls (outcome_source (prc_outcomes s))) = Endpoint_Up"
  shows "prc_read route epoch payload s =
    Some (Observed_Ordinary_Result (observe_collection pro_verified 7 (7,1) payload (prc_outcomes s)))"
  unfolding prc_lookup_uses_the_exact_two_tests prc_read_with_tests_def prc_payload_test_is_the_public_observation
  by (simp only: prc_typed_gate_supplies_the_signed_epoch_test[OF gate]
      prc_typed_gate_supplies_the_identity_test[OF gate] live simp_thms if_True)

lemma prc_local_observer_reads_the_retained_original_reply:
  assumes access: "result_access_bound pro_verified 7 (7,1) prp_original_payload outcomes"
    and live: "call_local_status (product_calls (outcome_source outcomes)) = Endpoint_Up"
    and entry: "outcome_entries outcomes (7,1) = Some pro_original_entry"
  shows "observe_collection pro_verified 7 (7,1) prp_original_payload outcomes = Collected pro_original_outcome"
proof -
  have exact: "result_payload pro_original_entry = prp_original_payload"
    and outcome: "result_outcome pro_original_entry = pro_original_outcome"
    by (simp_all add: pro_original_entry_def)
  have ready: "result_completion_ready pro_original_entry outcomes"
    by (rule pro_original_reserve_result_needs_no_terminal_publication_to_be_read)
  have access_test: "(\<not> result_access_bound pro_verified 7 (7,1) prp_original_payload outcomes) = False"
    using access by blast
  show ?thesis
    unfolding observe_collection_def
    by (simp only: access_test live entry simp_thms if_True if_False option.case exact ready outcome)
qed

abbreviation prc_after_dispatch :: settlement_world where
  "prc_after_dispatch \<equiv> prc_settlement prd_completed"

lemma prc_same_epoch_source_entry_and_availability:
  "outcome_source (prc_outcomes prc_after_dispatch) = hf_dispatched"
  "outcome_entries (prc_outcomes prc_after_dispatch) (7,1) = Some pro_original_entry"
  "call_local_status (product_calls (outcome_source (prc_outcomes prc_after_dispatch))) = Endpoint_Up"
proof -
  show "outcome_source (prc_outcomes prc_after_dispatch) = hf_dispatched"
    unfolding prc_settlement_contains_the_actual_outcomes
    by (rule prd_completed_dispatch_retains_both_actual_entries(1))
  show "outcome_entries (prc_outcomes prc_after_dispatch) (7,1) = Some pro_original_entry"
    unfolding prc_settlement_contains_the_actual_outcomes
    by (rule prd_completed_dispatch_retains_both_actual_entries(2))
  show "call_local_status (product_calls (outcome_source (prc_outcomes prc_after_dispatch))) = Endpoint_Up"
    unfolding prc_settlement_contains_the_actual_outcomes prd_completed_dispatch_retains_both_actual_entries(1)
    by (rule prd_dispatched_endpoint_is_up)
qed

lemma prc_exact_old_revision_reads_the_actual_original_after_dispatch:
  "prc_read route 9 prp_original_payload prc_after_dispatch =
    Some (Observed_Ordinary_Result (Collected pro_original_outcome))"
proof -
  have gate: "prp_receipt_gate 9 prp_original_payload (outcome_source (prc_outcomes prc_after_dispatch))"
    unfolding prc_same_epoch_source_entry_and_availability(1)
    by (rule prp_later_revision_keeps_the_actual_identity_admission)
  have access: "result_access_bound pro_verified 7 (7,1) prp_original_payload (prc_outcomes prc_after_dispatch)"
    by (rule prc_identity_test_supplies_local_result_access[OF prc_typed_gate_supplies_the_identity_test[OF gate]])
  have observed:
    "observe_collection pro_verified 7 (7,1) prp_original_payload (prc_outcomes prc_after_dispatch) =
      Collected pro_original_outcome"
    by (rule prc_local_observer_reads_the_retained_original_reply[OF access
        prc_same_epoch_source_entry_and_availability(3,2)])
  show ?thesis
    unfolding prc_lookup_passes_the_retained_table_to_the_public_observer
      [OF gate prc_same_epoch_source_entry_and_availability(3)] observed
    by (rule refl)
qed

lemma prc_changed_payload_passes_the_same_typed_identity_gate:
  "prp_receipt_gate 9 prp_changed_payload (outcome_source (prc_outcomes prc_after_dispatch))"
  unfolding prc_same_epoch_source_entry_and_availability(1)
  by (simp add: prp_receipt_gate_def endpoint_call_allowed_def endpoint_call_identity_def
      product_identity_bound_def active_identity_def prp_authenticate_def prp_policy_def prp_verify_def
      prp_changed_payload_def prp_original_payload_def hf_envelope_def hf_reserve_def sample_request_def
      hf_sessions_def prp_initial_reserved_dispatched_metadata identity_case_user_def identity_case_directory_def
      identity_case_proof_def Let_def)

lemma prc_changed_payload_is_rejected_by_the_actual_table_lookup:
  "prc_read route 9 prp_changed_payload prc_after_dispatch =
    Some (Observed_Ordinary_Result Collection_Rejected)"
proof -
  have different: "result_payload pro_original_entry \<noteq> prp_changed_payload"
    unfolding pro_original_entry_def product_result_entry.select_convs
    by (rule not_sym[OF prp_changed_payload_is_a_distinct_request])
  have observed: "observe_collection pro_verified 7 (7,1) prp_changed_payload (prc_outcomes prc_after_dispatch) =
    Collection_Rejected"
    by (rule conflicting_payload_is_observably_rejected
        [OF prc_same_epoch_source_entry_and_availability(2) different prc_same_epoch_source_entry_and_availability(3)])
  show ?thesis
    unfolding prc_lookup_passes_the_retained_table_to_the_public_observer
      [OF prc_changed_payload_passes_the_same_typed_identity_gate prc_same_epoch_source_entry_and_availability(3)]
      observed by (rule refl)
qed

lemma prc_removing_only_exact_payload_equality_would_expose_the_retained_reply:
  "prc_read_with_tests
    (9 = cut_authority_epoch (envelope_cut (payload_envelope prp_changed_payload)))
    (\<lambda>_ _. True) 9 prp_changed_payload prc_after_dispatch =
    Some (Observed_Ordinary_Result (Collected pro_original_outcome))"
proof -
  note gate = prc_changed_payload_passes_the_same_typed_identity_gate
  note identity = prc_typed_gate_supplies_the_identity_test[OF gate]
  have access: "result_access_bound pro_verified 7 (7,1) prp_changed_payload (prc_outcomes prc_after_dispatch)"
    by (rule prc_identity_test_supplies_local_result_access[OF identity])
  have ready: "result_completion_ready pro_original_entry (prc_outcomes prc_after_dispatch)"
    by (rule pro_original_reserve_result_needs_no_terminal_publication_to_be_read)
  have outcome: "result_outcome pro_original_entry = pro_original_outcome"
    by (simp add: pro_original_entry_def)
  show ?thesis
    unfolding prc_read_with_tests_def prc_observe_with_payload_test_def
    by (simp only: prc_typed_gate_supplies_the_signed_epoch_test[OF gate] identity access
        prc_same_epoch_source_entry_and_availability(3,2) ready outcome simp_thms option.case if_True if_False)
qed

lemma prc_old_signed_epoch_denies_lookup_at_the_live_reused_session:
  "prc_read route 10 prp_original_payload prc_epoch_settlement = None"
  unfolding prc_lookup_uses_the_exact_two_tests prc_read_with_tests_def prp_original_signed_epoch_is_not_rewritten(1)
  by simp

lemma prc_removing_only_signed_epoch_binding_would_read_the_retained_reply:
  "prc_read_with_tests True (=) 10 prp_original_payload prc_epoch_settlement =
    Some (Observed_Ordinary_Result (Collected pro_original_outcome))"
proof -
  have identity:
    "prp_receipt_without_signed_epoch 10 prp_original_payload (outcome_source (prc_outcomes prc_epoch_settlement))"
    unfolding prc_install_preserves_the_full_outcome_table_and_completed_set(1)
    by (rule prp_removing_only_signed_epoch_binding_reaches_admission)
  have access: "result_access_bound pro_verified 7 (7,1) prp_original_payload (prc_outcomes prc_epoch_settlement)"
    by (rule prc_identity_test_supplies_local_result_access[OF identity])
  have live: "call_local_status (product_calls (outcome_source (prc_outcomes prc_epoch_settlement))) = Endpoint_Up"
    unfolding prc_install_preserves_the_full_outcome_table_and_completed_set(1)
    by (rule prc_reissued_source_is_live)
  have observed: "observe_collection pro_verified 7 (7,1) prp_original_payload (prc_outcomes prc_epoch_settlement) =
    Collected pro_original_outcome"
    by (rule prc_local_observer_reads_the_retained_original_reply
        [OF access live prc_install_keeps_the_original_result_at_the_live_new_epoch(2)])
  show ?thesis
    unfolding prc_read_with_tests_def prc_payload_test_is_the_public_observation
    by (simp only: identity live observed simp_thms if_True)
qed

thm_oracles prc_exact_old_revision_reads_the_actual_original_after_dispatch
  prc_changed_payload_is_rejected_by_the_actual_table_lookup
  prc_removing_only_exact_payload_equality_would_expose_the_retained_reply
  prc_old_signed_epoch_denies_lookup_at_the_live_reused_session
  prc_removing_only_signed_epoch_binding_would_read_the_retained_reply

ML \<open>
  if null (Thm_Deps.all_oracles @{thms prc_exact_old_revision_reads_the_actual_original_after_dispatch
      prc_changed_payload_is_rejected_by_the_actual_table_lookup
      prc_removing_only_exact_payload_equality_would_expose_the_retained_reply
      prc_old_signed_epoch_denies_lookup_at_the_live_reused_session
      prc_removing_only_signed_epoch_binding_would_read_the_retained_reply})
  then writeln "P13_REPLAY_LOOKUP_ORACLES_EMPTY"
  else error "Unexpected oracle in replay lookup"
\<close>

end
