theory Replay_Receipt_Install
  imports "OIP_V062_P13_Replay_Stored_Outcome_Repair.Replay_Stored_Outcome"
begin

definition prc_outcomes :: "settlement_world \<Rightarrow> outcome_world" where
  "prc_outcomes s = origin_outcomes (settlement_primary s)"

definition prc_settlement :: "outcome_world \<Rightarrow> settlement_world" where
  "prc_settlement s = update_settlement_outcomes s
    (initial_settlement_world 2 (initial_origin_world (outcome_source s)))"

definition prc_epoch_settlement :: settlement_world where
  "prc_epoch_settlement = sample.exact_step (\<lambda>_ _ _. False) pro_verified
    ({7}::nat set) {0,2} (\<lambda>_. False)
    (Exact_Install 7 10 (transfer_contexts hg_proposal) (hf_sessions 10))
    (prc_settlement pro_completed)"

definition prc_world :: "settlement_world \<Rightarrow> regulated_product_world" where
  "prc_world s = initial_regulated_product (initial_product_reads 1 s)"

lemma prc_outcome_update_supplies_the_given_outcomes:
  "prc_outcomes (update_settlement_outcomes outcomes s) = outcomes"
  by (simp add: prc_outcomes_def update_settlement_outcomes_def)

lemma prc_settlement_contains_the_actual_outcomes:
  "prc_outcomes (prc_settlement outcomes) = outcomes"
  unfolding prc_settlement_def by (rule prc_outcome_update_supplies_the_given_outcomes)

lemma prc_identity_source_is_the_actual_outcome_source:
  "identity_source (prc_world s) = outcome_source (prc_outcomes s)"
  by (simp add: prc_world_def prc_outcomes_def identity_source_def observed_product_source_def
      regulated_read_world_def initial_regulated_product_def initial_governed_world_def
      initial_legal_world_def initial_product_reads_def)

lemma prc_ordinary_receipt_reads_the_actual_outcome_table:
  "legal_underlying_outcomes (governed_legal (regulated_orders (prc_world s))) = prc_outcomes s"
  by (simp add: prc_world_def prc_outcomes_def legal_underlying_outcomes_def
      initial_regulated_product_def initial_governed_world_def
      initial_legal_world_def initial_product_reads_def)

lemma prc_install_reissues_the_source_of_the_retained_outcomes:
  "prc_outcomes prc_epoch_settlement = pro_completed\<lparr>outcome_source := prp_reissued_source\<rparr>"
proof -
  let ?old = "prc_settlement pro_completed"
  let ?action = "Lock_Install 7 10 (transfer_contexts hg_proposal) (hf_sessions 10)"
  have before: "origin_outcomes (settlement_primary ?old) = pro_completed"
    using prc_settlement_contains_the_actual_outcomes[of pro_completed]
    by (simp only: prc_outcomes_def)
  have step: "sample.lock_product_step (\<lambda>_ _ _. False) (\<lambda>_ _ _ _. True)
    ({7}::nat set) {0,2} ?action (outcome_source pro_completed) = prp_reissued_source"
    unfolding pro_completed_retains_the_produced_source_and_entry(1) prp_reissued_source_def
    by (simp only: sample.lock_product_step.simps(2))
  show ?thesis
    unfolding prc_epoch_settlement_def sample.exact_step.simps(3) sample.apply_non_submit_lock_action_def
      Let_def before step
    by (rule prc_outcome_update_supplies_the_given_outcomes)
qed

lemma prc_install_preserves_the_full_outcome_table_and_completed_set:
  "outcome_source (prc_outcomes prc_epoch_settlement) = prp_reissued_source"
  "outcome_entries (prc_outcomes prc_epoch_settlement) = outcome_entries pro_completed"
  "outcome_completed (prc_outcomes prc_epoch_settlement) = outcome_completed pro_completed"
  unfolding prc_install_reissues_the_source_of_the_retained_outcomes by simp_all

lemma prc_reissued_source_is_live:
  "call_local_status (product_calls prp_reissued_source) = Endpoint_Up"
proof -
  have status:
    "call_local_status (sample.finality_calls.run_calls (map Apply_Authority_Input changes) calls) =
      call_local_status calls" for changes calls
    by (induction changes arbitrary: calls)
      (simp_all add: sample.finality_calls.apply_authority_input_def Let_def)
  have reissued:
    "product_calls prp_reissued_source =
      sample.finality_calls.run_calls (map Apply_Authority_Input (transfer_contexts hg_proposal))
        (product_calls hf_reserved)"
    by (simp add: prp_reissued_source_def prp_context_install_has_the_actual_new_epoch sample.product_apply_public_def)
  show ?thesis unfolding reissued status by (rule pro_reserved_endpoint_is_up)
qed

lemma prc_install_keeps_the_original_result_at_the_live_new_epoch:
  "active_identity identity_case_directory (identity_case_user 7) (identity_case_proof 1 10)
    (identity_source (prc_world prc_epoch_settlement))"
  "outcome_entries (prc_outcomes prc_epoch_settlement) (7,1) = Some pro_original_entry"
proof -
  show "active_identity identity_case_directory (identity_case_user 7) (identity_case_proof 1 10)
    (identity_source (prc_world prc_epoch_settlement))"
    unfolding prc_identity_source_is_the_actual_outcome_source prc_install_preserves_the_full_outcome_table_and_completed_set(1)
    by (rule prp_reused_numeric_session_is_current(3))
  show "outcome_entries (prc_outcomes prc_epoch_settlement) (7,1) = Some pro_original_entry"
    unfolding prc_install_preserves_the_full_outcome_table_and_completed_set(2)
    by (rule pro_completed_retains_the_produced_source_and_entry(2))
qed

thm_oracles prc_install_preserves_the_full_outcome_table_and_completed_set
  prc_install_keeps_the_original_result_at_the_live_new_epoch prc_reissued_source_is_live

ML \<open>
  if null (Thm_Deps.all_oracles @{thms prc_install_preserves_the_full_outcome_table_and_completed_set
      prc_install_keeps_the_original_result_at_the_live_new_epoch prc_reissued_source_is_live})
  then writeln "P13_REPLAY_INSTALL_ORACLES_EMPTY"
  else error "Unexpected oracle in replay installation"
\<close>

end
