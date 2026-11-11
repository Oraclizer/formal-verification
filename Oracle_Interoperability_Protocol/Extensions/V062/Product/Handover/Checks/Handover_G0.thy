theory Handover_G0
  imports "OIP_V062_Handover_Typed_Model.Handover_Typed_Model"
begin

text \<open>This check stays off the runtime extraction parent chain.\<close>

lemma hg_g0_normal_keeps_pending_and_changes_the_owner:
  "rust_handover_owner (fst (hg_native_step True True)) 17 = Some 8 \<and>
    authoritative_reservation_state (hg_product_after True True) = authoritative_reservation_state hf_source \<and>
    source_units (authoritative_reservation_state (hg_product_after True True)) (0,17) = 5 \<and>
    destination_units (authoritative_reservation_state (hg_product_after True True)) (2,17,3) = 0"
  using hg_normal_native_owner_sessions_epoch_and_immutable_ledger(2)
    hg_product_financial_state_and_phase_are_preserved
    hf_pending_projection_is_derived_without_reading_expected_columns(1,3)
  by simp

lemma hg_g0_missing_consent_and_single_removal:
  "hg_native_step True False = (hg_native_before, False) \<and>
    hg_product_after True False = hf_source \<and>
    snd (hg_without_successor_approval True False)"
  using hg_missing_successor_consent_preserves_the_entire_source
    hg_single_successor_approval_removal_changes_the_same_input
  by simp

lemma hg_g0_old_and_surviving_sessions_are_distinct:
  "\<not> active_identity identity_case_directory (identity_case_user 7) (identity_case_proof 1 9) (hg_product_after True True) \<and>
    active_identity identity_case_directory (identity_case_user 7) (identity_case_proof 2 10) (hg_product_after True True) \<and>
    active_identity identity_case_directory (identity_case_user 8) (identity_case_proof 3 10) (hg_product_after True True)"
  using hg_old_proof_is_rejected_but_the_worker_remains_live by simp

thm_oracles hg_g0_normal_keeps_pending_and_changes_the_owner
  hg_g0_missing_consent_and_single_removal hg_g0_old_and_surviving_sessions_are_distinct

ML \<open>
  if null (Thm_Deps.all_oracles @{thms hg_g0_normal_keeps_pending_and_changes_the_owner
      hg_g0_missing_consent_and_single_removal hg_g0_old_and_surviving_sessions_are_distinct})
  then writeln "HANDOVER_G0_ORACLES_EMPTY"
  else error "Unexpected oracle in the handover G0"
\<close>

end
