theory Replay_Epoch_G0
  imports "OIP_V062_P13_Replay_Epoch_Base.Replay_Epoch_Base"
begin

lemma prp_epoch_g0:
  "active_identity identity_case_directory (identity_case_user 7) (identity_case_proof 1 10) prp_reissued_source \<and>
    \<not> prp_receipt_gate 10 prp_original_payload prp_reissued_source \<and>
    prp_receipt_without_signed_epoch 10 prp_original_payload prp_reissued_source \<and>
    prp_receipt_gate 9 prp_original_payload hf_dispatched"
  using prp_reused_numeric_session_is_current(3) prp_reused_number_does_not_revive_an_old_signed_request
    prp_removing_only_signed_epoch_binding_reaches_admission prp_later_revision_keeps_the_actual_identity_admission
  by simp

thm_oracles prp_epoch_g0

ML \<open>
  if null (Thm_Deps.all_oracles @{thms prp_epoch_g0})
  then writeln "P13_REPLAY_EPOCH_G0_ORACLES_EMPTY"
  else error "Unexpected oracle in P13 Replay G0"
\<close>

end
