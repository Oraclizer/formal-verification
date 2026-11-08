theory Reference_Lock_Consumption
  imports Reference_Authority_Trace
begin

definition reference_lock_source where
  "reference_lock_source connection snapshot =
    identity_source (reopen_retained_product connection (reference_product snapshot))"

context source_attestation
begin

definition reference_submit_lock where
  "reference_submit_lock verified entry actor call_id envelope credential connection snapshot =
    submit_lock_entry (reference_permitted_at (reference_inputs snapshot)) verified
       entry actor call_id envelope credential (reference_lock_source connection snapshot)"

theorem a_reference_lock_effect_consumes_current_grants_and_the_exact_credential:
  assumes required: "command_lock_request (envelope_command envelope) = Some (request, generation)"
    and changed: "reference_submit_lock verified entry actor call_id envelope (Some credential)
       connection snapshot \<noteq> reference_lock_source connection snapshot"
  shows "reference_permitted_at (reference_inputs snapshot) entry actor (envelope_command envelope)"
    "lock_credential_matches actor credential request generation (reference_lock_source connection snapshot)"
proof -
  show "reference_permitted_at (reference_inputs snapshot) entry actor (envelope_command envelope)"
    using changed by (auto simp: reference_submit_lock_def submit_lock_entry_def lock_submission_allowed_def split: if_splits)
  show "lock_credential_matches actor credential request generation (reference_lock_source connection snapshot)"
    using required changed unfolding reference_submit_lock_def
    by (rule every_lock_entry_checks_current_credential)
qed

lemma an_old_credential_cannot_change_the_reference_lock_source:
  assumes "credential_epoch old < cut_authority_epoch (current_product_cut (reference_lock_source connection snapshot))"
  shows "reference_submit_lock verified entry actor call_id envelope (Some old) connection snapshot =
    reference_lock_source connection snapshot"
  unfolding reference_submit_lock_def
  by (rule every_lock_entry_rejects_older_authority_epoch[OF assms])

lemma a_replaced_generation_cannot_change_the_reference_lock_source:
  assumes "authoritative_lock_token (reference_lock_source connection snapshot) (token_asset (credential_token old)) = Some current"
    "token_generation (credential_token old) < token_generation current"
  shows "reference_submit_lock verified entry actor call_id envelope (Some old) connection snapshot =
    reference_lock_source connection snapshot"
  unfolding reference_submit_lock_def
  by (rule every_lock_entry_rejects_replaced_generation[OF assms])

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.a_reference_lock_effect_consumes_current_grants_and_the_exact_credential
      source_attestation.an_old_credential_cannot_change_the_reference_lock_source
      source_attestation.a_replaced_generation_cannot_change_the_reference_lock_source})
  then () else error "Unexpected oracle in reference lock consumption"
\<close>

end
