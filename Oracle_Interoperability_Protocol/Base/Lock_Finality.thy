theory Lock_Finality
  imports Product_Model
begin

section \<open>Lock fencing at the product commit cut\<close>

record product_lock_credential =
  credential_token :: product_lock_token
  credential_epoch :: nat
  credential_origin :: source_key

definition product_lock_admitted where
  "product_lock_admitted who credential s \<longleftrightarrow>
    token_owner (credential_token credential) = who \<and>
    current_lock_token s (credential_token credential) \<and>
    credential_epoch credential = cut_authority_epoch (current_product_cut s)"

lemma lock_holder_with_current_generation_and_epoch_is_admitted:
  assumes "product_locks (product_durable s) (token_asset token) = Some token"
  shows "product_lock_admitted (token_owner token)
    \<lparr>credential_token = token, credential_epoch = cut_authority_epoch (current_product_cut s),
      credential_origin = origin\<rparr> s"
  using assms by (simp add: product_lock_admitted_def current_lock_token_def)

lemma asset_ownership_cannot_substitute_for_lock_holder:
  "who \<noteq> token_owner (credential_token credential) \<Longrightarrow> \<not> product_lock_admitted who credential s"
  by (simp add: product_lock_admitted_def)

lemma lock_reassignment_fences_the_previous_generation:
  assumes "product_locks (product_durable s) (token_asset (credential_token old)) = Some replacement"
    and "token_generation (credential_token old) < token_generation replacement"
  shows "\<not> product_lock_admitted who old s"
proof -
  have "credential_token old \<noteq> replacement"
    using assms(2) by auto
  with assms(1) show ?thesis
    by (simp add: product_lock_admitted_def current_lock_token_def)
qed

lemma authority_replacement_fences_the_previous_epoch:
  "credential_epoch old < cut_authority_epoch (current_product_cut s) \<Longrightarrow>
    \<not> product_lock_admitted who old s"
  by (auto simp: product_lock_admitted_def)

section \<open>Timeout at the authoritative reservation step\<close>

context source_attestation
begin

definition product_source_mass :: "reservation_machine \<Rightarrow> source_account \<Rightarrow> int" where
  "product_source_mass m account = int (source_units (machine_state m) account) +
    unresolved_pool_mass (machine_state m) account + destination_pool_funding (machine_state m) account"

lemma public_reservation_word_conserves_product_source_mass:
  "product_source_mass (run_reservations balances actions (initial_reservation_machine balances)) account =
    int (balances account)"
  unfolding product_source_mass_def by (rule all_finite_executions_conserve_source_allocations)

theorem timeout_preserves_pending_and_cannot_release_funds:
  "let next = reservation_step balances (Time_Action elapsed) m in
    unresolved_source_obligations (machine_state next) = unresolved_source_obligations (machine_state m) \<and>
    source_units (machine_state next) = source_units (machine_state m) \<and>
    destination_units (machine_state next) = destination_units (machine_state m) \<and>
    reservation_at (machine_state next) = reservation_at (machine_state m)"
  using timeout_retains_unresolved_and_backlog[of elapsed m]
    timeout_has_no_terminal_or_financial_authority[of elapsed m]
  by (simp add: Let_def)

lemma actual_finality_timeout_preserves_pending_and_balances:
  "let next = finality_step (Invoke_Protocol endpoint (core_epoch s) index (Time_Intent elapsed)) s;
       before = machine_state (core_parent s);
       after = machine_state (core_parent next)
   in unresolved_source_obligations after = unresolved_source_obligations before \<and>
      source_units after = source_units before \<and> destination_units after = destination_units before \<and>
      reservation_at after = reservation_at before \<and> core_records next = core_records s"
  using timeout_preserves_pending_and_cannot_release_funds[where m="core_parent s" and elapsed=elapsed]
  by (simp add: Let_def finality_step_def invoke_protocol_def)

lemma actual_delivery_requires_exact_confirmed_evidence:
  assumes "\<not> exact_record_reference s index (request_binding r) Confirmed_Decision (request_certificate r)"
  shows "let result = invoke_protocol endpoint (core_epoch s) index (Deliver_Intent route r) s
    in snd result = Finality_Rejected \<and>
       machine_state (core_parent (fst result)) = machine_state (core_parent s)"
  using assms by (simp add: Let_def invoke_protocol_def reject_protocol_intent_def record_observation_def)

lemma actual_return_requires_exact_reversal_evidence:
  assumes "\<not> exact_record_reference s index (request_binding r) Reversed_Decision (request_certificate r)"
  shows "let result = invoke_protocol endpoint (core_epoch s) index (Return_Intent r g versions) s
    in snd result = Finality_Rejected \<and>
       machine_state (core_parent (fst result)) = machine_state (core_parent s)"
  using assms by (simp add: Let_def invoke_protocol_def reject_protocol_intent_def record_observation_def)

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    lock_holder_with_current_generation_and_epoch_is_admitted
    asset_ownership_cannot_substitute_for_lock_holder
    lock_reassignment_fences_the_previous_generation
    authority_replacement_fences_the_previous_epoch
    source_attestation.public_reservation_word_conserves_product_source_mass
    source_attestation.timeout_preserves_pending_and_cannot_release_funds
    source_attestation.actual_finality_timeout_preserves_pending_and_balances
    source_attestation.actual_delivery_requires_exact_confirmed_evidence
    source_attestation.actual_return_requires_exact_reversal_evidence})
  then () else error "Unexpected oracle in lock and finality proofs"
\<close>

end
