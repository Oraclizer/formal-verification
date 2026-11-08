theory Lock_Accounting
  imports Lock_Product_Run
begin

context source_attestation
begin

theorem initialized_lock_product_conserves_active_and_pending_mass:
  "product_source_mass (core_parent (call_authority_state (product_calls
    (run_lock_product permitted verified maintainers registered actions
      (initial_lock_world balances regulatory contexts durable))))) account = int (balances account)"
proof -
  let ?core = "initial_finality_core balances regulatory contexts"
  let ?world = "initial_lock_world balances regulatory contexts durable"
  let ?product = "run_lock_product permitted verified maintainers registered actions ?world"
  have initial: "product_calls ?world = initial_call_machine ?core"
    by (simp add: initial_lock_world_def)
  obtain word where lifted: "product_calls ?product = finality_calls.run_calls word (product_calls ?world)"
    using lock_product_trace_is_public_word[of permitted verified maintainers registered actions ?world] by blast
  let ?run = "finality_calls.run_calls word (initial_call_machine ?core)"
  have word: "product_calls ?product = ?run"
    using lifted unfolding initial .
  let ?actions = "call_operations (call_authority_log ?run) ?core"
  have actual: "call_authority_state ?run = run_finality ?actions ?core"
    by (rule generated_calls_have_actual_finality_source)
  show ?thesis unfolding word actual product_source_mass_def
    by (rule finality_preserves_source_allocation)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    source_attestation.initialized_lock_product_conserves_active_and_pending_mass
    source_attestation.context_install_invalidates_old_credential
    source_attestation.driver_failure_preserves_authoritative_state
    source_attestation.every_lock_entry_rejects_missing_credential
    source_attestation.every_lock_entry_checks_current_credential
    source_attestation.every_lock_entry_rejects_older_authority_epoch
    source_attestation.every_lock_entry_rejects_replaced_generation})
  then () else error "Unexpected oracle in product lock accounting"
\<close>

end
