(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Provider
  imports Reservation_Conservation Reservation_Recovery Reservation_Access Reservation_Progress
begin

section \<open>A Proved Contract for the Next Protocol Layer\<close>

context source_attestation
begin

definition reservation_contract :: "(source_account \<Rightarrow> nat) \<Rightarrow> reservation_machine \<Rightarrow> bool" where
  "reservation_contract balances m \<longleftrightarrow>
    journal_agreement balances m \<and> ownership_consistent(machine_state m) \<and>
    source_history_unique(machine_state m) \<and> message_source_invariant(machine_state m) \<and>
    source_lifecycle_consistent(machine_state m) \<and> settlement_records_consistent(machine_state m) \<and>
    financial_history_agreement balances m \<and> return_history_agreement m"

theorem initial_reservation_contract:
  "reservation_contract balances(initial_reservation_machine balances)"
  unfolding reservation_contract_def
  using initial_journal_agreement[of balances] financial_history_initial[of balances]
    return_history_initial[of balances]
  by (simp add: initial_reservation_machine_def ownership_initial source_history_initial
      message_source_initial initial_source_lifecycle settlement_records_initial)

theorem actual_step_preserves_reservation_contract:
  assumes "reservation_contract balances m"
  shows "reservation_contract balances(reservation_step balances action m)"
  using assms unfolding reservation_contract_def
  by (intro conjI)
     (blast intro: reservation_step_preserves_journal reservation_step_preserves_ownership
       reservation_step_preserves_source_uniqueness reservation_step_preserves_message_source
       reservation_step_preserves_source_lifecycle reservation_step_preserves_settlement_records
       reservation_step_preserves_financial_history reservation_step_preserves_return_history)+

theorem finite_execution_preserves_reservation_contract:
  assumes "reservation_contract balances m"
  shows "reservation_contract balances(run_reservations balances actions m)"
  using assms by (induction actions arbitrary:m)
    (auto intro: actual_step_preserves_reservation_contract)

theorem all_finite_executions_supply_the_reservation_contract:
  "reservation_contract balances(run_reservations balances actions(initial_reservation_machine balances))"
  by (rule finite_execution_preserves_reservation_contract[OF initial_reservation_contract])

theorem reservation_contract_instantiates_guarded_invariance:
  "guarded_invariant UNIV (\<lambda>m action. Some(reservation_step balances action m)) UNIV
    (reservation_contract balances) (\<lambda>m action. True)"
proof unfold_locales
  fix m action after
  assume "m\<in>UNIV" "action\<in>UNIV" "Some(reservation_step balances action m)=Some after"
  then show "after\<in>UNIV" by simp
next
  fix m action after
  assume "m\<in>UNIV" "action\<in>UNIV" "reservation_contract balances m" "True"
    "Some(reservation_step balances action m)=Some after"
  then show "reservation_contract balances after"
    by (auto intro: actual_step_preserves_reservation_contract)
qed

theorem provider_preserves_source_allocation:
  assumes "reservation_contract balances m"
  shows "int(source_units(machine_state m)account)+unresolved_pool_mass(machine_state m)account+
    destination_pool_funding(machine_state m)account=int(balances account)"
  by (rule source_pool_mass_is_conserved)
     (use assms in \<open>auto simp: reservation_contract_def\<close>)

theorem provider_recovers_actual_continuations:
  assumes "reservation_contract balances m"
  shows "run_reservations balances continuation
    (restart_reservation_machine balances(m\<lparr>machine_state:=lost_cache\<rparr>))=
    run_reservations balances continuation m"
  by (rule complete_journal_preserves_actual_continuations_after_cache_loss)
     (use assms in \<open>simp add: reservation_contract_def\<close>)

text \<open>The next protocol layer receives the actual action datatype,
  execution function, computed evidence checks, immutable source identity,
  current worker/version guards, financial lineage and complete-journal replay.
  The contract is proved from initialization and closed under those operations;
  it is not an uninterpreted release-safety oracle. The guarded-invariant
  interpretation uses the existing composition interface with an unbounded
  carrier. Its outer guard is True because each actual step already evaluates
  its internal checks and completes rejected requests without an effect.

  The interface does not supply independent terminal consensus, an externally
  controlled source-effect producer, an atomicity abstraction for raw observers,
  a theorem that every normal form is realizable, or runtime durability. Those
  producer and refinement obligations remain with subsequent protocol and
  implementation work. The interface packaging itself is not counted as new
  mathematical novelty.\<close>

end

end
