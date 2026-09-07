(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Conservation
  imports Reservation_Return_History
begin

section \<open>Conserved Source Allocations Through Settlement and Onward Use\<close>

definition binding_mass :: "source_account \<Rightarrow> transfer_binding \<Rightarrow> int" where
  "binding_mass account b=(if source_account_of b=account then int(binding_amount b) else 0)"

lemma injective_key_selects_exact_weight:
  fixes weight :: "'a \<Rightarrow> int"
  assumes finite: "finite entries" and injective: "inj_on key entries" and member: "entry\<in>entries"
  shows "(\<Sum>x\<in>entries. if key x=key entry then weight x else 0)=weight entry"
proof -
  have "(\<Sum>x\<in>entries. if key x=key entry then weight x else 0)=
    (\<Sum>x\<in>entries. if x=entry then weight entry else 0)"
  proof (rule sum.cong[OF refl])
    fix x
    assume x: "x\<in>entries"
    have eq: "key x=key entry \<longleftrightarrow> x=entry"
    proof
      assume same: "key x=key entry"
      show "x=entry" by (rule inj_onD[OF injective same x member])
    next
      assume "x=entry"
      then show "key x=key entry" by simp
    qed
    show "(if key x=key entry then weight x else 0)=(if x=entry then weight entry else 0)"
      by (simp add: eq)
  qed
  also have "...=weight entry" using finite member by simp
  finally show ?thesis .
qed

context source_attestation
begin

theorem credited_root_preserves_its_exact_funding:
  assumes financial: "financial_history_agreement balances m"
    and messages: "message_invariant(received_messages(machine_state m))"
    and credit: "b\<in>set(credit_history(received_messages(machine_state m)))"
  shows "(\<Sum>account\<in>financial_accounts(machine_state m).
    int(funded_units(machine_state m)(binding_key b,account)))=int(binding_amount b)"
proof -
  let ?credits = "credit_history(received_messages(machine_state m))"
  have unique: "distinct(map binding_key ?credits)"
    using messages unfolding message_invariant_def by blast
  have distinct: "distinct ?credits" by (rule conjunct1[OF unique[unfolded distinct_map]])
  have injective: "inj_on binding_key(set ?credits)" using unique by (simp add: distinct_map)
  have rooted: "(\<Sum>account\<in>financial_accounts(machine_state m).
      int(funded_units(machine_state m)(binding_key b,account)))=
    sum_list(map(\<lambda>entry. if binding_key entry=binding_key b then int(binding_amount entry) else 0)?credits)"
    by (rule all_descendant_funding_of_a_root_is_conserved[OF financial]) simp_all
  show ?thesis
    using rooted injective_key_selects_exact_weight[OF finite_set injective credit,
      where weight="\<lambda>entry. int(binding_amount entry)"]
    by (simp add: sum_list_distinct_conv_sum_set[OF distinct])
qed

definition unresolved_pool_mass :: "reservation_state \<Rightarrow> source_account \<Rightarrow> int" where
  "unresolved_pool_mass s account=(\<Sum>b\<in>unresolved_source_obligations s. binding_mass account b)"

definition destination_pool_funding :: "reservation_state \<Rightarrow> source_account \<Rightarrow> int" where
  "destination_pool_funding s account=(\<Sum>b\<in>set(credit_history(received_messages s)).
    if source_account_of b=account
    then (\<Sum>holder\<in>financial_accounts s. int(funded_units s(binding_key b,holder))) else 0)"

lemma destination_pool_funding_is_credit_mass:
  assumes financial: "financial_history_agreement balances m"
    and messages: "message_invariant(received_messages(machine_state m))"
  shows "destination_pool_funding(machine_state m)account=
    (\<Sum>b\<in>set(credit_history(received_messages(machine_state m))). binding_mass account b)"
  unfolding destination_pool_funding_def
proof (rule sum.cong[OF refl])
  fix b
  assume "b\<in>set(credit_history(received_messages(machine_state m)))"
  then have "(\<Sum>holder\<in>financial_accounts(machine_state m).
    int(funded_units(machine_state m)(binding_key b,holder)))=int(binding_amount b)"
    by (rule credited_root_preserves_its_exact_funding[OF financial messages])
  then show "(if source_account_of b=account
    then (\<Sum>holder\<in>financial_accounts(machine_state m).
      int(funded_units(machine_state m)(binding_key b,holder))) else 0)=binding_mass account b"
    by (simp add: binding_mass_def)
qed

theorem source_pool_mass_is_conserved:
  assumes financial: "financial_history_agreement balances m"
    and unique: "source_history_unique(machine_state m)"
    and messages: "message_source_invariant(machine_state m)"
    and life: "source_lifecycle_consistent(machine_state m)"
    and settlement: "settlement_records_consistent(machine_state m)"
    and returns: "return_history_agreement m"
  shows "int(source_units(machine_state m)account)+unresolved_pool_mass(machine_state m)account+
    destination_pool_funding(machine_state m)account=int(balances account)"
proof -
  let ?s = "machine_state m"
  let ?U = "unresolved_source_obligations ?s"
  let ?C = "set(credit_history(received_messages ?s))"
  let ?R = "returned_source_bindings ?s"
  have source_key_unique: "distinct(map binding_key(source_effects ?s))"
    using unique by (simp only: source_history_unique_def)
  have source_distinct: "distinct(source_effects ?s)"
    by (rule conjunct1[OF source_key_unique[unfolded distinct_map]])
  have message_inv: "message_invariant(received_messages ?s)" and origin: "credited_source_origin ?s"
    using messages unfolding message_source_invariant_def by blast+
  have partition: "set(source_effects ?s)=?U\<union>?C\<union>?R"
    by (rule source_effects_have_exact_settlement_partition[OF origin])
  have finiteU: "finite ?U" and finiteR: "finite ?R"
    by (simp_all add: unresolved_source_obligations_def returned_source_bindings_def)
  have UC: "?U\<inter>?C={}" by (rule unresolved_and_completed_credit_are_disjoint)
  have UR: "?U\<inter>?R={}" by (rule unresolved_and_returned_are_disjoint)
  have CR: "?C\<inter>?R={}" by (rule completed_credit_and_returned_are_disjoint[OF settlement message_inv])
  have all_R: "(?U\<union>?C)\<inter>?R={}" using UR CR by blast
  have split_mass: "(\<Sum>b\<in>set(source_effects ?s). binding_mass account b)=
    (\<Sum>b\<in>?U. binding_mass account b)+(\<Sum>b\<in>?C. binding_mass account b)+
    (\<Sum>b\<in>?R. binding_mass account b)"
    by (simp only: partition sum.union_disjoint[OF finite_UnI[OF finiteU finite_set] finiteR all_R]
        sum.union_disjoint[OF finiteU finite_set UC])
  have debit_mass: "source_debits ?s account=(\<Sum>b\<in>set(source_effects ?s). binding_mass account b)"
    by (simp add: source_debits_def binding_mass_def sum_list_distinct_conv_sum_set[OF source_distinct])
  have return_mass: "sum_list(map(returned_amount account)(machine_journal m))=
    (\<Sum>b\<in>?R. binding_mass account b)"
    using source_return_journal_has_exact_set_amount[OF returns life,of account]
    by (simp add: binding_mass_def)
  have balance: "int(source_units ?s account)+source_debits ?s account=int(balances account)+
    sum_list(map(returned_amount account)(machine_journal m))"
    using financial unfolding financial_history_agreement_def by blast
  have funding: "destination_pool_funding ?s account=(\<Sum>b\<in>?C. binding_mass account b)"
    by (rule destination_pool_funding_is_credit_mass[OF financial message_inv])
  show ?thesis using balance split_mass debit_mass return_mass funding
    unfolding unresolved_pool_mass_def by linarith
qed

theorem all_finite_executions_conserve_source_allocations:
  fixes balances :: "source_account \<Rightarrow> nat" and actions :: "reservation_action list"
  defines "m \<equiv> run_reservations balances actions(initial_reservation_machine balances)"
  shows "int(source_units(machine_state m)account)+unresolved_pool_mass(machine_state m)account+
    destination_pool_funding(machine_state m)account=int(balances account)"
proof (rule source_pool_mass_is_conserved)
  show "financial_history_agreement balances m"
    unfolding m_def by (rule generated_balances_follow_financial_history)
  show "source_history_unique(machine_state m)"
    unfolding m_def
  proof (rule finite_interleaving_preserves_source_uniqueness)
    show "source_history_unique(machine_state(initial_reservation_machine balances))"
      by (simp add: initial_reservation_machine_def source_history_initial)
    show "journal_agreement balances(initial_reservation_machine balances)"
      by (rule initial_journal_agreement)
  qed
  show "message_source_invariant(machine_state m)"
    unfolding m_def by (rule generated_message_source_invariant)
  show "source_lifecycle_consistent(machine_state m)"
    unfolding m_def by (rule generated_source_lifecycle)
  show "settlement_records_consistent(machine_state m)"
    unfolding m_def by (rule generated_settlement_records)
  show "return_history_agreement m"
    unfolding m_def by (rule generated_return_history)
qed

text \<open>The sums range over the finite roots and destination accounts that
  actually occur in the run. A credited root contributes its current funding
  across all holders, including lawful onward effects. Returned source funds
  appear in the source balance, unresolved obligations in the pending term,
  and credited funds in the destination term. Reconciliation lag is not counted
  again as pending mass. The equality is per source allocation pool and does
  not require finite total genesis supply across all possible accounts.\<close>

end

end
