(* SPDX-License-Identifier: BSD-3-Clause *)
theory Root_Funding_Bounds
  imports "Preemptive_Lock_Correctness.Reservation_Provider"
begin

section \<open>Account Funding Across Finite Source Roots\<close>

definition financial_keys :: "reservation_state \<Rightarrow> source_key set" where
  "financial_keys s =
    set(map binding_key(credit_history(received_messages s))) \<union>
    set(map (binding_key \<circ> lineage_root)(lawful_descendants s))"

lemma finite_financial_keys [simp]: "finite(financial_keys s)"
  by (simp add: financial_keys_def)

lemma sum_history_zero:
  fixes weight :: "'a \<Rightarrow> int"
  assumes "\<forall>x\<in>set history. weight x=0"
  shows "sum_list(map weight history)=0"
  using assms by (induction history) auto

lemma sum_keyed_history:
  fixes weight :: "'a \<Rightarrow> int"
  assumes fin: "finite keys" and cover: "\<forall>x\<in>set history. key x\<in>keys"
  shows "(\<Sum>k\<in>keys. sum_list(map(\<lambda>x. if key x=k then weight x else 0)history)) =
    sum_list(map weight history)"
  using cover
proof (induction history)
  case Nil
  then show ?case by simp
next
  case (Cons x history)
  have member: "key x\<in>keys" using Cons.prems by simp
  have head: "(\<Sum>k\<in>keys. if key x=k then weight x else 0)=weight x"
    using fin member by (simp add: eq_commute)
  have tail: "(\<Sum>k\<in>keys. sum_list(map(\<lambda>x. if key x=k then weight x else 0)history)) =
    sum_list(map weight history)"
    by (rule Cons.IH) (use Cons.prems in auto)
  show ?case by (simp add: sum.distrib head tail)
qed

lemma root_credits_sum_to_destination_credits:
  "(\<Sum>key\<in>financial_keys s. root_credits s key account)=destination_credits s account"
proof -
  have cover: "\<forall>b\<in>set(credit_history(received_messages s)). binding_key b\<in>financial_keys s"
    by (auto simp: financial_keys_def)
  have split: "\<And>b key. (if binding_key b=key \<and> destination_account_of b=account
      then int(binding_amount b) else 0) =
    (if binding_key b=key then (if destination_account_of b=account then int(binding_amount b) else 0) else 0)"
    by auto
  show ?thesis
    unfolding root_credits_def destination_credits_def split
    by (rule sum_keyed_history[OF finite_financial_keys cover])
qed

lemma rooted_deltas_sum_to_destination_deltas:
  "(\<Sum>key\<in>financial_keys s. sum_list(map(\<lambda>e.
      if binding_key(lineage_root e)=key then descendant_delta account e else 0)(lawful_descendants s))) =
    sum_list(map(descendant_delta account)(lawful_descendants s))"
  by (rule sum_keyed_history[OF finite_financial_keys])
     (auto simp: financial_keys_def)

theorem destination_balance_is_sum_of_root_funding:
  assumes inv: "financial_history_agreement balances m"
  shows "(\<Sum>key\<in>financial_keys(machine_state m).
      int(funded_units(machine_state m)(key,account))) =
    int(destination_units(machine_state m)account)"
proof -
  have roots: "\<And>key. int(funded_units(machine_state m)(key,account)) =
    root_credits(machine_state m)key account +
      sum_list(map(\<lambda>e. if binding_key(lineage_root e)=key then descendant_delta account e else 0)
        (lawful_descendants(machine_state m)))"
    using inv unfolding financial_history_agreement_def by blast
  have total: "int(destination_units(machine_state m)account) =
    destination_credits(machine_state m)account +
      sum_list(map(descendant_delta account)(lawful_descendants(machine_state m)))"
    using inv unfolding financial_history_agreement_def by blast
  show ?thesis
    by (simp only: roots sum.distrib root_credits_sum_to_destination_credits
        rooted_deltas_sum_to_destination_deltas total)
qed

lemma funding_outside_financial_keys_is_zero:
  assumes inv: "financial_history_agreement balances m"
    and absent: "key\<notin>financial_keys(machine_state m)"
  shows "funded_units(machine_state m)(key,account)=0"
proof -
  have roots: "\<forall>b\<in>set(credit_history(received_messages(machine_state m))). binding_key b\<noteq>key"
    and effects: "\<forall>e\<in>set(lawful_descendants(machine_state m)). binding_key(lineage_root e)\<noteq>key"
    using absent by (auto simp: financial_keys_def)
  have credit_zero: "root_credits(machine_state m)key account=0"
    unfolding root_credits_def by (rule sum_history_zero) (use roots in auto)
  have delta_zero: "sum_list(map(\<lambda>e. if binding_key(lineage_root e)=key
    then descendant_delta account e else 0)(lawful_descendants(machine_state m)))=0"
    by (rule sum_history_zero) (use effects in auto)
  have exact: "int(funded_units(machine_state m)(key,account)) =
    root_credits(machine_state m)key account +
      sum_list(map(\<lambda>e. if binding_key(lineage_root e)=key
        then descendant_delta account e else 0)(lawful_descendants(machine_state m)))"
    using inv unfolding financial_history_agreement_def by blast
  have "int(funded_units(machine_state m)(key,account))=0"
    using exact by (simp only: credit_zero delta_zero add_0)
  then show ?thesis by simp
qed

theorem root_funding_bounded_by_destination_balance:
  assumes inv: "financial_history_agreement balances m"
  shows "funded_units(machine_state m)(key,account)\<le>destination_units(machine_state m)account"
proof (cases "key\<in>financial_keys(machine_state m)")
  case True
  have split: "(\<Sum>k\<in>financial_keys(machine_state m). int(funded_units(machine_state m)(k,account))) =
    int(funded_units(machine_state m)(key,account)) +
      (\<Sum>k\<in>financial_keys(machine_state m)-{key}. int(funded_units(machine_state m)(k,account)))"
    by (rule sum.remove[OF finite_financial_keys True])
  have nonnegative: "0\<le>(\<Sum>k\<in>financial_keys(machine_state m)-{key}.
    int(funded_units(machine_state m)(k,account)))"
    by (rule sum_nonneg) simp
  note total = destination_balance_is_sum_of_root_funding[OF inv, of account]
  have "int(funded_units(machine_state m)(key,account))\<le>int(destination_units(machine_state m)account)"
    using split nonnegative total by linarith
  then show ?thesis by simp
next
  case False
  show ?thesis by (simp add: funding_outside_financial_keys_is_zero[OF inv False])
qed

lemma single_financial_root_determines_account_funding:
  assumes inv: "financial_history_agreement balances m"
    and only: "financial_keys(machine_state m)\<subseteq>{key}"
  shows "funded_units(machine_state m)(key,account)=destination_units(machine_state m)account"
proof (cases "key\<in>financial_keys(machine_state m)")
  case True
  have exact: "financial_keys(machine_state m)={key}" using only True by auto
  show ?thesis using destination_balance_is_sum_of_root_funding[OF inv,of account]
    by (simp add: exact)
next
  case False
  have empty: "financial_keys(machine_state m)={}" using only False by auto
  show ?thesis using destination_balance_is_sum_of_root_funding[OF inv,of account]
    funding_outside_financial_keys_is_zero[OF inv False,of account] by (simp add: empty)
qed

context source_attestation
begin

theorem reachable_root_funding_bounded_by_destination_balance:
  "funded_units(machine_state(run_reservations balances actions(initial_reservation_machine balances)))(key,account)
    \<le>destination_units(machine_state(run_reservations balances actions(initial_reservation_machine balances)))account"
  by (rule root_funding_bounded_by_destination_balance[OF generated_balances_follow_financial_history])

lemma unresolved_pool_mass_nonnegative: "0\<le>unresolved_pool_mass s pool"
  unfolding unresolved_pool_mass_def binding_mass_def by (rule sum_nonneg) simp

lemma destination_pool_funding_nonnegative: "0\<le>destination_pool_funding s pool"
  unfolding destination_pool_funding_def
  by (rule sum_nonneg) (auto intro: sum_nonneg)

theorem source_pool_destination_funding_bounds:
  assumes contract: "reservation_contract balances m"
  shows "0\<le>destination_pool_funding(machine_state m)pool \<and>
    destination_pool_funding(machine_state m)pool \<le>
      int(balances pool)-int(source_units(machine_state m)pool) \<and>
    int(balances pool)-int(source_units(machine_state m)pool)\<le>int(balances pool)"
  using provider_preserves_source_allocation[OF contract,of pool]
    unresolved_pool_mass_nonnegative[of "machine_state m" pool]
    destination_pool_funding_nonnegative[of "machine_state m" pool]
  by (intro conjI; linarith)

theorem source_pool_funding_equals_spent_allocation_iff:
  assumes contract: "reservation_contract balances m"
  shows "destination_pool_funding(machine_state m)pool =
      int(balances pool)-int(source_units(machine_state m)pool) \<longleftrightarrow>
    unresolved_pool_mass(machine_state m)pool=0"
  using provider_preserves_source_allocation[OF contract,of pool] by linarith

theorem source_pool_funding_equals_genesis_iff:
  assumes contract: "reservation_contract balances m"
  shows "destination_pool_funding(machine_state m)pool=int(balances pool) \<longleftrightarrow>
    source_units(machine_state m)pool=0 \<and> unresolved_pool_mass(machine_state m)pool=0"
  using provider_preserves_source_allocation[OF contract,of pool]
    unresolved_pool_mass_nonnegative[of "machine_state m" pool]
  by (auto; linarith)

end

theorem accepted_descendant_amount_is_root_funded:
  assumes "snd(execute_descendant c r root sender recipient amount m)=Descendant_Executed"
  shows "amount\<le>funded_units(machine_state m)(binding_key root,holder_account root sender)"
  using assms by (auto simp: execute_descendant_def record_observation_def Let_def split: if_splits)

text \<open>Funding is a quantity attributed to an immutable source root.
  Current authorization, regulatory state and an exact spend permission are
  separate inputs to the actual descendant consumer. The allocation bounds
  do not assert that those permissions hold, or that all funded units can be
  spent under a fixed current context. The equality conditions concern zero
  unresolved mass; they do not identify a zero-weight set with an empty set.\<close>

end
