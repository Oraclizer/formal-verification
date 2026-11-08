theory Reference_Source_Accounts
  imports Reference_Product_Image
begin

record reference_source_accounts =
  account_holders :: "source_account \<Rightarrow> product_principal set"
  holder_available :: "source_account \<Rightarrow> product_principal \<Rightarrow> nat"

definition source_accounts_match_the_pool where
  "source_accounts_match_the_pool accounts state \<longleftrightarrow>
    (\<forall>key. finite (account_holders accounts key) \<and>
       sum (holder_available accounts key) (account_holders accounts key) = source_units state key \<and>
       (\<forall>who. who \<notin> account_holders accounts key \<longrightarrow> holder_available accounts key who = 0))"

definition debit_reference_account where
  "debit_reference_account payer binding accounts =
    (let key = source_account_of binding; entries = holder_available accounts;
         balances = entries key
     in accounts\<lparr>holder_available := entries
         (key := balances(payer := balances payer - binding_amount binding))\<rparr>)"

lemma debit_of_one_member_decreases_the_sum_by_the_same_amount:
  fixes balances :: "'holder \<Rightarrow> nat"
  assumes finite: "finite holders" and payer: "payer \<in> holders" and enough: "amount \<le> balances payer"
  shows "sum (balances(payer := balances payer - amount)) holders = sum balances holders - amount"
proof -
  have old: "sum balances holders = balances payer + sum balances (holders - {payer})"
    by (rule sum.remove[OF finite payer])
  have rest: "sum (balances(payer := balances payer - amount)) (holders - {payer}) =
      sum balances (holders - {payer})"
    by (rule sum.cong) auto
  have new: "sum (balances(payer := balances payer - amount)) holders =
      (balances payer - amount) + sum balances (holders - {payer})"
    using sum.remove[OF finite payer, of "balances(payer := balances payer - amount)"]
    by (simp add: rest)
  have arithmetic: "(balances payer - amount) + sum balances (holders - {payer}) =
      (balances payer + sum balances (holders - {payer})) - amount"
    by (rule add_diff_assoc2[OF enough])
  show ?thesis using arithmetic by (simp only: old new)
qed

theorem the_exact_payer_debit_matches_the_actual_source_pool_event:
  assumes bound: "source_accounts_match_the_pool accounts state"
    and payer: "payer \<in> account_holders accounts (source_account_of binding)"
    and enough: "binding_amount binding \<le> holder_available accounts (source_account_of binding) payer"
  shows "source_accounts_match_the_pool (debit_reference_account payer binding accounts)
      (apply_reservation_event (Source_Effect_Event binding) state)"
proof -
  let ?key = "source_account_of binding"
  let ?holders = "account_holders accounts ?key"
  let ?amount = "binding_amount binding"
  let ?balances = "holder_available accounts ?key"
  note account_at = spec[OF bound[unfolded source_accounts_match_the_pool_def]]
  have finite: "finite ?holders" and available: "sum ?balances ?holders = source_units state ?key"
    using account_at[of ?key] by blast+
  have exact: "sum (?balances(payer := ?balances payer - ?amount)) ?holders = source_units state ?key - ?amount"
    using debit_of_one_member_decreases_the_sum_by_the_same_amount[where balances="?balances", OF finite payer enough]
      available by simp
  let ?changed = "debit_reference_account payer binding accounts"
  let ?after = "apply_reservation_event (Source_Effect_Event binding) state"
  have per_account: "finite (account_holders ?changed key) \<and>
      sum (holder_available ?changed key) (account_holders ?changed key) = source_units ?after key \<and>
      (\<forall>who. who \<notin> account_holders ?changed key \<longrightarrow> holder_available ?changed key who = 0)" for key
  proof -
    have original: "finite (account_holders accounts key)"
      "sum (holder_available accounts key) (account_holders accounts key) = source_units state key"
      "\<forall>who. who \<notin> account_holders accounts key \<longrightarrow> holder_available accounts key who = 0"
      using account_at[of key] by blast+
    have holders: "account_holders ?changed key = account_holders accounts key"
      by (simp add: debit_reference_account_def Let_def)
    have pool: "sum (holder_available ?changed key) (account_holders ?changed key) = source_units ?after key"
    proof (cases "key = ?key")
      case True
      then show ?thesis using exact
        by (simp add: debit_reference_account_def Let_def set_phase_def)
    next
      case False
      then show ?thesis using original(2)
        by (simp add: debit_reference_account_def Let_def set_phase_def)
    qed
    have outside_zero: "\<forall>who. who \<notin> account_holders ?changed key \<longrightarrow> holder_available ?changed key who = 0"
    proof (intro allI impI)
      fix who
      assume outside: "who \<notin> account_holders ?changed key"
      have zero: "holder_available accounts key who = 0"
        using original(3) outside holders by blast
      have "key \<noteq> ?key \<or> who \<noteq> payer" using payer outside holders by blast
      then show "holder_available ?changed key who = 0"
        using zero by (auto simp: debit_reference_account_def Let_def)
    qed
    show ?thesis using original(1) holders pool outside_zero by simp
  qed
  show ?thesis unfolding source_accounts_match_the_pool_def
    by (intro allI; rule per_account)
qed

lemma an_aggregate_with_enough_units_need_not_fund_the_exact_payer:
  fixes balances :: "product_principal \<Rightarrow> nat"
  assumes "balances 7 = 0" "balances 8 = 10"
  shows "5 \<le> sum balances {7,8}" "\<not> 5 \<le> balances 7"
  using assms by simp_all

record 'head reference_funded_product_image =
  funded_product :: "'head reference_product_image"
  exact_source_accounts :: reference_source_accounts

definition reference_funded_image_is_coherent where
  "reference_funded_image_is_coherent frame \<longleftrightarrow>
    reference_image_views_agree (funded_product frame) \<and>
    source_accounts_match_the_pool (exact_source_accounts frame)
      (snapshot_financial (capture_reference_view (image_authority (funded_product frame))))"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms debit_of_one_member_decreases_the_sum_by_the_same_amount
      the_exact_payer_debit_matches_the_actual_source_pool_event an_aggregate_with_enough_units_need_not_fund_the_exact_payer})
  then () else error "Unexpected oracle in exact source accounts"
\<close>

end
