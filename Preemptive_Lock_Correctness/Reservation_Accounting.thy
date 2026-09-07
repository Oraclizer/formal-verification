(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Accounting
  imports Reservation_Message_Link
begin

section \<open>Account Balances and Rooted Financial History\<close>

definition source_debits :: "reservation_state \<Rightarrow> source_account \<Rightarrow> int" where
  "source_debits s account = sum_list(map (\<lambda>b.
    if source_account_of b=account then int(binding_amount b) else 0)(source_effects s))"

fun returned_amount :: "source_account \<Rightarrow> reservation_event \<Rightarrow> int" where
  "returned_amount account (Return_Event b) =
    (if source_account_of b=account then int(binding_amount b) else 0)"
| "returned_amount account _ = 0"

definition destination_credits :: "reservation_state \<Rightarrow> destination_account \<Rightarrow> int" where
  "destination_credits s account = sum_list(map (\<lambda>b.
    if destination_account_of b=account then int(binding_amount b) else 0)
    (credit_history(received_messages s)))"

definition root_credits :: "reservation_state \<Rightarrow> source_key \<Rightarrow> destination_account \<Rightarrow> int" where
  "root_credits s key account = sum_list(map (\<lambda>b.
    if binding_key b=key \<and> destination_account_of b=account then int(binding_amount b) else 0)
    (credit_history(received_messages s)))"

definition descendant_delta :: "destination_account \<Rightarrow> descendant_effect \<Rightarrow> int" where
  "descendant_delta account effect =
    (if holder_account(lineage_root effect)(lineage_to effect)=account then int(lineage_amount effect) else 0) -
    (if holder_account(lineage_root effect)(lineage_from effect)=account then int(lineage_amount effect) else 0)"

definition financial_history_agreement :: "(source_account \<Rightarrow> nat) \<Rightarrow> reservation_machine \<Rightarrow> bool" where
  "financial_history_agreement balances m \<longleftrightarrow>
    (\<forall>account. int(source_units(machine_state m)account)+source_debits(machine_state m)account =
      int(balances account)+sum_list(map(returned_amount account)(machine_journal m))) \<and>
    (\<forall>account. int(destination_units(machine_state m)account)=destination_credits(machine_state m)account+
      sum_list(map(descendant_delta account)(lawful_descendants(machine_state m)))) \<and>
    (\<forall>key account. int(funded_units(machine_state m)(key,account))=root_credits(machine_state m)key account+
      sum_list(map(\<lambda>effect. if binding_key(lineage_root effect)=key then descendant_delta account effect else 0)
        (lawful_descendants(machine_state m))))"

lemma financial_history_initial:
  "financial_history_agreement balances(initial_reservation_machine balances)"
  by (simp add: financial_history_agreement_def initial_reservation_machine_def
      initial_reservation_state_def source_debits_def destination_credits_def root_credits_def empty_message_state_def)

lemma observation_preserves_financial_history [simp]:
  "financial_history_agreement balances(fst(record_observation r reply m))=
    financial_history_agreement balances m"
  by (simp add: financial_history_agreement_def record_observation_def)

lemma descendant_accounting_step:
  assumes inv: "financial_history_agreement balances m"
    and funds: "lineage_amount e\<le>destination_units(machine_state m)(holder_account(lineage_root e)(lineage_from e))"
    and rooted: "lineage_amount e\<le>funded_units(machine_state m)
      (binding_key(lineage_root e),holder_account(lineage_root e)(lineage_from e))"
  shows "financial_history_agreement balances(commit_reservation_event(Descendant_Event e)m)"
  using inv funds rooted
  by (cases "binding_key(lineage_root e)")
     (auto simp: financial_history_agreement_def source_debits_def destination_credits_def root_credits_def
      descendant_delta_def holder_account_def commit_reservation_event_def Let_def of_nat_diff algebra_simps
      split: if_splits)

context source_attestation
begin

theorem reservation_step_preserves_financial_history:
  assumes inv: "financial_history_agreement balances m" and journal: "journal_agreement balances m"
  shows "financial_history_agreement balances(reservation_step balances action m)"
proof (cases action)
  case (Descendant_Action c r root sender recipient amount)
  then show ?thesis using inv
    by (auto simp: execute_descendant_def Let_def
        intro!: descendant_accounting_step)
next
  case Restart_Action
  then show ?thesis using restart_reconstructs_committed_state[OF journal] inv by simp
qed (use inv in \<open>auto simp: protocol_definitions record_observation_def commit_reservation_event_def
  financial_history_agreement_def source_debits_def destination_credits_def root_credits_def
  source_account_of_def destination_account_of_def
  set_phase_def finish_reservation_def Let_def record_credit_def of_nat_diff algebra_simps
  split: option.splits message_reply.splits\<close>)

theorem finite_interleaving_preserves_financial_history:
  assumes "financial_history_agreement balances m" "journal_agreement balances m"
  shows "financial_history_agreement balances(run_reservations balances actions m)"
  using assms by (induction actions arbitrary:m)
    (auto intro: reservation_step_preserves_financial_history reservation_step_preserves_journal)

theorem generated_balances_follow_financial_history:
  "financial_history_agreement balances
    (run_reservations balances actions(initial_reservation_machine balances))"
  by (rule finite_interleaving_preserves_financial_history[OF financial_history_initial initial_journal_agreement])

end

definition financial_accounts :: "reservation_state \<Rightarrow> destination_account set" where
  "financial_accounts s = set(map destination_account_of(credit_history(received_messages s))) \<union>
    (\<Union>e\<in>set(lawful_descendants s).
      {holder_account(lineage_root e)(lineage_from e),holder_account(lineage_root e)(lineage_to e)})"

lemma finite_financial_accounts [simp]: "finite(financial_accounts s)"
  by (simp add: financial_accounts_def)

lemma descendant_delta_sums_to_zero:
  assumes "finite accounts"
    "holder_account(lineage_root e)(lineage_from e)\<in>accounts"
    "holder_account(lineage_root e)(lineage_to e)\<in>accounts"
  shows "(\<Sum>account\<in>accounts. descendant_delta account e)=0"
  using assms by (simp add: descendant_delta_def sum_subtractf)

lemma rooted_descendant_history_sums_to_zero:
  assumes "finite accounts"
    "\<forall>e\<in>set history. holder_account(lineage_root e)(lineage_from e)\<in>accounts \<and>
      holder_account(lineage_root e)(lineage_to e)\<in>accounts"
  shows "(\<Sum>account\<in>accounts. sum_list(map(\<lambda>e.
    if binding_key(lineage_root e)=key then descendant_delta account e else 0)history))=0"
  using assms
proof (induction history)
  case Nil
  then show ?case by simp
next
  case (Cons e history)
  have head: "(\<Sum>account\<in>accounts.
    if binding_key(lineage_root e)=key then descendant_delta account e else 0)=0"
  proof (cases "binding_key(lineage_root e)=key")
    case True
    have "(\<Sum>account\<in>accounts. descendant_delta account e)=0"
      by (rule descendant_delta_sums_to_zero) (use Cons.prems in auto)
    then show ?thesis using True by simp
  next
    case False
    then show ?thesis by simp
  qed
  have tail: "(\<Sum>account\<in>accounts. sum_list(map(\<lambda>e.
    if binding_key(lineage_root e)=key then descendant_delta account e else 0)history))=0"
    by (rule Cons.IH) (use Cons.prems in auto)
  show ?case by (simp add: sum.distrib head tail)
qed

lemma root_credit_history_sum:
  assumes "finite accounts" "\<forall>b\<in>set history. destination_account_of b\<in>accounts"
  shows "(\<Sum>account\<in>accounts. sum_list(map(\<lambda>b.
    if binding_key b=key \<and> destination_account_of b=account then int(binding_amount b) else 0)history))=
    sum_list(map(\<lambda>b. if binding_key b=key then int(binding_amount b) else 0)history)"
  using assms by (induction history) (auto simp: sum.distrib)

theorem all_descendant_funding_of_a_root_is_conserved:
  assumes inv: "financial_history_agreement balances m"
    and finite: "finite accounts"
    and covers: "financial_accounts(machine_state m)\<subseteq>accounts"
  shows "(\<Sum>account\<in>accounts. int(funded_units(machine_state m)(key,account)))=
    sum_list(map(\<lambda>b. if binding_key b=key then int(binding_amount b) else 0)
      (credit_history(received_messages(machine_state m))))"
proof -
  have roots: "\<forall>account. int(funded_units(machine_state m)(key,account))=
    root_credits(machine_state m)key account+
      sum_list(map(\<lambda>e. if binding_key(lineage_root e)=key then descendant_delta account e else 0)
        (lawful_descendants(machine_state m)))"
    using inv unfolding financial_history_agreement_def by blast
  have credit_cover: "\<forall>b\<in>set(credit_history(received_messages(machine_state m))). destination_account_of b\<in>accounts"
    and descendant_cover: "\<forall>e\<in>set(lawful_descendants(machine_state m)).
      holder_account(lineage_root e)(lineage_from e)\<in>accounts \<and>
      holder_account(lineage_root e)(lineage_to e)\<in>accounts"
    using covers unfolding financial_accounts_def by auto
  show ?thesis
    by (simp add: roots sum.distrib root_credits_def
        root_credit_history_sum[OF finite credit_cover]
        rooted_descendant_history_sums_to_zero[OF finite descendant_cover])
qed

text \<open>The identities apply to every account and every source root. They
  record actual accepted effects, including arbitrary onward transfers and
  self-transfers. They do not identify regulatory holding support with token
  quantities. Source returns remain visible in the journal; their uniqueness
  and exclusion from destination settlement require the lifecycle and evidence
  results in addition to these accounting identities.\<close>

end
