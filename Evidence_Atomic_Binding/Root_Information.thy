(* SPDX-License-Identifier: BSD-3-Clause *)
theory Root_Information
  imports Root_Continuation
begin

section \<open>Erasing Lineage While Retaining Every Other State Field\<close>

definition erase_lineage_state :: "reservation_machine \<Rightarrow> reservation_state" where
  "erase_lineage_state m =
    (machine_state m)\<lparr>funded_units:=(\<lambda>_.0),lawful_descendants:=[]\<rparr>"

definition two_holder_continuation :: "reservation_machine \<Rightarrow> reservation_reply" where
  "two_holder_continuation m = snd(execute_descendant(sample_context ACTIVE)
    (spend_request 17 3 1)(sample_binding 17)4 3 1 m)"

lemma lineage_history_is_actual_finite_execution:
  "lineage_history root = sample.run_reservations sample_balances
    ((sample_credit_trace 17@sample_credit_trace 23)@
      [Descendant_Action(sample_context ACTIVE)(spend_request root 4 5)(sample_binding root)3 4 5])
    (initial_reservation_machine sample_balances)"
  by (simp add: lineage_history_def mixed_base_def sample_initial_def sample.reservation_run_append)

lemma lineage_history_supplies_parent_contract:
  "sample.reservation_contract sample_balances(lineage_history root)"
  unfolding lineage_history_is_actual_finite_execution
  by (rule sample.all_finite_executions_supply_the_reservation_contract)

lemma two_roots_two_holders_have_equal_erased_states:
  "erase_lineage_state(lineage_history 17)=erase_lineage_state(lineage_history 23)"
  by (simp add: erase_lineage_state_def lineage_trace_defs)

lemma two_holder_actual_continuation_distinguishes_roots:
  "two_holder_continuation(lineage_history 17)=Descendant_Executed \<and>
    two_holder_continuation(lineage_history 23)=Request_Rejected"
  by (simp add: two_holder_continuation_def lineage_trace_defs)

lemma witness_uses_exactly_two_financial_roots:
  "financial_keys(machine_state(lineage_history 17))={(0,17),(0,23)} \<and>
    financial_keys(machine_state(lineage_history 23))={(0,17),(0,23)}"
  by (simp add: financial_keys_def lineage_trace_defs insert_commute)

lemma witness_uses_exactly_two_holder_accounts:
  "financial_accounts(machine_state(lineage_history 17))={(2,17,3),(2,17,4)} \<and>
    financial_accounts(machine_state(lineage_history 23))={(2,17,3),(2,17,4)}"
  by (simp add: financial_accounts_def lineage_trace_defs insert_commute)

lemma witness_has_equal_pooled_balances_and_different_root_funding:
  "destination_units(machine_state(lineage_history 17))=
      destination_units(machine_state(lineage_history 23)) \<and>
    destination_units(machine_state(lineage_history 17))(2,17,3)=5 \<and>
    destination_units(machine_state(lineage_history 17))(2,17,4)=5 \<and>
    funded_units(machine_state(lineage_history 17))((0,17),(2,17,4))=5 \<and>
    funded_units(machine_state(lineage_history 23))((0,17),(2,17,4))=0"
  by (simp add: lineage_trace_defs)

theorem all_other_reservation_state_fields_do_not_determine_actual_continuation:
  "\<not>(\<exists>decide. \<forall>m\<in>{lineage_history 17,lineage_history 23}.
    decide(erase_lineage_state m)=two_holder_continuation m)"
  using two_roots_two_holders_have_equal_erased_states
    two_holder_actual_continuation_distinguishes_roots by auto

theorem generated_parent_contract_does_not_recover_erased_lineage:
  "\<not>(\<exists>decide. \<forall>m. sample.reservation_contract sample_balances m \<longrightarrow>
    decide(erase_lineage_state m)=two_holder_continuation m)"
proof
  assume "\<exists>decide. \<forall>m. sample.reservation_contract sample_balances m \<longrightarrow>
    decide(erase_lineage_state m)=two_holder_continuation m"
  then obtain decide where determines: "\<And>m. sample.reservation_contract sample_balances m \<Longrightarrow>
    decide(erase_lineage_state m)=two_holder_continuation m" by blast
  have first: "decide(erase_lineage_state(lineage_history 17))=two_holder_continuation(lineage_history 17)"
    by (rule determines[OF lineage_history_supplies_parent_contract])
  have second: "decide(erase_lineage_state(lineage_history 23))=two_holder_continuation(lineage_history 23)"
    by (rule determines[OF lineage_history_supplies_parent_contract])
  have restricted: "\<forall>m\<in>{lineage_history 17,lineage_history 23}.
    decide(erase_lineage_state m)=two_holder_continuation m"
    using first second by auto
  have witness: "\<exists>decide. \<forall>m\<in>{lineage_history 17,lineage_history 23}.
    decide(erase_lineage_state m)=two_holder_continuation m"
    by (rule exI[of _ decide], rule restricted)
  show False using all_other_reservation_state_fields_do_not_determine_actual_continuation witness by blast
qed

lemma funded_quantity_does_not_supply_current_spend_permission:
  "funded_units(machine_state(lineage_history 17))((0,17),(2,17,4))=5 \<and>
    snd(execute_descendant((sample_context ACTIVE)\<lparr>lock_spend_permissions:={}\<rparr>)
      (spend_request 17 3 1)(sample_binding 17)4 3 1(lineage_history 17))=Request_Rejected"
  by (simp add: lineage_trace_defs)

section \<open>Restricted Cases in Which the Ambiguity Disappears\<close>

lemma erased_state_equality_preserves_pooled_balances:
  assumes same: "erase_lineage_state m=erase_lineage_state n"
  shows "destination_units(machine_state m)=destination_units(machine_state n)"
  using arg_cong[OF same,where f=destination_units]
  by (simp add: erase_lineage_state_def)

theorem one_financial_root_suffices_for_the_actual_consumer:
  assumes first: "financial_history_agreement balances m"
    and second: "financial_history_agreement balances n"
    and credit_first: "b\<in>set(credit_history(received_messages(machine_state m)))"
    and credit_second: "b\<in>set(credit_history(received_messages(machine_state n)))"
    and one_first: "financial_keys(machine_state m)\<subseteq>{binding_key b}"
    and one_second: "financial_keys(machine_state n)\<subseteq>{binding_key b}"
    and same: "erase_lineage_state m=erase_lineage_state n"
  shows "snd(execute_descendant c r b sender recipient amount m)=
    snd(execute_descendant c r b sender recipient amount n)"
proof -
  have pooled: "destination_units(machine_state m)=destination_units(machine_state n)"
    by (rule erased_state_equality_preserves_pooled_balances[OF same])
  have funding: "\<forall>account. funded_units(machine_state m)(binding_key b,account)=
    funded_units(machine_state n)(binding_key b,account)"
    using single_financial_root_determines_account_funding[OF first one_first]
      single_financial_root_determines_account_funding[OF second one_second] pooled by simp
  show ?thesis
    by (rule equal_credited_root_funding_preserves_actual_descendant_reply[
      OF first second credit_first credit_second funding])
qed

lemma funding_outside_financial_accounts_is_zero:
  assumes financial: "financial_history_agreement balances m"
    and absent: "account\<notin>financial_accounts(machine_state m)"
  shows "funded_units(machine_state m)(key,account)=0"
proof -
  have credits: "\<forall>b\<in>set(credit_history(received_messages(machine_state m))).
    destination_account_of b\<noteq>account"
    and descendants: "\<forall>e\<in>set(lawful_descendants(machine_state m)).
      holder_account(lineage_root e)(lineage_from e)\<noteq>account \<and>
      holder_account(lineage_root e)(lineage_to e)\<noteq>account"
    using absent by (auto simp: financial_accounts_def)
  have credit_zero: "root_credits(machine_state m)key account=0"
    unfolding root_credits_def by (rule sum_history_zero) (use credits in auto)
  have delta_zero: "sum_list(map(\<lambda>e. if binding_key(lineage_root e)=key
    then descendant_delta account e else 0)(lawful_descendants(machine_state m)))=0"
    by (rule sum_history_zero) (use descendants in \<open>auto simp: descendant_delta_def\<close>)
  have exact: "int(funded_units(machine_state m)(key,account)) =
    root_credits(machine_state m)key account +
      sum_list(map(\<lambda>e. if binding_key(lineage_root e)=key
        then descendant_delta account e else 0)(lawful_descendants(machine_state m)))"
    using financial unfolding financial_history_agreement_def by blast
  have "int(funded_units(machine_state m)(key,account))=0"
    using exact by (simp only: credit_zero delta_zero add_0)
  then show ?thesis by simp
qed

context source_attestation
begin

lemma one_holder_account_determines_credited_root_funding:
  assumes financial: "financial_history_agreement balances m"
    and messages: "message_invariant(received_messages(machine_state m))"
    and credit: "b\<in>set(credit_history(received_messages(machine_state m)))"
    and one: "financial_accounts(machine_state m)\<subseteq>{account}"
  shows "funded_units(machine_state m)(binding_key b,query)=
    (if query=account then binding_amount b else 0)"
proof -
  have member: "destination_account_of b\<in>financial_accounts(machine_state m)"
    using credit by (auto simp: financial_accounts_def)
  have exact: "financial_accounts(machine_state m)={account}" using member one by auto
  have at: "funded_units(machine_state m)(binding_key b,account)=binding_amount b"
    using credited_root_preserves_its_exact_funding[OF financial messages credit]
    by (simp add: exact)
  show ?thesis
  proof (cases "query=account")
    case True
    then show ?thesis by (simp add: at)
  next
    case False
    have absent: "query\<notin>financial_accounts(machine_state m)" by (simp add: exact False)
    show ?thesis using funding_outside_financial_accounts_is_zero[OF financial absent,of "binding_key b"]
      by (simp add: False)
  qed
qed

theorem one_holder_account_suffices_for_the_actual_consumer:
  assumes first: "reservation_contract balances m"
    and second: "reservation_contract balances n"
    and credit_first: "b\<in>set(credit_history(received_messages(machine_state m)))"
    and credit_second: "b\<in>set(credit_history(received_messages(machine_state n)))"
    and one_first: "financial_accounts(machine_state m)\<subseteq>{account}"
    and one_second: "financial_accounts(machine_state n)\<subseteq>{account}"
  shows "snd(execute_descendant c r b sender recipient amount m)=
    snd(execute_descendant c r b sender recipient amount n)"
proof -
  have financial_first: "financial_history_agreement balances m"
    and financial_second: "financial_history_agreement balances n"
    and messages_first: "message_invariant(received_messages(machine_state m))"
    and messages_second: "message_invariant(received_messages(machine_state n))"
    using first second unfolding reservation_contract_def message_source_invariant_def by blast+
  have funding: "\<forall>query. funded_units(machine_state m)(binding_key b,query)=
    funded_units(machine_state n)(binding_key b,query)"
    using one_holder_account_determines_credited_root_funding[
      OF financial_first messages_first credit_first one_first]
      one_holder_account_determines_credited_root_funding[
      OF financial_second messages_second credit_second one_second] by simp
  show ?thesis
    by (rule equal_credited_root_funding_preserves_actual_descendant_reply[
      OF financial_first financial_second credit_first credit_second funding])
qed

end

section \<open>Complete Journals Retain the Missing Information\<close>

lemma complete_journal_recovers_each_witness:
  "restart_reservation_machine sample_balances
    ((lineage_history root)\<lparr>machine_state:=lost_cache\<rparr>)=lineage_history root"
  by (rule complete_journal_recovers_arbitrary_cache_loss[OF lineage_history_journal])

lemma complete_journal_preserves_the_distinguishing_actual_consumer:
  "two_holder_continuation(restart_reservation_machine sample_balances
      ((lineage_history root)\<lparr>machine_state:=lost_cache\<rparr>)) =
    two_holder_continuation(lineage_history root)"
  by (simp only: complete_journal_recovers_each_witness)

text \<open>The erasure returns only a reservation state. It retains all of
  that record except funding and descendant history, but it does not retain
  the machine's financial journal. A complete journal therefore supplies a
  different observation and recovers the distinguishing consumer normally.
  The two-root, two-account witness and the restricted one-root and one-account
  theorems establish the stated cardinality boundary for this ambiguity.
  They do not claim a globally minimal trace, a sufficient representation for
  every action family, or an inverse realization theorem for arbitrary records.\<close>

end
