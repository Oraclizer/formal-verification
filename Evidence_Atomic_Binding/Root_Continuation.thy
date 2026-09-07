(* SPDX-License-Identifier: BSD-3-Clause *)
theory Root_Continuation
  imports Root_Funding_Bounds
begin

section \<open>Frames for an Already Credited Source Root\<close>

definition root_snapshot :: "source_key \<Rightarrow> reservation_state \<Rightarrow>
  (destination_account \<Rightarrow> nat) \<times> descendant_effect list" where
  "root_snapshot key s = ((\<lambda>account. funded_units s(key,account)),
    filter(\<lambda>e. binding_key(lineage_root e)=key)(lawful_descendants s))"

fun avoids_root :: "source_key \<Rightarrow> reservation_action \<Rightarrow> bool" where
  "avoids_root key (Descendant_Action c r root sender recipient amount) = (binding_key root\<noteq>key)"
| "avoids_root key _ = True"

fun event_avoids_root :: "source_key \<Rightarrow> reservation_event \<Rightarrow> bool" where
  "event_avoids_root key (Credit_Event b) = (binding_key b\<noteq>key)"
| "event_avoids_root key (Descendant_Event e) = (binding_key(lineage_root e)\<noteq>key)"
| "event_avoids_root key _ = True"

lemma event_preserves_avoided_root:
  assumes "event_avoids_root key event"
  shows "root_snapshot key(apply_reservation_event event s)=root_snapshot key s"
  using assms by (cases event)
    (auto simp: root_snapshot_def set_phase_def finish_reservation_def Let_def fun_eq_iff)

lemma observation_preserves_root_snapshot [simp]:
  "root_snapshot key(machine_state(fst(record_observation r reply m)))=root_snapshot key(machine_state m)"
  by (simp add: record_observation_def)

lemma commit_preserves_avoided_root:
  "event_avoids_root key event \<Longrightarrow>
    root_snapshot key(machine_state(commit_reservation_event event m))=root_snapshot key(machine_state m)"
  by (simp add: commit_reservation_event_def event_preserves_avoided_root)

lemma event_preserves_existing_credit:
  assumes "b\<in>set(credit_history(received_messages s))"
  shows "b\<in>set(credit_history(received_messages(apply_reservation_event event s)))"
  using assms by (cases event)
    (auto simp: set_phase_def finish_reservation_def record_credit_def Let_def)

context source_attestation
begin

lemma new_published_credit_has_different_key:
  assumes inv: "message_invariant(received_messages s)"
    and old: "b\<in>set(credit_history(received_messages s))"
    and new: "snd(published_receive route c r s)=New_Credit next"
  shows "binding_key next\<noteq>binding_key b"
proof -
  have admitted: "credit_admissible c r"
    and unused: "credit_marker(request_binding r)\<notin>consumed_at(received_messages s)"
    and same: "next=request_binding r"
    using new by (auto simp: published_receive_expansion split: if_splits)
  have fresh: "binding_key(request_binding r)\<notin>set(map binding_key(credit_history(received_messages s)))"
    by (rule accepted_new_key_is_fresh[OF inv admitted unused])
  show ?thesis using fresh old by (auto simp: same)
qed

lemma reservation_step_preserves_existing_credit:
  assumes journal: "journal_agreement balances m"
    and credit: "b\<in>set(credit_history(received_messages(machine_state m)))"
  shows "b\<in>set(credit_history(received_messages(machine_state(reservation_step balances action m))))"
proof (cases action)
  case Restart_Action
  then show ?thesis using restart_reconstructs_committed_state[OF journal] credit by simp
qed (use credit in \<open>auto simp: protocol_definitions Let_def record_observation_def
    commit_reservation_event_def set_phase_def finish_reservation_def
    intro: event_preserves_existing_credit
    split: option.splits message_reply.splits\<close>)

theorem reservation_step_preserves_avoided_credited_root:
  assumes contract: "reservation_contract balances m"
    and credit: "b\<in>set(credit_history(received_messages(machine_state m)))"
    and avoids: "avoids_root(binding_key b)action"
  shows "root_snapshot(binding_key b)(machine_state(reservation_step balances action m)) =
    root_snapshot(binding_key b)(machine_state m)"
proof (cases action)
  case (Deliver_Action route c r)
  have messages: "message_invariant(received_messages(machine_state m))"
    using contract unfolding reservation_contract_def message_source_invariant_def by blast
  have fresh: "\<And>next. snd(published_receive route c r(machine_state m))=New_Credit next \<Longrightarrow>
    binding_key next\<noteq>binding_key b"
    by (rule new_published_credit_has_different_key[OF messages credit])
  show ?thesis
  proof (cases "snd(published_receive route c r(machine_state m))")
    case Message_Rejected
    then show ?thesis
      by (simp add: Deliver_Action deliver_reserved_credit_def record_observation_def)
  next
    case (Duplicate_Credit delivered)
    then show ?thesis
      by (simp add: Deliver_Action deliver_reserved_credit_def record_observation_def)
  next
    case (New_Credit delivered)
    have different: "binding_key delivered\<noteq>binding_key b" by (rule fresh[OF New_Credit])
    have frame: "root_snapshot(binding_key b)(machine_state(commit_reservation_event(Credit_Event delivered)m)) =
      root_snapshot(binding_key b)(machine_state m)"
      by (rule commit_preserves_avoided_root) (simp add: different)
    show ?thesis
      by (simp only: Deliver_Action reservation_step.simps deliver_reserved_credit_def New_Credit
          message_reply.case observation_preserves_root_snapshot frame)
  qed
next
  case (Descendant_Action c r root sender recipient amount)
  have different: "binding_key root\<noteq>binding_key b" using avoids by (simp add: Descendant_Action)
  have frame: "\<And>e. lineage_root e=root \<Longrightarrow>
    root_snapshot(binding_key b)(machine_state(commit_reservation_event(Descendant_Event e)m)) =
      root_snapshot(binding_key b)(machine_state m)"
    by (rule commit_preserves_avoided_root) (simp add: different)
  show ?thesis unfolding Descendant_Action
    by (simp only: reservation_step.simps execute_descendant_def Let_def;
        split if_splits;
        simp only: observation_preserves_root_snapshot frame reservation_state.select_convs
          descendant_effect.select_convs; blast)
next
  case Restart_Action
  have journal: "journal_agreement balances m" using contract unfolding reservation_contract_def by blast
  show ?thesis unfolding Restart_Action
    using restart_reconstructs_committed_state[OF journal] by simp
qed (auto simp: protocol_definitions Let_def root_snapshot_def record_observation_def
    commit_reservation_event_def set_phase_def finish_reservation_def split: option.splits)

theorem finite_actions_preserve_avoided_credited_root:
  assumes contract: "reservation_contract balances m"
    and credit: "b\<in>set(credit_history(received_messages(machine_state m)))"
    and avoids: "\<forall>action\<in>set actions. avoids_root(binding_key b)action"
  shows "reservation_contract balances(run_reservations balances actions m) \<and>
    b\<in>set(credit_history(received_messages(machine_state(run_reservations balances actions m)))) \<and>
    root_snapshot(binding_key b)(machine_state(run_reservations balances actions m)) =
      root_snapshot(binding_key b)(machine_state m)"
  using assms
proof (induction actions arbitrary:m)
  case Nil
  then show ?case by simp
next
  case (Cons action actions)
  let ?next = "reservation_step balances action m"
  have next_contract: "reservation_contract balances ?next"
    by (rule actual_step_preserves_reservation_contract[OF Cons.prems(1)])
  have journal: "journal_agreement balances m"
    using Cons.prems(1) unfolding reservation_contract_def by blast
  have next_credit: "b\<in>set(credit_history(received_messages(machine_state ?next)))"
    by (rule reservation_step_preserves_existing_credit[OF journal Cons.prems(2)])
  have head_avoids: "avoids_root(binding_key b)action"
    and tail_avoids: "\<forall>action\<in>set actions. avoids_root(binding_key b)action"
    using Cons.prems(3) by auto
  have head: "root_snapshot(binding_key b)(machine_state ?next)=root_snapshot(binding_key b)(machine_state m)"
    by (rule reservation_step_preserves_avoided_credited_root[OF Cons.prems(1,2) head_avoids])
  have tail: "reservation_contract balances(run_reservations balances actions ?next) \<and>
    b\<in>set(credit_history(received_messages(machine_state(run_reservations balances actions ?next)))) \<and>
    root_snapshot(binding_key b)(machine_state(run_reservations balances actions ?next)) =
      root_snapshot(binding_key b)(machine_state ?next)"
    by (rule Cons.IH[OF next_contract next_credit tail_avoids])
  show ?case using tail head by simp
qed

end

lemma actual_descendant_reply_ignores_redundant_pooled_bound:
  assumes financial: "financial_history_agreement balances m"
  shows "snd(execute_descendant c r root sender recipient amount m) =
    (if root\<in>set(credit_history(received_messages(machine_state m))) \<and>
      request_binding r=descendant_binding root recipient amount (binding_operation(request_binding r)) \<and>
      (binding_operation(request_binding r)=Ordinary_Transfer_Effect \<or>
        (\<exists>kind. binding_operation(request_binding r)=Enforcement_Transfer_Effect kind)) \<and>
      context_endpoint(lock_authority c)=binding_destination root \<and>
      metadata_permission c r(binding_destination root) \<and> 0<amount \<and>
      (request_caller r,binding_key root,sender,recipient,amount,binding_operation(request_binding r))
        \<in>lock_spend_permissions c \<and>
      amount\<le>funded_units(machine_state m)(binding_key root,holder_account root sender)
    then Descendant_Executed else Request_Rejected)"
  using root_funding_bounded_by_destination_balance[OF financial,
    of "binding_key root" "holder_account root sender"]
  by (auto simp: execute_descendant_def record_observation_def Let_def)

theorem equal_credited_root_funding_preserves_actual_descendant_reply:
  assumes first: "financial_history_agreement balances m"
    and second: "financial_history_agreement balances n"
    and credit_first: "b\<in>set(credit_history(received_messages(machine_state m)))"
    and credit_second: "b\<in>set(credit_history(received_messages(machine_state n)))"
    and funding: "\<forall>account. funded_units(machine_state m)(binding_key b,account)=
      funded_units(machine_state n)(binding_key b,account)"
  shows "snd(execute_descendant c r b sender recipient amount m)=
    snd(execute_descendant c r b sender recipient amount n)"
  by (simp only: actual_descendant_reply_ignores_redundant_pooled_bound[OF first]
      actual_descendant_reply_ignores_redundant_pooled_bound[OF second]
      credit_first credit_second funding)

context source_attestation
begin

theorem finite_unrelated_actions_preserve_actual_root_continuation:
  assumes contract: "reservation_contract balances m"
    and credit: "b\<in>set(credit_history(received_messages(machine_state m)))"
    and avoids: "\<forall>action\<in>set actions. avoids_root(binding_key b)action"
  defines "after \<equiv> run_reservations balances actions m"
  shows "(\<forall>account. funded_units(machine_state after)(binding_key b,account)=
      funded_units(machine_state m)(binding_key b,account)) \<and>
    filter(\<lambda>e. binding_key(lineage_root e)=binding_key b)(lawful_descendants(machine_state after)) =
      filter(\<lambda>e. binding_key(lineage_root e)=binding_key b)(lawful_descendants(machine_state m)) \<and>
    snd(execute_descendant c r b sender recipient amount after)=
      snd(execute_descendant c r b sender recipient amount m)"
proof -
  have preserved: "reservation_contract balances after \<and>
    b\<in>set(credit_history(received_messages(machine_state after))) \<and>
    root_snapshot(binding_key b)(machine_state after)=root_snapshot(binding_key b)(machine_state m)"
    unfolding after_def by (rule finite_actions_preserve_avoided_credited_root[OF contract credit avoids])
  have funds: "\<forall>account. funded_units(machine_state after)(binding_key b,account)=
    funded_units(machine_state m)(binding_key b,account)"
    and history: "filter(\<lambda>e. binding_key(lineage_root e)=binding_key b)(lawful_descendants(machine_state after)) =
      filter(\<lambda>e. binding_key(lineage_root e)=binding_key b)(lawful_descendants(machine_state m))"
    using preserved unfolding root_snapshot_def by (auto simp: fun_eq_iff)
  have first: "financial_history_agreement balances after"
    and second: "financial_history_agreement balances m"
    using preserved contract unfolding reservation_contract_def by blast+
  have later_credit: "b\<in>set(credit_history(received_messages(machine_state after)))"
    using preserved by blast
  have reply: "snd(execute_descendant c r b sender recipient amount after)=
    snd(execute_descendant c r b sender recipient amount m)"
    by (rule equal_credited_root_funding_preserves_actual_descendant_reply[OF first second later_credit credit funds])
  show ?thesis using funds history reply by blast
qed

theorem generated_parent_supplies_root_continuation_frame:
  fixes balances :: "source_account \<Rightarrow> nat" and prefix :: "reservation_action list"
  defines "m \<equiv> run_reservations balances prefix(initial_reservation_machine balances)"
  assumes credit: "b\<in>set(credit_history(received_messages(machine_state m)))"
    and avoids: "\<forall>action\<in>set actions. avoids_root(binding_key b)action"
  shows "snd(execute_descendant c r b sender recipient amount(run_reservations balances actions m))=
    snd(execute_descendant c r b sender recipient amount m)"
proof -
  have contract: "reservation_contract balances m"
    unfolding m_def by (rule all_finite_executions_supply_the_reservation_contract)
  show ?thesis using finite_unrelated_actions_preserve_actual_root_continuation[OF contract credit avoids,
    where c=c and r=r
      and sender=sender and recipient=recipient and amount=amount] by simp
qed

end

text \<open>The filter permits other source roots to share an asset, endpoint
  and holder account. Their effects may change pooled balances and append
  other descendant records. It preserves the selected root's funding vector
  and filtered history. Context and request are held fixed only when comparing
  the two actual consumer replies; a changed policy is not covered by that
  equality. A successful descendant of the selected root, including a
  self-transfer that appends history, is outside this static action filter.\<close>

end
