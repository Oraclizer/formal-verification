(* SPDX-License-Identifier: BSD-3-Clause *)
theory Transfer_Ledger_Refinement
  imports Finality_Protocol
begin

section \<open>An Independent Transfer Ledger\<close>

record transfer_ledger =
  ledger_source :: "source_account \<Rightarrow> nat"
  ledger_destination :: "destination_account \<Rightarrow> nat"
  ledger_funding :: "(source_key \<times> destination_account) \<Rightarrow> nat"
  ledger_debits :: "transfer_binding list"
  ledger_credits :: "transfer_binding list"
  ledger_returns :: "transfer_binding list"
  ledger_descendants :: "descendant_effect list"

datatype transfer_ledger_event =
    Ledger_Debit transfer_binding
  | Ledger_Credit transfer_binding
  | Ledger_Return transfer_binding
  | Ledger_Descendant descendant_effect

definition initial_transfer_ledger :: "(source_account \<Rightarrow> nat) \<Rightarrow> transfer_ledger" where
  "initial_transfer_ledger balances =
    \<lparr>ledger_source=balances,ledger_destination=(\<lambda>_.0),ledger_funding=(\<lambda>_.0),
      ledger_debits=[],ledger_credits=[],ledger_returns=[],ledger_descendants=[]\<rparr>"

fun apply_transfer_ledger_event :: "transfer_ledger_event \<Rightarrow> transfer_ledger \<Rightarrow> transfer_ledger" where
  "apply_transfer_ledger_event(Ledger_Debit b)l =
    l\<lparr>ledger_source:=(ledger_source l)(source_account_of b:=ledger_source l(source_account_of b)-binding_amount b),
      ledger_debits:=ledger_debits l@[b]\<rparr>"
| "apply_transfer_ledger_event(Ledger_Credit b)l =
    l\<lparr>ledger_destination:=(ledger_destination l)
        (destination_account_of b:=ledger_destination l(destination_account_of b)+binding_amount b),
      ledger_funding:=(ledger_funding l)((binding_key b,destination_account_of b):=
        ledger_funding l(binding_key b,destination_account_of b)+binding_amount b),
      ledger_credits:=ledger_credits l@[b]\<rparr>"
| "apply_transfer_ledger_event(Ledger_Return b)l =
    l\<lparr>ledger_source:=(ledger_source l)(source_account_of b:=ledger_source l(source_account_of b)+binding_amount b),
      ledger_returns:=ledger_returns l@[b]\<rparr>"
| "apply_transfer_ledger_event(Ledger_Descendant e)l =
    (let b=lineage_root e; amount=lineage_amount e;
      source=holder_account b(lineage_from e); target=holder_account b(lineage_to e);
      units=(ledger_destination l)(source:=ledger_destination l source-amount);
      funding=(ledger_funding l)((binding_key b,source):=ledger_funding l(binding_key b,source)-amount)
    in l\<lparr>ledger_destination:=units(target:=units target+amount),
      ledger_funding:=funding((binding_key b,target):=funding(binding_key b,target)+amount),
      ledger_descendants:=ledger_descendants l@[e]\<rparr>)"

fun run_transfer_ledger :: "transfer_ledger_event list \<Rightarrow> transfer_ledger \<Rightarrow> transfer_ledger" where
  "run_transfer_ledger [] l=l"
| "run_transfer_ledger(e#rest)l=run_transfer_ledger rest(apply_transfer_ledger_event e l)"

lemma run_transfer_ledger_append:
  "run_transfer_ledger(first@second)l=run_transfer_ledger second(run_transfer_ledger first l)"
  by (induction first arbitrary:l) auto

fun transfer_event_word :: "reservation_event \<Rightarrow> transfer_ledger_event list" where
  "transfer_event_word(Source_Effect_Event b)=[Ledger_Debit b]"
| "transfer_event_word(Credit_Event b)=[Ledger_Credit b]"
| "transfer_event_word(Return_Event b)=[Ledger_Return b]"
| "transfer_event_word(Descendant_Event e)=[Ledger_Descendant e]"
| "transfer_event_word _=[]"

definition transfer_journal_word :: "reservation_event list \<Rightarrow> transfer_ledger_event list" where
  "transfer_journal_word events=concat(map transfer_event_word events)"

lemma transfer_journal_word_append [simp]:
  "transfer_journal_word(first@second)=transfer_journal_word first@transfer_journal_word second"
  by (simp add: transfer_journal_word_def)

definition transfer_projection :: "reservation_machine \<Rightarrow> transfer_ledger" where
  "transfer_projection m =
    \<lparr>ledger_source=source_units(machine_state m),
      ledger_destination=destination_units(machine_state m),
      ledger_funding=funded_units(machine_state m),
      ledger_debits=source_effects(machine_state m),
      ledger_credits=credit_history(received_messages(machine_state m)),
      ledger_returns=returned_bindings(machine_journal m),
      ledger_descendants=lawful_descendants(machine_state m)\<rparr>"

lemma transfer_projection_uses_actual_state_and_journal:
  assumes "machine_state m=machine_state n" "machine_journal m=machine_journal n"
  shows "transfer_projection m=transfer_projection n"
  using assms by (simp add: transfer_projection_def)

theorem actual_committed_event_refines_transfer_word:
  "transfer_projection(commit_reservation_event event m) =
    run_transfer_ledger(transfer_event_word event)(transfer_projection m)"
  by (cases event)
    (simp_all add: transfer_projection_def commit_reservation_event_def
      set_phase_def finish_reservation_def record_credit_def Let_def)

lemma completed_observation_is_transfer_stutter:
  "transfer_projection(fst(record_observation r reply m))=transfer_projection m"
  by (simp add: transfer_projection_def record_observation_def)

theorem initial_parent_has_initial_transfer_ledger:
  "transfer_projection(initial_reservation_machine balances)=initial_transfer_ledger balances"
  by (simp add: transfer_projection_def initial_reservation_machine_def initial_reservation_state_def
      initial_transfer_ledger_def empty_message_state_def)

section \<open>Replay Is Derived from the Event Correspondence\<close>

definition reservation_replay_snapshot :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  reservation_event list \<Rightarrow> reservation_machine" where
  "reservation_replay_snapshot balances events =
    (initial_reservation_machine balances)\<lparr>machine_state:=replay_reservation_events balances events,
      machine_journal:=events\<rparr>"

lemma reservation_replay_snapshot_empty [simp]:
  "reservation_replay_snapshot balances []=initial_reservation_machine balances"
  by (simp add: reservation_replay_snapshot_def initial_reservation_machine_def replay_reservation_events_def)

lemma reservation_replay_snapshot_append:
  "reservation_replay_snapshot balances(events@[event]) =
    commit_reservation_event event(reservation_replay_snapshot balances events)"
  by (simp add: reservation_replay_snapshot_def commit_reservation_event_def replay_append_event)

theorem replay_projection_follows_independent_transfer_arithmetic:
  "transfer_projection(reservation_replay_snapshot balances events) =
    run_transfer_ledger(transfer_journal_word events)(initial_transfer_ledger balances)"
proof (induction events rule: rev_induct)
  case Nil
  then show ?case by (simp add: transfer_journal_word_def initial_parent_has_initial_transfer_ledger)
next
  case (snoc event events)
  show ?case by (simp only: reservation_replay_snapshot_append actual_committed_event_refines_transfer_word
      transfer_journal_word_append run_transfer_ledger_append snoc.IH)
    (simp add: transfer_journal_word_def)
qed

theorem restart_projection_replays_the_actual_journal:
  "transfer_projection(restart_reservation_machine balances m) =
    run_transfer_ledger(transfer_journal_word(machine_journal m))(initial_transfer_ledger balances)"
proof -
  have same: "transfer_projection(restart_reservation_machine balances m)=
    transfer_projection(reservation_replay_snapshot balances(machine_journal m))"
    by (rule transfer_projection_uses_actual_state_and_journal)
      (simp_all add: restart_reservation_machine_def reservation_replay_snapshot_def)
  show ?thesis by (simp only: same replay_projection_follows_independent_transfer_arithmetic)
qed

lemma journal_agreement_determines_projected_ledger:
  assumes journal: "journal_agreement balances m"
  shows "transfer_projection m =
    run_transfer_ledger(transfer_journal_word(machine_journal m))(initial_transfer_ledger balances)"
  using restart_projection_replays_the_actual_journal[of balances m]
    restart_reconstructs_committed_state[OF journal] by simp

definition journal_extension :: "reservation_machine \<Rightarrow> reservation_machine \<Rightarrow> bool" where
  "journal_extension before after \<longleftrightarrow>
    (\<exists>suffix. machine_journal after=machine_journal before@suffix)"

lemma journal_extension_refl [simp]: "journal_extension m m"
  unfolding journal_extension_def by (rule exI[of _ "[]"]) simp

lemma observation_extends_journal [simp]:
  "journal_extension m(fst(record_observation r reply m))"
  by (simp add: journal_extension_def record_observation_def)

lemma commit_extends_journal [simp]: "journal_extension m(commit_reservation_event event m)"
  unfolding journal_extension_def commit_reservation_event_def
  by (rule exI[of _ "[event]"]) simp

lemma observed_commit_extends_journal [simp]:
  "journal_extension m(fst(record_observation r reply(commit_reservation_event event m)))"
  by (simp add: record_observation_def journal_extension_def commit_reservation_event_def)

lemma journal_extension_has_exact_suffix:
  assumes "journal_extension before after"
  shows "machine_journal after=machine_journal before@
    drop(length(machine_journal before))(machine_journal after)"
  using assms unfolding journal_extension_def by auto

definition emitted_transfer_word :: "reservation_machine \<Rightarrow> reservation_machine \<Rightarrow>
  transfer_ledger_event list" where
  "emitted_transfer_word before after = transfer_journal_word
    (drop(length(machine_journal before))(machine_journal after))"

lemma journal_extension_refines_exact_transfer_suffix:
  assumes before: "journal_agreement balances m"
    and after: "journal_agreement balances n"
    and extension: "journal_extension m n"
  shows "transfer_projection n=run_transfer_ledger(emitted_transfer_word m n)(transfer_projection m)"
proof -
  have suffix: "machine_journal n=machine_journal m@drop(length(machine_journal m))(machine_journal n)"
    by (rule journal_extension_has_exact_suffix[OF extension])
  have projected_after: "transfer_projection n =
    run_transfer_ledger(transfer_journal_word(machine_journal n))(initial_transfer_ledger balances)"
    by (rule journal_agreement_determines_projected_ledger[OF after])
  have expanded: "transfer_projection n =
    run_transfer_ledger(transfer_journal_word(drop(length(machine_journal m))(machine_journal n)))
      (run_transfer_ledger(transfer_journal_word(machine_journal m))(initial_transfer_ledger balances))"
    using projected_after by (subst (asm) suffix)
      (simp only: transfer_journal_word_append run_transfer_ledger_append)
  show ?thesis using expanded journal_agreement_determines_projected_ledger[OF before]
    by (simp only: emitted_transfer_word_def)
qed

section \<open>The Actual Child Dispatcher Supplies the Word\<close>

context source_attestation
begin

lemma actual_parent_step_extends_journal:
  "journal_extension m(reservation_step balances action m)"
  by (cases action)
    (auto simp: protocol_definitions Let_def journal_extension_def record_observation_def
      commit_reservation_event_def restart_reservation_machine_def
      split: option.splits message_reply.splits)

lemma rejected_protocol_intent_extends_journal:
  "journal_extension(core_parent s)(core_parent(reject_protocol_intent intent s))"
  by (auto simp: reject_protocol_intent_def journal_extension_def record_observation_def split: option.splits)

lemma actual_protocol_invocation_extends_journal:
  "journal_extension(core_parent s)(core_parent(fst(invoke_protocol endpoint epoch index intent s)))"
proof -
  have actual: "journal_extension(core_parent s)
    (fst(intent_result(current_lock_view s endpoint)intent(core_parent s)))"
    by (subst intent_result_is_actual_parent_step[where balances="\<lambda>_.0"],
        rule actual_parent_step_extends_journal)
  show ?thesis using actual
    by (simp add: invoke_protocol_def rejected_protocol_intent_extends_journal Let_def)
qed

theorem actual_finality_step_extends_parent_journal:
  "journal_extension(core_parent s)(core_parent(finality_step action s))"
  by (cases action)
    (auto simp: finality_step_def record_terminal_def publish_primary_def invoke_regulatory_def
      Let_def intro: actual_protocol_invocation_extends_journal
      split: option.splits if_splits)

theorem actual_finality_step_refines_transfer_action_word:
  assumes contract: "reservation_contract balances(core_parent s)"
  shows "transfer_projection(core_parent(finality_step action s)) =
    run_transfer_ledger(emitted_transfer_word(core_parent s)(core_parent(finality_step action s)))
      (transfer_projection(core_parent s))"
proof -
  have after_contract: "reservation_contract balances(core_parent(finality_step action s))"
    by (rule finality_step_preserves_parent_contract[OF contract])
  have before: "journal_agreement balances(core_parent s)"
    and after: "journal_agreement balances(core_parent(finality_step action s))"
    using contract after_contract unfolding reservation_contract_def by blast+
  show ?thesis by (rule journal_extension_refines_exact_transfer_suffix[
    OF before after actual_finality_step_extends_parent_journal])
qed

fun finality_transfer_word :: "finality_operation list \<Rightarrow> finality_core \<Rightarrow>
  transfer_ledger_event list" where
  "finality_transfer_word [] s=[]"
| "finality_transfer_word(action#rest)s=
    emitted_transfer_word(core_parent s)(core_parent(finality_step action s))@
      finality_transfer_word rest(finality_step action s)"

theorem finite_actual_child_execution_refines_transfer_word:
  assumes "reservation_contract balances(core_parent s)"
  shows "transfer_projection(core_parent(run_finality actions s)) =
    run_transfer_ledger(finality_transfer_word actions s)(transfer_projection(core_parent s))"
  using assms
proof (induction actions arbitrary:s)
  case Nil
  then show ?case by simp
next
  case (Cons action actions)
  have contract: "reservation_contract balances(core_parent(finality_step action s))"
    by (rule finality_step_preserves_parent_contract[OF Cons.prems])
  have tail: "transfer_projection(core_parent(run_finality actions(finality_step action s))) =
    run_transfer_ledger(finality_transfer_word actions(finality_step action s))
      (transfer_projection(core_parent(finality_step action s)))"
    by (rule Cons.IH[OF contract])
  show ?case using tail actual_finality_step_refines_transfer_action_word[OF Cons.prems,of action]
    by (simp only: run_finality.simps finality_transfer_word.simps run_transfer_ledger_append)
qed

theorem generated_child_has_independent_transfer_ledger:
  "transfer_projection(core_parent(run_finality actions(initial_finality_core balances regulatory contexts))) =
    run_transfer_ledger(finality_transfer_word actions(initial_finality_core balances regulatory contexts))
      (initial_transfer_ledger balances)"
proof -
  have contract: "reservation_contract balances(core_parent(initial_finality_core balances regulatory contexts))"
    by (simp add: initial_finality_core_def initial_reservation_contract)
  show ?thesis using finite_actual_child_execution_refines_transfer_word[OF contract,of actions]
    by (simp add: initial_finality_core_def initial_parent_has_initial_transfer_ledger)
qed

end

text \<open>The projection reads actual source, destination and root funding
  fields, the debit and credit histories, and the recorded returns and onward
  effects. The independent ledger transition calculates their arithmetic.
  Replay correspondence follows from the event proof, rather than defining
  the projection as replay. The event calculation is total, including natural
  subtraction on arbitrary inputs; it is not a claim that every such event is
  admissible. The child action word comes from the journal suffix generated
  by the actual guarded dispatcher. Its parent contract is supplied initially
  and preserved at every actual step. Regulatory support and its product
  relation are separate from this quantity ledger.\<close>

end
