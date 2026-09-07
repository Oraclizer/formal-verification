(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Settlement
  imports Reservation_Lifecycle Reservation_Evidence Reservation_Accounting
begin

section \<open>Source Outcomes and Financial Settlement\<close>

context source_attestation
begin

definition settlement_records_consistent :: "reservation_state \<Rightarrow> bool" where
  "settlement_records_consistent s \<longleftrightarrow>
    (\<forall>key res. reservation_at s key=Some res \<longrightarrow>
      (reservation_phase res=Source_Returned \<longrightarrow>
        stable_source key=Some \<lparr>statement_binding=reservation_binding res,statement_status=Reversed\<rparr>) \<and>
      (reservation_phase res=Source_Confirmed \<longrightarrow>
        reservation_binding res\<in>set(credit_history(received_messages s))))"

lemma settlement_records_initial:
  "settlement_records_consistent(initial_reservation_state balances)"
  by (simp add: settlement_records_consistent_def initial_reservation_state_def)

lemma settlement_acquire:
  assumes "settlement_records_consistent s"
    "reservation_at s(binding_key(reservation_binding res))=None"
    "reservation_phase res=Reservation_Held"
  shows "settlement_records_consistent(apply_reservation_event(Acquired_Event res)s)"
  using assms by (auto simp: settlement_records_consistent_def)

lemma settlement_nonterminal_phase:
  assumes "settlement_records_consistent s" "phase\<noteq>Source_Returned" "phase\<noteq>Source_Confirmed"
  shows "settlement_records_consistent(set_phase key phase s)"
  using assms
  by (auto simp: settlement_records_consistent_def set_phase_def split: option.splits if_splits)

lemma settlement_dispatch:
  "settlement_records_consistent s \<Longrightarrow>
    settlement_records_consistent(apply_reservation_event(Dispatched_Event key)s)"
  by (simp add: settlement_nonterminal_phase)

lemma settlement_source_effect:
  "settlement_records_consistent s \<Longrightarrow>
    settlement_records_consistent(apply_reservation_event(Source_Effect_Event b)s)"
  using settlement_nonterminal_phase[of s Source_Pending "binding_key b"]
  by (auto simp: settlement_records_consistent_def)

lemma settlement_cancel:
  "settlement_records_consistent s \<Longrightarrow>
    settlement_records_consistent(apply_reservation_event(Cancel_Event key)s)"
  using settlement_nonterminal_phase[of s Source_Cancelled key]
  by (auto simp: settlement_records_consistent_def finish_reservation_def)

lemma settlement_fence:
  "settlement_records_consistent s \<Longrightarrow>
    settlement_records_consistent(apply_reservation_event(Source_Fence_Event key)s)"
  using settlement_nonterminal_phase[of s Source_Cancelled key]
  by (auto simp: settlement_records_consistent_def finish_reservation_def)

lemma settlement_worker:
  "settlement_records_consistent s \<Longrightarrow>
    settlement_records_consistent(apply_reservation_event(Worker_Event key worker generation deadline)s)"
  by (auto simp: settlement_records_consistent_def split: option.splits if_splits)

lemma settlement_return:
  assumes "settlement_records_consistent s" "binding_is_registered s b"
    "stable_source(binding_key b)=Some \<lparr>statement_binding=b,statement_status=Reversed\<rparr>"
  shows "settlement_records_consistent(apply_reservation_event(Return_Event b)s)"
  using assms
  by (auto simp: settlement_records_consistent_def binding_is_registered_def
      finish_reservation_def set_phase_def split: option.splits if_splits)

lemma settlement_confirm:
  assumes "settlement_records_consistent s" "binding_is_registered s b"
    "b\<in>set(credit_history(received_messages s))"
  shows "settlement_records_consistent(apply_reservation_event(Confirm_Event(binding_key b))s)"
  using assms
  by (auto simp: settlement_records_consistent_def binding_is_registered_def
      finish_reservation_def set_phase_def split: option.splits if_splits)

lemma settlement_data:
  "settlement_records_consistent(apply_reservation_event(Data_Event a value version)s)=
    settlement_records_consistent s"
  by (simp add: settlement_records_consistent_def)

lemma settlement_certificate:
  "settlement_records_consistent(apply_reservation_event(Certificate_Event cert)s)=settlement_records_consistent s"
  by (simp add: settlement_records_consistent_def)

lemma settlement_credit:
  "settlement_records_consistent s \<Longrightarrow>
    settlement_records_consistent(apply_reservation_event(Credit_Event b)s)"
  by (auto simp: settlement_records_consistent_def)

lemma settlement_descendant:
  "settlement_records_consistent(apply_reservation_event(Descendant_Event effect)s)=settlement_records_consistent s"
  by (simp add: settlement_records_consistent_def Let_def)

lemma settlement_clock:
  "settlement_records_consistent(apply_reservation_event(Clock_Event elapsed)s)=settlement_records_consistent s"
  by (simp add: settlement_records_consistent_def)

lemma owner_has_registered_binding:
  "owns_recorded_reservation c r g versions s \<Longrightarrow> binding_is_registered s(request_binding r)"
  unfolding owns_recorded_reservation_def binding_is_registered_def by blast

declare apply_reservation_event.simps [simp del]

theorem reservation_step_preserves_settlement_records:
  assumes inv: "settlement_records_consistent(machine_state m)"
    and journal: "journal_agreement balances m"
  shows "settlement_records_consistent(machine_state(reservation_step balances action m))"
  using inv journal restart_reconstructs_committed_state[OF journal]
  by (cases action)
     (auto simp: protocol_definitions Let_def
       settlement_data settlement_certificate settlement_descendant settlement_clock
       intro!: settlement_acquire
       intro: settlement_dispatch settlement_source_effect settlement_cancel settlement_fence
         settlement_worker settlement_credit settlement_return settlement_confirm
         owner_has_registered_binding reversed_evidence_is_stable
       split: option.splits message_reply.splits)

declare apply_reservation_event.simps [simp]

theorem finite_interleaving_preserves_settlement_records:
  assumes "settlement_records_consistent(machine_state m)" "journal_agreement balances m"
  shows "settlement_records_consistent(machine_state(run_reservations balances actions m))"
  using assms by (induction actions arbitrary:m)
    (auto intro: reservation_step_preserves_settlement_records reservation_step_preserves_journal)

theorem generated_settlement_records:
  "settlement_records_consistent(machine_state
    (run_reservations balances actions(initial_reservation_machine balances)))"
proof (rule finite_interleaving_preserves_settlement_records)
  show "settlement_records_consistent(machine_state(initial_reservation_machine balances))"
    by (simp add: initial_reservation_machine_def settlement_records_initial)
  show "journal_agreement balances(initial_reservation_machine balances)"
    by (rule initial_journal_agreement)
qed

definition returned_source_bindings :: "reservation_state \<Rightarrow> transfer_binding set" where
  "returned_source_bindings s =
    {b\<in>set(source_effects s). phase_at s(binding_key b)=Some Source_Returned}"

theorem source_effects_have_exact_settlement_partition:
  assumes "credited_source_origin s"
  shows "set(source_effects s)=unresolved_source_obligations s \<union>
    set(credit_history(received_messages s)) \<union> returned_source_bindings s"
  using assms
  by (auto simp: credited_source_origin_def unresolved_source_obligations_def returned_source_bindings_def)

theorem unresolved_and_returned_are_disjoint:
  "unresolved_source_obligations s \<inter> returned_source_bindings s={}"
  by (auto simp: unresolved_source_obligations_def returned_source_bindings_def)

theorem completed_credit_and_returned_are_disjoint:
  assumes records: "settlement_records_consistent s"
    and messages: "message_invariant(received_messages s)"
  shows "set(credit_history(received_messages s)) \<inter> returned_source_bindings s={}"
proof (rule ccontr)
  assume "set(credit_history(received_messages s)) \<inter> returned_source_bindings s\<noteq>{}"
  then obtain b where credited: "b\<in>set(credit_history(received_messages s))"
    and phase: "phase_at s(binding_key b)=Some Source_Returned"
    unfolding returned_source_bindings_def by blast
  obtain res where at: "reservation_at s(binding_key b)=Some res"
    and returned: "reservation_phase res=Source_Returned"
    using phase by (auto simp: phase_at_def split: option.splits)
  have reverse: "stable_source(binding_key b)=
    Some \<lparr>statement_binding=reservation_binding res,statement_status=Reversed\<rparr>"
    using records at returned unfolding settlement_records_consistent_def by blast
  have final: "stable_source(binding_key b)=Some \<lparr>statement_binding=b,statement_status=Finalized\<rparr>"
    using messages credited unfolding message_invariant_def by blast
  show False using reverse final
    by (metis option.inject source_statement.select_convs(2) source_status.distinct(5))
qed

theorem reachable_settlement_partition:
  fixes balances :: "source_account \<Rightarrow> nat"
    and actions :: "reservation_action list"
  defines "state \<equiv> machine_state(run_reservations balances actions(initial_reservation_machine balances))"
  shows "set(source_effects state)=unresolved_source_obligations state \<union>
      set(credit_history(received_messages state)) \<union> returned_source_bindings state"
    "unresolved_source_obligations state \<inter> set(credit_history(received_messages state))={}"
    "unresolved_source_obligations state \<inter> returned_source_bindings state={}"
    "set(credit_history(received_messages state)) \<inter> returned_source_bindings state={}"
proof -
  have messages: "message_source_invariant state"
    unfolding state_def by (rule generated_message_source_invariant)
  have records: "settlement_records_consistent state"
    unfolding state_def by (rule generated_settlement_records)
  show "set(source_effects state)=unresolved_source_obligations state \<union>
      set(credit_history(received_messages state)) \<union> returned_source_bindings state"
    by (rule source_effects_have_exact_settlement_partition)
       (use messages in \<open>simp add: message_source_invariant_def\<close>)
  show "unresolved_source_obligations state \<inter> set(credit_history(received_messages state))={}"
    by (rule unresolved_and_completed_credit_are_disjoint)
  show "unresolved_source_obligations state \<inter> returned_source_bindings state={}"
    by (rule unresolved_and_returned_are_disjoint)
  show "set(credit_history(received_messages state)) \<inter> returned_source_bindings state={}"
    by (rule completed_credit_and_returned_are_disjoint[OF records])
       (use messages in \<open>simp add: message_source_invariant_def\<close>)
qed

end

fun return_binding :: "reservation_event \<Rightarrow> transfer_binding list" where
  "return_binding(Return_Event b)=[b]"
| "return_binding _=[]"

definition returned_bindings :: "reservation_event list \<Rightarrow> transfer_binding list" where
  "returned_bindings events=concat(map return_binding events)"

lemma returned_bindings_append [simp]:
  "returned_bindings(xs@ys)=returned_bindings xs@returned_bindings ys"
  by (simp add: returned_bindings_def)

lemma returned_bindings_empty [simp]: "returned_bindings []=[]"
  by (simp add: returned_bindings_def)

lemma returned_bindings_singleton [simp]: "returned_bindings[event]=return_binding event"
  by (simp add: returned_bindings_def)

lemma journal_return_amount_is_binding_sum:
  "sum_list(map(returned_amount account)events)=
    sum_list(map(\<lambda>b. if source_account_of b=account then int(binding_amount b) else 0)(returned_bindings events))"
proof (induction events)
  case Nil
  then show ?case by simp
next
  case (Cons event rest)
  then show ?case by (cases event) (simp_all add: returned_bindings_def)
qed

text \<open>The partition distinguishes an actual destination credit, an
  evidence-supported source return, and an unresolved source obligation.
  A pending source acknowledgement may coexist with an actual credit; it
  contributes to the credit component only. Source facts remain supplied by
  the parent attestation profile.\<close>

end
