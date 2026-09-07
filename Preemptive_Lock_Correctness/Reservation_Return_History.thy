(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Return_History
  imports Reservation_Settlement
begin

section \<open>Authoritative Non-Effect Closure\<close>

context source_attestation
begin

lemma source_non_effect_excludes_recorded_credit:
  assumes "message_source_invariant s" "\<not>source_was_debited s key"
  shows "key\<notin>set(map binding_key(credit_history(received_messages s)))"
proof
  assume "key\<in>set(map binding_key(credit_history(received_messages s)))"
  then obtain b where credited: "b\<in>set(credit_history(received_messages s))"
    and same: "binding_key b=key" by auto
  have origin: "set(credit_history(received_messages s))\<subseteq>set(source_effects s)"
    using assms(1) unfolding message_source_invariant_def credited_source_origin_def by blast
  have source: "b\<in>set(source_effects s)" by (rule subsetD[OF origin credited])
  have mapped: "binding_key b\<in>binding_key ` set(source_effects s)" by (rule imageI[OF source])
  have member: "key\<in>binding_key ` set(source_effects s)" using mapped by (simp only: same)
  have excluded: "key\<notin>binding_key ` set(source_effects s)"
    using assms(2) by (simp add: source_was_debited_def)
  show False using member excluded by contradiction
qed

theorem successful_fence_prevents_every_later_credit:
  assumes life: "source_lifecycle_consistent(machine_state m)"
    and own: "ownership_consistent(machine_state m)"
    and messages: "message_source_invariant(machine_state m)"
    and journal: "journal_agreement balances m"
    and success: "snd(fence_unexecuted_source c r g versions m)=Source_Fenced"
  shows "binding_key(request_binding r)\<notin>set(map binding_key(credit_history(received_messages
    (machine_state(run_reservations balances continuation(fst(fence_unexecuted_source c r g versions m)))))))"
proof -
  let ?next = "fst(fence_unexecuted_source c r g versions m)"
  have next_messages: "message_source_invariant(machine_state ?next)"
    using reservation_step_preserves_message_source[OF messages journal,
      where action="Fence_Action c r g versions"] by simp
  have next_journal: "journal_agreement balances ?next"
    using reservation_step_preserves_journal[OF journal,
      where action="Fence_Action c r g versions"] by simp
  have later_messages: "message_source_invariant(machine_state(run_reservations balances continuation ?next))"
    by (rule finite_interleaving_preserves_message_source[OF next_messages next_journal])
  have absent: "\<not>source_was_debited(machine_state(run_reservations balances continuation ?next))
    (binding_key(request_binding r))"
    by (rule successful_fence_prevents_every_later_source_effect[OF life own journal success])
  show ?thesis by (rule source_non_effect_excludes_recorded_credit[OF later_messages absent])
qed

theorem successful_cancel_prevents_every_later_credit:
  assumes life: "source_lifecycle_consistent(machine_state m)"
    and own: "ownership_consistent(machine_state m)"
    and messages: "message_source_invariant(machine_state m)"
    and journal: "journal_agreement balances m"
    and success: "snd(cancel_before_dispatch c r g versions m)=Reservation_Released"
  shows "binding_key(request_binding r)\<notin>set(map binding_key(credit_history(received_messages
    (machine_state(run_reservations balances continuation(fst(cancel_before_dispatch c r g versions m)))))))"
proof -
  let ?next = "fst(cancel_before_dispatch c r g versions m)"
  have next_messages: "message_source_invariant(machine_state ?next)"
    using reservation_step_preserves_message_source[OF messages journal,
      where action="Cancel_Action c r g versions"] by simp
  have next_journal: "journal_agreement balances ?next"
    using reservation_step_preserves_journal[OF journal,
      where action="Cancel_Action c r g versions"] by simp
  have later_messages: "message_source_invariant(machine_state(run_reservations balances continuation ?next))"
    by (rule finite_interleaving_preserves_message_source[OF next_messages next_journal])
  have absent: "\<not>source_was_debited(machine_state(run_reservations balances continuation ?next))
    (binding_key(request_binding r))"
    by (rule successful_cancel_prevents_every_later_source_effect[OF life own journal success])
  show ?thesis by (rule source_non_effect_excludes_recorded_credit[OF later_messages absent])
qed

end

section \<open>Returned Bindings and the Actual Journal\<close>

definition return_recorded_bindings :: "reservation_state \<Rightarrow> transfer_binding set" where
  "return_recorded_bindings s={b. \<exists>res. reservation_at s(binding_key b)=Some res \<and>
    reservation_binding res=b \<and> reservation_phase res=Source_Returned}"

definition return_history_agreement :: "reservation_machine \<Rightarrow> bool" where
  "return_history_agreement m \<longleftrightarrow>
    distinct(map binding_key(returned_bindings(machine_journal m))) \<and>
    set(returned_bindings(machine_journal m))=return_recorded_bindings(machine_state m)"

lemma returned_binding_has_returned_phase:
  "b\<in>return_recorded_bindings s \<Longrightarrow> phase_at s(binding_key b)=Some Source_Returned"
  by (auto simp: return_recorded_bindings_def phase_at_def)

lemma return_recorded_bindings_depend_on_lookup:
  "reservation_at s=reservation_at t \<Longrightarrow> return_recorded_bindings s=return_recorded_bindings t"
  by (simp add: return_recorded_bindings_def)

lemma nonreturned_key_is_absent:
  assumes "phase_at s key\<noteq>Some Source_Returned"
  shows "\<forall>b\<in>return_recorded_bindings s. binding_key b\<noteq>key"
proof (intro ballI)
  fix b
  assume member: "b\<in>return_recorded_bindings s"
  have phase: "phase_at s(binding_key b)=Some Source_Returned"
    by (rule returned_binding_has_returned_phase[OF member])
  show "binding_key b\<noteq>key"
  proof
    assume same: "binding_key b=key"
    have "phase_at s key=Some Source_Returned" using phase by (simp only: same)
    with assms show False by contradiction
  qed
qed

lemma return_records_after_phase:
  "return_recorded_bindings(set_phase key phase s)=
    {b\<in>return_recorded_bindings s. binding_key b\<noteq>key} \<union>
    (if phase=Source_Returned then {b. binding_is_registered s b \<and> binding_key b=key} else {})"
  by (auto simp: return_recorded_bindings_def binding_is_registered_def set_phase_def
      split: option.splits if_splits)

lemma nonreturned_phase_preserves_return_records:
  assumes "phase\<noteq>Source_Returned" "phase_at s key\<noteq>Some Source_Returned"
  shows "return_recorded_bindings(set_phase key phase s)=return_recorded_bindings s"
  using nonreturned_key_is_absent[OF assms(2)]
  by (auto simp: return_records_after_phase assms(1))

lemma registered_bindings_at_one_key:
  assumes registered: "binding_is_registered s b"
  shows "{other. binding_is_registered s other \<and> binding_key other=binding_key b}={b}"
proof -
  obtain res where at: "reservation_at s(binding_key b)=Some res" and binding: "reservation_binding res=b"
    using registered unfolding binding_is_registered_def by blast
  have unique: "\<And>other. binding_is_registered s other \<Longrightarrow> binding_key other=binding_key b \<Longrightarrow> other=b"
  proof -
    fix other
    assume other_registered: "binding_is_registered s other" and same_key: "binding_key other=binding_key b"
    obtain stored where other_at: "reservation_at s(binding_key other)=Some stored"
      and other_binding: "reservation_binding stored=other"
      using other_registered unfolding binding_is_registered_def by blast
    have same_stored: "stored=res" using other_at at by (simp add: same_key)
    show "other=b" using binding other_binding by (simp add: same_stored)
  qed
  show ?thesis using registered unique by auto
qed

lemma return_record_acquire:
  assumes "reservation_at s(binding_key(reservation_binding res))=None" "reservation_phase res=Reservation_Held"
  shows "return_recorded_bindings(apply_reservation_event(Acquired_Event res)s)=return_recorded_bindings s"
  using assms by (auto simp: return_recorded_bindings_def)

lemma return_record_worker:
  "return_recorded_bindings(apply_reservation_event(Worker_Event key worker generation deadline)s)=
    return_recorded_bindings s"
  by (auto simp: return_recorded_bindings_def split: option.splits if_splits)

lemma return_record_dispatch:
  assumes "phase_at s key=Some Reservation_Held"
  shows "return_recorded_bindings(apply_reservation_event(Dispatched_Event key)s)=return_recorded_bindings s"
  using nonreturned_phase_preserves_return_records[of Source_Submitted s key] assms by simp

lemma return_record_source:
  assumes "phase_at s(binding_key b)\<in>{Some Source_Submitted,Some Source_Pending}"
  shows "return_recorded_bindings(apply_reservation_event(Source_Effect_Event b)s)=return_recorded_bindings s"
proof -
  have same: "return_recorded_bindings(apply_reservation_event(Source_Effect_Event b)s)=
    return_recorded_bindings(set_phase(binding_key b)Source_Pending s)"
    by (rule return_recorded_bindings_depend_on_lookup) simp
  show ?thesis unfolding same
    by (rule nonreturned_phase_preserves_return_records)
       (use assms in \<open>auto\<close>)
qed

lemma return_record_cancel:
  assumes "phase_at s key=Some Reservation_Held"
  shows "return_recorded_bindings(apply_reservation_event(Cancel_Event key)s)=return_recorded_bindings s"
proof -
  have same: "return_recorded_bindings(apply_reservation_event(Cancel_Event key)s)=
    return_recorded_bindings(set_phase key Source_Cancelled s)"
    by (rule return_recorded_bindings_depend_on_lookup) (simp add: finish_reservation_def)
  show ?thesis unfolding same
    by (rule nonreturned_phase_preserves_return_records) (use assms in \<open>auto\<close>)
qed

lemma return_record_fence:
  assumes "phase_at s key\<in>{Some Source_Submitted,Some Source_Pending}"
  shows "return_recorded_bindings(apply_reservation_event(Source_Fence_Event key)s)=return_recorded_bindings s"
proof -
  have same: "return_recorded_bindings(apply_reservation_event(Source_Fence_Event key)s)=
    return_recorded_bindings(set_phase key Source_Cancelled s)"
    by (rule return_recorded_bindings_depend_on_lookup) (simp add: finish_reservation_def)
  show ?thesis unfolding same
    by (rule nonreturned_phase_preserves_return_records) (use assms in \<open>auto\<close>)
qed

lemma return_record_confirm:
  assumes "phase_at s key=Some Source_Pending"
  shows "return_recorded_bindings(apply_reservation_event(Confirm_Event key)s)=return_recorded_bindings s"
proof -
  have same: "return_recorded_bindings(apply_reservation_event(Confirm_Event key)s)=
    return_recorded_bindings(set_phase key Source_Confirmed s)"
    by (rule return_recorded_bindings_depend_on_lookup) (simp add: finish_reservation_def)
  show ?thesis unfolding same
    by (rule nonreturned_phase_preserves_return_records) (use assms in \<open>auto\<close>)
qed

lemma return_record_return:
  assumes registered: "binding_is_registered s b" and pending: "phase_at s(binding_key b)=Some Source_Pending"
  shows "return_recorded_bindings(apply_reservation_event(Return_Event b)s)=insert b(return_recorded_bindings s)"
proof -
  have same: "return_recorded_bindings(apply_reservation_event(Return_Event b)s)=
    return_recorded_bindings(set_phase(binding_key b)Source_Returned s)"
    by (rule return_recorded_bindings_depend_on_lookup) (simp add: finish_reservation_def)
  have absent: "\<forall>old\<in>return_recorded_bindings s. binding_key old\<noteq>binding_key b"
    by (rule nonreturned_key_is_absent) (simp add: pending)
  show ?thesis using absent unfolding same
    by (auto simp: return_records_after_phase registered_bindings_at_one_key[OF registered])
qed

lemma return_record_data:
  "return_recorded_bindings(apply_reservation_event(Data_Event asset value version)s)=return_recorded_bindings s"
  by (rule return_recorded_bindings_depend_on_lookup) simp

lemma return_record_certificate:
  "return_recorded_bindings(apply_reservation_event(Certificate_Event cert)s)=return_recorded_bindings s"
  by (rule return_recorded_bindings_depend_on_lookup) simp

lemma return_record_credit:
  "return_recorded_bindings(apply_reservation_event(Credit_Event b)s)=return_recorded_bindings s"
  by (rule return_recorded_bindings_depend_on_lookup) simp

lemma return_record_descendant:
  "return_recorded_bindings(apply_reservation_event(Descendant_Event effect)s)=return_recorded_bindings s"
  by (rule return_recorded_bindings_depend_on_lookup) (simp add: Let_def)

lemma return_record_clock:
  "return_recorded_bindings(apply_reservation_event(Clock_Event elapsed)s)=return_recorded_bindings s"
  by (rule return_recorded_bindings_depend_on_lookup) simp

lemma return_history_initial:
  "return_history_agreement(initial_reservation_machine balances)"
  by (simp add: return_history_agreement_def initial_reservation_machine_def
      initial_reservation_state_def return_recorded_bindings_def)

lemma return_history_observation [simp]:
  "return_history_agreement(fst(record_observation r reply m))=return_history_agreement m"
  by (simp add: return_history_agreement_def record_observation_def)

lemma return_history_nonreturn_commit:
  assumes "return_history_agreement m" "return_binding event=[]"
    "return_recorded_bindings(apply_reservation_event event(machine_state m))=
      return_recorded_bindings(machine_state m)"
  shows "return_history_agreement(commit_reservation_event event m)"
  using assms by (auto simp: return_history_agreement_def commit_reservation_event_def)

lemma pending_source_key_has_not_been_returned:
  assumes inv: "return_history_agreement m" and pending: "phase_at(machine_state m)key=Some Source_Pending"
  shows "key\<notin>set(map binding_key(returned_bindings(machine_journal m)))"
proof
  assume "key\<in>set(map binding_key(returned_bindings(machine_journal m)))"
  then obtain b where member: "b\<in>set(returned_bindings(machine_journal m))" and same: "binding_key b=key"
    by auto
  have represented: "b\<in>return_recorded_bindings(machine_state m)"
    using inv member unfolding return_history_agreement_def by blast
  have phase: "phase_at(machine_state m)(binding_key b)=Some Source_Returned"
    by (rule returned_binding_has_returned_phase[OF represented])
  show False using phase pending by (simp add: same)
qed

lemma return_history_return_commit:
  assumes inv: "return_history_agreement m"
    and registered: "binding_is_registered(machine_state m)b"
    and pending: "phase_at(machine_state m)(binding_key b)=Some Source_Pending"
  shows "return_history_agreement(commit_reservation_event(Return_Event b)m)"
proof -
  have unique: "distinct(map binding_key(returned_bindings(machine_journal m)))"
    and exact: "set(returned_bindings(machine_journal m))=return_recorded_bindings(machine_state m)"
    using inv unfolding return_history_agreement_def by blast+
  have fresh: "binding_key b\<notin>set(map binding_key(returned_bindings(machine_journal m)))"
    by (rule pending_source_key_has_not_been_returned[OF inv pending])
  have fresh_recorded: "binding_key b\<notin>binding_key ` return_recorded_bindings(machine_state m)"
    by (rule fresh[unfolded set_map exact])
  have after: "return_recorded_bindings(apply_reservation_event(Return_Event b)(machine_state m))=
    insert b(return_recorded_bindings(machine_state m))"
    by (rule return_record_return[OF registered pending])
  show ?thesis
    by (simp del: apply_reservation_event.simps add: return_history_agreement_def
        commit_reservation_event_def unique fresh fresh_recorded exact after)
qed

context source_attestation
begin

declare apply_reservation_event.simps [simp del]

theorem reservation_step_preserves_return_history:
  assumes inv: "return_history_agreement m" and journal: "journal_agreement balances m"
  shows "return_history_agreement(reservation_step balances action m)"
proof (cases action)
  case (Return_Action c r g versions)
  then show ?thesis using inv
    by (auto simp: release_to_source_def
        intro!: return_history_return_commit intro: owner_has_registered_binding)
next
  case Restart_Action
  then show ?thesis using restart_reconstructs_committed_state[OF journal] inv by simp
qed (use inv in \<open>auto simp: protocol_definitions Let_def
    return_record_acquire return_record_worker return_record_dispatch return_record_source
    return_record_cancel return_record_fence return_record_confirm return_record_data
    return_record_certificate return_record_credit return_record_descendant return_record_clock
  intro!: return_history_nonreturn_commit
  split: option.splits message_reply.splits\<close>)

declare apply_reservation_event.simps [simp]

theorem finite_interleaving_preserves_return_history:
  assumes "return_history_agreement m" "journal_agreement balances m"
  shows "return_history_agreement(run_reservations balances actions m)"
  using assms by (induction actions arbitrary:m)
    (auto intro: reservation_step_preserves_return_history reservation_step_preserves_journal)

theorem generated_return_history:
  "return_history_agreement(run_reservations balances actions(initial_reservation_machine balances))"
proof (rule finite_interleaving_preserves_return_history)
  show "return_history_agreement(initial_reservation_machine balances)" by (rule return_history_initial)
  show "journal_agreement balances(initial_reservation_machine balances)" by (rule initial_journal_agreement)
qed

theorem every_source_key_is_returned_at_most_once:
  "count_list(map binding_key(returned_bindings(machine_journal
    (run_reservations balances actions(initial_reservation_machine balances)))))key\<le>1"
proof -
  have unique: "distinct(map binding_key(returned_bindings(machine_journal
    (run_reservations balances actions(initial_reservation_machine balances)))))"
    using generated_return_history[of balances actions] unfolding return_history_agreement_def by blast
  show ?thesis by (rule distinct_key_count_bound[OF unique])
qed

lemma return_records_are_exact_source_returns:
  assumes life: "source_lifecycle_consistent s"
  shows "return_recorded_bindings s=returned_source_bindings s"
proof -
  have effect_if_returned: "\<And>key res. reservation_at s key=Some res \<Longrightarrow>
    reservation_phase res=Source_Returned \<Longrightarrow> reservation_binding res\<in>set(source_effects s)"
  proof -
    fix key res
    assume at: "reservation_at s key=Some res" and phase: "reservation_phase res=Source_Returned"
    have source_phase: "reservation_phase res\<in>{Source_Pending,Source_Confirmed,Source_Returned}"
      by (simp add: phase)
    show "reservation_binding res\<in>set(source_effects s)"
      using life at source_phase unfolding source_lifecycle_consistent_def by blast
  qed
  show ?thesis using life
    by (auto simp: return_recorded_bindings_def returned_source_bindings_def
        source_lifecycle_consistent_def phase_at_def dest: effect_if_returned split: option.splits)
qed

theorem return_journal_matches_returned_source_bindings:
  assumes history: "return_history_agreement m" and life: "source_lifecycle_consistent(machine_state m)"
  shows "set(returned_bindings(machine_journal m))=returned_source_bindings(machine_state m)"
  using history return_records_are_exact_source_returns[OF life]
  unfolding return_history_agreement_def by blast

theorem source_return_journal_has_exact_set_amount:
  assumes history: "return_history_agreement m" and life: "source_lifecycle_consistent(machine_state m)"
  shows "sum_list(map(returned_amount account)(machine_journal m))=
    (\<Sum>b\<in>returned_source_bindings(machine_state m).
      if source_account_of b=account then int(binding_amount b) else 0)"
proof -
  have unique: "distinct(map binding_key(returned_bindings(machine_journal m)))"
    using history unfolding return_history_agreement_def by blast
  have distinct: "distinct(returned_bindings(machine_journal m))"
    by (rule conjunct1[OF unique[unfolded distinct_map]])
  have exact: "set(returned_bindings(machine_journal m))=returned_source_bindings(machine_state m)"
    by (rule return_journal_matches_returned_source_bindings[OF history life])
  show ?thesis
    by (simp only: journal_return_amount_is_binding_sum sum_list_distinct_conv_sum_set[OF distinct] exact)
qed

text \<open>The return list is extracted from the actual journal of accepted
  protocol actions. Its key uniqueness follows from the pending-phase check
  and the permanent returned record. These results connect the signed account
  identity to the source-outcome partition without introducing a terminal
  oracle or equating regulatory support with quantities.\<close>

end

end
