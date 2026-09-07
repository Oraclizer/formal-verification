(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Lifecycle
  imports Reservation_Message_Link Reservation_Ownership
begin

section \<open>Permanent Closure and Retained Obligations\<close>

context source_attestation
begin

theorem closed_reservation_record_is_permanent:
  assumes closed: "reservation_at(machine_state m)key=Some res"
    and inactive: "\<not>active_reservation_phase(reservation_phase res)"
    and journal: "journal_agreement balances m"
  shows "reservation_at(machine_state(reservation_step balances action m))key=Some res"
  using closed inactive journal restart_reconstructs_committed_state[OF journal]
  by (cases action)
     (auto simp: protocol_definitions Let_def record_observation_def commit_reservation_event_def
       owns_current_reservation_def owns_recorded_reservation_def phase_at_def set_phase_def
       finish_reservation_def split: option.splits message_reply.splits)

theorem closed_record_survives_arbitrary_continuation:
  assumes "reservation_at(machine_state m)key=Some res"
    "\<not>active_reservation_phase(reservation_phase res)" "journal_agreement balances m"
  shows "reservation_at(machine_state(run_reservations balances actions m))key=Some res"
  using assms
  by (induction actions arbitrary:m)
     (auto intro: closed_reservation_record_is_permanent reservation_step_preserves_journal)

end

definition source_lifecycle_consistent :: "reservation_state \<Rightarrow> bool" where
  "source_lifecycle_consistent s \<longleftrightarrow>
    (\<forall>b\<in>set(source_effects s). \<exists>res. reservation_at s(binding_key b)=Some res \<and>
      reservation_binding res=b \<and> reservation_phase res\<in>{Source_Pending,Source_Confirmed,Source_Returned}) \<and>
    (\<forall>key res. reservation_at s key=Some res \<and>
      reservation_phase res\<in>{Source_Pending,Source_Confirmed,Source_Returned}
      \<longrightarrow> reservation_binding res\<in>set(source_effects s))"

lemma initial_source_lifecycle:
  "source_lifecycle_consistent(initial_reservation_state balances)"
  by (simp add: source_lifecycle_consistent_def initial_reservation_state_def)

lemma closed_cancelled_key_has_no_source_effect:
  assumes "source_lifecycle_consistent s" "reservation_at s key=Some res"
    "reservation_phase res=Source_Cancelled"
  shows "\<not>source_was_debited s key"
  using assms
  by (auto simp: source_lifecycle_consistent_def source_was_debited_def)

lemma lifecycle_phase_preserved:
  assumes "source_lifecycle_consistent s"
    "\<forall>res. reservation_at s key=Some res \<longrightarrow>
      (reservation_phase res\<in>{Source_Pending,Source_Confirmed,Source_Returned} \<longleftrightarrow>
       phase\<in>{Source_Pending,Source_Confirmed,Source_Returned})"
  shows "source_lifecycle_consistent(set_phase key phase s)"
  using assms
  by (auto simp: source_lifecycle_consistent_def set_phase_def
      split: option.splits if_splits)

lemma lifecycle_finish_preserved:
  assumes "source_lifecycle_consistent s"
    "\<forall>res. reservation_at s key=Some res \<longrightarrow>
      (reservation_phase res\<in>{Source_Pending,Source_Confirmed,Source_Returned} \<longleftrightarrow>
       phase\<in>{Source_Pending,Source_Confirmed,Source_Returned})"
  shows "source_lifecycle_consistent(finish_reservation key phase s)"
  using lifecycle_phase_preserved[OF assms]
  by (auto simp: source_lifecycle_consistent_def finish_reservation_def)

lemma lifecycle_acquire:
  assumes "source_lifecycle_consistent s"
    "reservation_at s(binding_key(reservation_binding res))=None"
    "reservation_phase res=Reservation_Held"
  shows "source_lifecycle_consistent(apply_reservation_event(Acquired_Event res)s)"
  using assms
  by (auto simp: source_lifecycle_consistent_def)

lemma lifecycle_dispatch:
  assumes "source_lifecycle_consistent s" "phase_at s key=Some Reservation_Held"
  shows "source_lifecycle_consistent(apply_reservation_event(Dispatched_Event key)s)"
  using lifecycle_phase_preserved[OF assms(1),of key Source_Submitted] assms(2)
  by (auto simp: phase_at_def split: option.splits)

lemma lifecycle_cancel:
  assumes "source_lifecycle_consistent s" "phase_at s key=Some Reservation_Held"
  shows "source_lifecycle_consistent(apply_reservation_event(Cancel_Event key)s)"
  using lifecycle_finish_preserved[OF assms(1),of key Source_Cancelled] assms(2)
  by (auto simp: phase_at_def split: option.splits)

lemma lifecycle_fence:
  assumes "source_lifecycle_consistent s" "ownership_consistent s"
    "\<not>source_was_debited s key"
  shows "source_lifecycle_consistent(apply_reservation_event(Source_Fence_Event key)s)"
proof -
  have absent: "\<forall>res. reservation_at s key=Some res \<longrightarrow>
      reservation_phase res\<notin>{Source_Pending,Source_Confirmed,Source_Returned}"
  proof (intro allI impI)
    fix res
    assume at: "reservation_at s key=Some res"
    show "reservation_phase res\<notin>{Source_Pending,Source_Confirmed,Source_Returned}"
    proof
      assume phase: "reservation_phase res\<in>{Source_Pending,Source_Confirmed,Source_Returned}"
      have identity: "binding_key(reservation_binding res)=key"
        using assms(2) at unfolding ownership_consistent_def by blast
      have effect: "reservation_binding res\<in>set(source_effects s)"
        using assms(1) at phase unfolding source_lifecycle_consistent_def by blast
      have "source_was_debited s key"
        using effect identity by (auto simp: source_was_debited_def)
      with assms(3) show False by blast
    qed
  qed
  show ?thesis using lifecycle_finish_preserved[OF assms(1),of key Source_Cancelled] absent by simp
qed

lemma lifecycle_return:
  assumes "source_lifecycle_consistent s" "phase_at s(binding_key b)=Some Source_Pending"
  shows "source_lifecycle_consistent(apply_reservation_event(Return_Event b)s)"
  using lifecycle_finish_preserved[OF assms(1),of "binding_key b" Source_Returned] assms(2)
  by (auto simp: source_lifecycle_consistent_def phase_at_def split: option.splits)

lemma lifecycle_confirm:
  assumes "source_lifecycle_consistent s" "phase_at s key=Some Source_Pending"
  shows "source_lifecycle_consistent(apply_reservation_event(Confirm_Event key)s)"
  using lifecycle_finish_preserved[OF assms(1),of key Source_Confirmed] assms(2)
  by (auto simp: phase_at_def split: option.splits)

lemma lifecycle_worker:
  "source_lifecycle_consistent s \<Longrightarrow>
    source_lifecycle_consistent(apply_reservation_event(Worker_Event key worker generation deadline)s)"
  by (auto simp: source_lifecycle_consistent_def split: option.splits if_splits)

lemma lifecycle_data:
  "source_lifecycle_consistent(apply_reservation_event(Data_Event asset value version)s)=
    source_lifecycle_consistent s"
  by (simp add: source_lifecycle_consistent_def)

lemma lifecycle_certificate:
  "source_lifecycle_consistent(apply_reservation_event(Certificate_Event cert)s)=source_lifecycle_consistent s"
  by (simp add: source_lifecycle_consistent_def)

lemma lifecycle_credit:
  "source_lifecycle_consistent(apply_reservation_event(Credit_Event b)s)=source_lifecycle_consistent s"
  by (simp add: source_lifecycle_consistent_def)

lemma lifecycle_descendant:
  "source_lifecycle_consistent(apply_reservation_event(Descendant_Event effect)s)=source_lifecycle_consistent s"
  by (simp add: source_lifecycle_consistent_def Let_def)

lemma lifecycle_clock:
  "source_lifecycle_consistent(apply_reservation_event(Clock_Event time)s)=source_lifecycle_consistent s"
  by (simp add: source_lifecycle_consistent_def)

lemma lifecycle_source_phase:
  assumes "source_lifecycle_consistent s" "ownership_consistent s"
    "binding_is_registered s b" "\<not>source_was_debited s(binding_key b)"
    "phase_at s(binding_key b)\<in>{Some Source_Submitted,Some Source_Pending}"
  shows "source_lifecycle_consistent(apply_reservation_event(Source_Effect_Event b)s)"
proof -
  obtain res where at: "reservation_at s(binding_key b)=Some res"
    and binding: "reservation_binding res=b"
    using assms(3) unfolding binding_is_registered_def by blast
  let ?next = "apply_reservation_event(Source_Effect_Event b)s"
  have lookup: "\<And>key. reservation_at ?next key=
    (if key=binding_key b then Some(res\<lparr>reservation_phase:=Source_Pending\<rparr>) else reservation_at s key)"
    using at by (simp add: set_phase_def)
  have effects: "source_effects ?next=source_effects s@[b]" by simp
  have fresh: "\<And>old. old\<in>set(source_effects s) \<Longrightarrow> binding_key old\<noteq>binding_key b"
  proof -
    fix old
    assume earlier: "old\<in>set(source_effects s)"
    have member: "binding_key old\<in>binding_key ` set(source_effects s)"
      by (rule imageI[OF earlier])
    have excluded: "binding_key b\<notin>binding_key ` set(source_effects s)"
      using assms(4) by (simp add: source_was_debited_def)
    show "binding_key old\<noteq>binding_key b"
    proof
      assume same: "binding_key old=binding_key b"
      have current_member: "binding_key b\<in>binding_key ` set(source_effects s)"
        using member by (simp only: same)
      show False using current_member excluded by contradiction
    qed
  qed
  have forward: "\<forall>old\<in>set(source_effects ?next). \<exists>stored.
    reservation_at ?next(binding_key old)=Some stored \<and> reservation_binding stored=old \<and>
    reservation_phase stored\<in>{Source_Pending,Source_Confirmed,Source_Returned}"
  proof (intro ballI)
    fix old
    assume member: "old\<in>set(source_effects ?next)"
    show "\<exists>stored. reservation_at ?next(binding_key old)=Some stored \<and>
      reservation_binding stored=old \<and>
      reservation_phase stored\<in>{Source_Pending,Source_Confirmed,Source_Returned}"
    proof (cases "old=b")
      case True
      show ?thesis
        by (rule exI[of _ "res\<lparr>reservation_phase:=Source_Pending\<rparr>"])
           (simp add: set_phase_def at binding True)
    next
      case False
      have earlier: "old\<in>set(source_effects s)" using member False by (simp add: effects)
      obtain stored where old_at: "reservation_at s(binding_key old)=Some stored"
        and old_binding: "reservation_binding stored=old"
        and old_phase: "reservation_phase stored\<in>{Source_Pending,Source_Confirmed,Source_Returned}"
        using assms(1) earlier unfolding source_lifecycle_consistent_def by blast
      have different: "binding_key old\<noteq>binding_key b" by (rule fresh[OF earlier])
      show ?thesis
      proof (intro exI[of _ stored] conjI)
        show "reservation_at ?next(binding_key old)=Some stored"
          by (simp add: set_phase_def different old_at)
        show "reservation_binding stored=old" by (rule old_binding)
        show "reservation_phase stored\<in>{Source_Pending,Source_Confirmed,Source_Returned}"
          by (rule old_phase)
      qed
    qed
  qed
  have backward: "\<forall>key stored. reservation_at ?next key=Some stored \<and>
    reservation_phase stored\<in>{Source_Pending,Source_Confirmed,Source_Returned} \<longrightarrow>
    reservation_binding stored\<in>set(source_effects ?next)"
  proof (intro allI impI)
    fix key stored
    assume premise: "reservation_at ?next key=Some stored \<and>
      reservation_phase stored\<in>{Source_Pending,Source_Confirmed,Source_Returned}"
    show "reservation_binding stored\<in>set(source_effects ?next)"
    proof (cases "key=binding_key b")
      case True
      have same: "stored=res\<lparr>reservation_phase:=Source_Pending\<rparr>"
        using premise by (auto simp: set_phase_def at True)
      show ?thesis by (simp add: same binding effects)
    next
      case False
      have old_at: "reservation_at s key=Some stored" using premise by (auto simp: set_phase_def False)
      have earlier: "reservation_binding stored\<in>set(source_effects s)"
        using assms(1) old_at premise unfolding source_lifecycle_consistent_def by blast
      then show ?thesis by (simp add: effects)
    qed
  qed
  show ?thesis using forward backward unfolding source_lifecycle_consistent_def by blast
qed

context source_attestation
begin

declare apply_reservation_event.simps [simp del]

theorem reservation_step_preserves_source_lifecycle:
  assumes life: "source_lifecycle_consistent(machine_state m)"
    and own: "ownership_consistent(machine_state m)"
    and journal: "journal_agreement balances m"
  shows "source_lifecycle_consistent(machine_state(reservation_step balances action m))"
  using life own journal restart_reconstructs_committed_state[OF journal]
  by (cases action)
     (auto simp: protocol_definitions Let_def
       lifecycle_data lifecycle_certificate lifecycle_credit lifecycle_descendant lifecycle_clock
       intro!: lifecycle_acquire
       intro: lifecycle_dispatch lifecycle_source_phase lifecycle_cancel lifecycle_fence
         lifecycle_return lifecycle_confirm lifecycle_worker
       split: option.splits message_reply.splits)

declare apply_reservation_event.simps [simp]

theorem finite_interleaving_preserves_lifecycle:
  assumes "source_lifecycle_consistent(machine_state m)" "ownership_consistent(machine_state m)"
    "journal_agreement balances m"
  shows "source_lifecycle_consistent(machine_state(run_reservations balances actions m))"
  using assms
  by (induction actions arbitrary:m)
     (auto intro: reservation_step_preserves_source_lifecycle reservation_step_preserves_ownership
       reservation_step_preserves_journal)

lemma generated_source_lifecycle:
  "source_lifecycle_consistent(machine_state
    (run_reservations balances actions(initial_reservation_machine balances)))"
proof (rule finite_interleaving_preserves_lifecycle)
  show "source_lifecycle_consistent(machine_state(initial_reservation_machine balances))"
    by (simp add: initial_reservation_machine_def initial_source_lifecycle)
  show "ownership_consistent(machine_state(initial_reservation_machine balances))"
    by (simp add: initial_reservation_machine_def ownership_initial)
  show "journal_agreement balances(initial_reservation_machine balances)"
    by (rule initial_journal_agreement)
qed

theorem cancelled_source_cannot_be_reused:
  assumes life: "source_lifecycle_consistent(machine_state m)"
    and own: "ownership_consistent(machine_state m)"
    and journal: "journal_agreement balances m"
    and closed: "reservation_at(machine_state m)key=Some res"
    and phase: "reservation_phase res=Source_Cancelled"
  shows "\<not>source_was_debited(machine_state(run_reservations balances continuation m))key"
proof -
  have preserved: "reservation_at(machine_state(run_reservations balances continuation m))key=Some res"
    by (rule closed_record_survives_arbitrary_continuation[OF closed _ journal]) (simp add: phase)
  have later_life: "source_lifecycle_consistent(machine_state(run_reservations balances continuation m))"
    by (rule finite_interleaving_preserves_lifecycle[OF life own journal])
  show ?thesis by (rule closed_cancelled_key_has_no_source_effect[OF later_life preserved phase])
qed

theorem successful_cancel_closes_without_financial_effect:
  assumes success: "snd(cancel_before_dispatch c r g versions m)=Reservation_Released"
  shows "phase_at(machine_state(fst(cancel_before_dispatch c r g versions m)))
      (binding_key(request_binding r))=Some Source_Cancelled \<and>
    (\<forall>asset. asset_owner(machine_state(fst(cancel_before_dispatch c r g versions m)))asset
      \<noteq>Some(binding_key(request_binding r))) \<and>
    source_units(machine_state(fst(cancel_before_dispatch c r g versions m)))=source_units(machine_state m) \<and>
    destination_units(machine_state(fst(cancel_before_dispatch c r g versions m)))=destination_units(machine_state m)"
proof -
  let ?after = "machine_state(fst(cancel_before_dispatch c r g versions m))"
  have accepted: "owns_recorded_reservation c r g versions(machine_state m) \<and>
    phase_at(machine_state m)(binding_key(request_binding r))=Some Reservation_Held"
    using success
    by (auto simp: cancel_before_dispatch_def record_observation_def split: if_splits)
  have result: "?after=finish_reservation(binding_key(request_binding r))Source_Cancelled(machine_state m)"
    using accepted by (simp add: cancel_before_dispatch_def)
  show ?thesis using accepted
    by (auto simp: result phase_at_def finish_reservation_def set_phase_def
        split: option.splits if_splits)
qed

theorem successful_fence_closes_without_financial_effect:
  assumes success: "snd(fence_unexecuted_source c r g versions m)=Source_Fenced"
  shows "phase_at(machine_state(fst(fence_unexecuted_source c r g versions m)))
      (binding_key(request_binding r))=Some Source_Cancelled \<and>
    (\<forall>asset. asset_owner(machine_state(fst(fence_unexecuted_source c r g versions m)))asset
      \<noteq>Some(binding_key(request_binding r))) \<and>
    source_units(machine_state(fst(fence_unexecuted_source c r g versions m)))=source_units(machine_state m) \<and>
    destination_units(machine_state(fst(fence_unexecuted_source c r g versions m)))=destination_units(machine_state m)"
proof -
  let ?after = "machine_state(fst(fence_unexecuted_source c r g versions m))"
  have accepted: "owns_recorded_reservation c r g versions(machine_state m) \<and>
    phase_at(machine_state m)(binding_key(request_binding r))\<in>{Some Source_Submitted,Some Source_Pending} \<and>
    \<not>source_was_debited(machine_state m)(binding_key(request_binding r)) \<and>
    context_endpoint(lock_authority c)=fst(binding_key(request_binding r))"
    using success
    by (auto simp: fence_unexecuted_source_def record_observation_def split: if_splits)
  have result: "?after=finish_reservation(binding_key(request_binding r))Source_Cancelled(machine_state m)"
    using accepted by (simp add: fence_unexecuted_source_def)
  show ?thesis using accepted
    by (auto simp: result phase_at_def finish_reservation_def set_phase_def
        split: option.splits if_splits)
qed

theorem successful_fence_prevents_every_later_source_effect:
  assumes life: "source_lifecycle_consistent(machine_state m)"
    and own: "ownership_consistent(machine_state m)"
    and journal: "journal_agreement balances m"
    and success: "snd(fence_unexecuted_source c r g versions m)=Source_Fenced"
  shows "\<not>source_was_debited(machine_state(run_reservations balances continuation
      (fst(fence_unexecuted_source c r g versions m))))(binding_key(request_binding r))"
proof -
  let ?next = "fst(fence_unexecuted_source c r g versions m)"
  have closed: "phase_at(machine_state ?next)(binding_key(request_binding r))=Some Source_Cancelled"
    using successful_fence_closes_without_financial_effect[OF success] by blast
  obtain res where at: "reservation_at(machine_state ?next)(binding_key(request_binding r))=Some res"
    and phase: "reservation_phase res=Source_Cancelled"
    using closed by (auto simp: phase_at_def split: option.splits)
  have next_life: "source_lifecycle_consistent(machine_state ?next)"
    using reservation_step_preserves_source_lifecycle[OF life own journal,
      where action="Fence_Action c r g versions"] by simp
  have next_own: "ownership_consistent(machine_state ?next)"
    using reservation_step_preserves_ownership[OF own journal,
      where action="Fence_Action c r g versions"] by simp
  have next_journal: "journal_agreement balances ?next"
    using reservation_step_preserves_journal[OF journal,
      where action="Fence_Action c r g versions"] by simp
  show ?thesis
    by (rule cancelled_source_cannot_be_reused[OF next_life next_own next_journal at phase])
qed

theorem successful_cancel_prevents_every_later_source_effect:
  assumes life: "source_lifecycle_consistent(machine_state m)"
    and own: "ownership_consistent(machine_state m)"
    and journal: "journal_agreement balances m"
    and success: "snd(cancel_before_dispatch c r g versions m)=Reservation_Released"
  shows "\<not>source_was_debited(machine_state(run_reservations balances continuation
      (fst(cancel_before_dispatch c r g versions m))))(binding_key(request_binding r))"
proof -
  let ?next = "fst(cancel_before_dispatch c r g versions m)"
  have closed: "phase_at(machine_state ?next)(binding_key(request_binding r))=Some Source_Cancelled"
    using successful_cancel_closes_without_financial_effect[OF success] by blast
  obtain res where at: "reservation_at(machine_state ?next)(binding_key(request_binding r))=Some res"
    and phase: "reservation_phase res=Source_Cancelled"
    using closed by (auto simp: phase_at_def split: option.splits)
  have next_life: "source_lifecycle_consistent(machine_state ?next)"
    using reservation_step_preserves_source_lifecycle[OF life own journal,
      where action="Cancel_Action c r g versions"] by simp
  have next_own: "ownership_consistent(machine_state ?next)"
    using reservation_step_preserves_ownership[OF own journal,
      where action="Cancel_Action c r g versions"] by simp
  have next_journal: "journal_agreement balances ?next"
    using reservation_step_preserves_journal[OF journal,
      where action="Cancel_Action c r g versions"] by simp
  show ?thesis
    by (rule cancelled_source_cannot_be_reused[OF next_life next_own next_journal at phase])
qed

definition unresolved_source_obligations :: "reservation_state \<Rightarrow> transfer_binding set" where
  "unresolved_source_obligations s =
    {b\<in>set(source_effects s). b\<notin>set(credit_history(received_messages s)) \<and>
      phase_at s(binding_key b)\<noteq>Some Source_Returned}"

definition source_acknowledgement_backlog :: "reservation_state \<Rightarrow> transfer_binding set" where
  "source_acknowledgement_backlog s =
    {b\<in>set(credit_history(received_messages s)). phase_at s(binding_key b)=Some Source_Pending}"

theorem unresolved_and_completed_credit_are_disjoint:
  "unresolved_source_obligations s \<inter> set(credit_history(received_messages s))={}"
  by (auto simp: unresolved_source_obligations_def)

theorem timeout_retains_unresolved_and_backlog:
  "unresolved_source_obligations(machine_state(advance_reservation_time elapsed m))=
      unresolved_source_obligations(machine_state m) \<and>
    source_acknowledgement_backlog(machine_state(advance_reservation_time elapsed m))=
      source_acknowledgement_backlog(machine_state m)"
  by (simp add: unresolved_source_obligations_def source_acknowledgement_backlog_def
      phase_at_def advance_reservation_time_def commit_reservation_event_def)

text \<open>The source phase also describes acknowledgement lag. Economic
  pending obligations therefore depend on actual credits and returns, rather
  than on that phase alone. This prevents counting a completed destination
  credit again as pending mass. The distinction is a local financial view,
  not a complete cross-domain terminal-decision protocol.\<close>

end

end
