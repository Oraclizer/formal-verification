(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Ownership
  imports Reservation_Execution
begin

section \<open>Ownership Across Interleavings\<close>

definition ownership_consistent :: "reservation_state \<Rightarrow> bool" where
  "ownership_consistent s \<longleftrightarrow>
    (\<forall>asset key. asset_owner s asset=Some key \<longleftrightarrow>
      (\<exists>res. reservation_at s key=Some res \<and> active_reservation_phase(reservation_phase res) \<and>
        asset\<in>set(reservation_footprint res))) \<and>
    (\<forall>key res. reservation_at s key=Some res \<longrightarrow>
      binding_key(reservation_binding res)=key \<and>
      binding_asset(reservation_binding res)\<in>set(reservation_footprint res))"

lemma ownership_initial:
  "ownership_consistent(initial_reservation_state balances)"
  by (simp add: ownership_consistent_def initial_reservation_state_def)

lemma no_source_key_iff_none [simp]:
  "(\<forall>a b. owner\<noteq>Some(a,b)) \<longleftrightarrow> owner=None"
  by (cases owner) auto

lemma observation_state [simp]:
  "machine_state(fst(record_observation r reply m))=machine_state m"
  by (simp add: record_observation_def)

lemma committed_state [simp]:
  "machine_state(commit_reservation_event event m)=apply_reservation_event event(machine_state m)"
  by (simp add: commit_reservation_event_def)

lemma acquired_ownership:
  assumes "ownership_consistent s"
    "reservation_at s (binding_key(reservation_binding res))=None"
    "\<forall>a\<in>set(reservation_footprint res). asset_owner s a=None"
    "binding_asset(reservation_binding res)\<in>set(reservation_footprint res)"
    "active_reservation_phase(reservation_phase res)"
  shows "ownership_consistent(apply_reservation_event(Acquired_Event res)s)"
proof -
  have no_old_overlap:
    "\<And>a key old. a\<in>set(reservation_footprint res) \<Longrightarrow>
      reservation_at s key=Some old \<Longrightarrow> active_reservation_phase(reservation_phase old) \<Longrightarrow>
      a\<notin>set(reservation_footprint old)"
  proof -
    fix a key old
    assume inside: "a\<in>set(reservation_footprint res)"
      and old: "reservation_at s key=Some old"
      and active: "active_reservation_phase(reservation_phase old)"
    have empty: "asset_owner s a=None" using assms(3) inside by blast
    have "asset_owner s a=Some key" if "a\<in>set(reservation_footprint old)"
      using assms(1) old active that unfolding ownership_consistent_def by blast
    with empty show "a\<notin>set(reservation_footprint old)" by auto
  qed
  show ?thesis using assms no_old_overlap by (auto simp: ownership_consistent_def)
qed

lemma active_phase_preserves_ownership:
  assumes "ownership_consistent s" "active_reservation_phase phase"
    "\<forall>res. reservation_at s key=Some res \<longrightarrow> active_reservation_phase(reservation_phase res)"
  shows "ownership_consistent(set_phase key phase s)"
  using assms by (auto simp: ownership_consistent_def set_phase_def split: option.splits if_splits)

lemma finished_ownership:
  assumes "ownership_consistent s" "\<not>active_reservation_phase phase"
  shows "ownership_consistent(finish_reservation key phase s)"
proof -
  have only_owner:
    "\<And>a other res. asset_owner s a=Some key \<Longrightarrow> reservation_at s other=Some res \<Longrightarrow>
      active_reservation_phase(reservation_phase res) \<Longrightarrow>
      a\<in>set(reservation_footprint res) \<Longrightarrow> other=key"
  proof -
    fix a other res
    assume owned: "asset_owner s a=Some key" and at: "reservation_at s other=Some res"
      and active: "active_reservation_phase(reservation_phase res)"
      and member: "a\<in>set(reservation_footprint res)"
    have "asset_owner s a=Some other" using assms(1) at active member
      unfolding ownership_consistent_def by blast
    with owned show "other=key" by simp
  qed
  show ?thesis using assms
    by (auto simp: ownership_consistent_def finish_reservation_def set_phase_def
        dest: only_owner split: option.splits if_splits)
qed

lemma worker_ownership:
  "ownership_consistent s \<Longrightarrow>
    ownership_consistent(apply_reservation_event(Worker_Event key worker generation deadline)s)"
  by (auto simp: ownership_consistent_def split: option.splits if_splits)

lemma data_ownership:
  "ownership_consistent(apply_reservation_event(Data_Event a value version)s)=ownership_consistent s"
  by (simp add: ownership_consistent_def)

lemma certificate_ownership:
  "ownership_consistent(apply_reservation_event(Certificate_Event cert)s)=ownership_consistent s"
  by (simp add: ownership_consistent_def)

lemma credit_ownership:
  "ownership_consistent(apply_reservation_event(Credit_Event b)s)=ownership_consistent s"
  by (simp add: ownership_consistent_def)

lemma descendant_ownership:
  "ownership_consistent(apply_reservation_event(Descendant_Event effect)s)=ownership_consistent s"
  by (simp add: ownership_consistent_def Let_def)

lemma clock_ownership:
  "ownership_consistent(apply_reservation_event(Clock_Event time)s)=ownership_consistent s"
  by (simp add: ownership_consistent_def)

lemma source_effect_ownership:
  assumes "ownership_consistent s"
    "phase_at s(binding_key b)\<in>{Some Source_Submitted,Some Source_Pending}"
  shows "ownership_consistent(apply_reservation_event(Source_Effect_Event b)s)"
proof -
  have "ownership_consistent(set_phase(binding_key b)Source_Pending s)"
    by (rule active_phase_preserves_ownership[OF assms(1)])
       (use assms(2) in \<open>auto simp: phase_at_def split: option.splits\<close>)
  then show ?thesis by (simp add: ownership_consistent_def)
qed

lemma return_ownership:
  "ownership_consistent s \<Longrightarrow>
    ownership_consistent(apply_reservation_event(Return_Event b)s)"
  using finished_ownership[of s Source_Returned "binding_key b"]
  by (simp add: ownership_consistent_def)

lemma held_phase_ownership:
  assumes "ownership_consistent s" "phase_at s key=Some Reservation_Held"
  shows "ownership_consistent(apply_reservation_event(Dispatched_Event key)s)"
  using active_phase_preserves_ownership[OF assms(1),of Source_Submitted key] assms(2)
  by (auto simp: phase_at_def split: option.splits)

lemma cancel_ownership:
  "ownership_consistent s \<Longrightarrow> ownership_consistent(apply_reservation_event(Cancel_Event key)s)"
  by (simp add: finished_ownership)

lemma fence_ownership:
  "ownership_consistent s \<Longrightarrow> ownership_consistent(apply_reservation_event(Source_Fence_Event key)s)"
  by (simp add: finished_ownership)

lemma confirm_ownership:
  "ownership_consistent s \<Longrightarrow> ownership_consistent(apply_reservation_event(Confirm_Event key)s)"
  by (simp add: finished_ownership)

context source_attestation
begin

declare apply_reservation_event.simps [simp del]

theorem reservation_step_preserves_ownership:
  assumes own: "ownership_consistent(machine_state m)" and journal: "journal_agreement balances m"
  shows "ownership_consistent(machine_state(reservation_step balances action m))"
  using own journal restart_reconstructs_committed_state[OF journal]
  by (cases action)
     (auto simp: protocol_definitions Let_def required_footprint_def
       data_ownership certificate_ownership credit_ownership descendant_ownership clock_ownership
       intro!: acquired_ownership
       intro: held_phase_ownership source_effect_ownership worker_ownership
       cancel_ownership fence_ownership confirm_ownership return_ownership
       split: option.splits message_reply.splits)

declare apply_reservation_event.simps [simp]

theorem finite_interleaving_preserves_ownership:
  assumes "ownership_consistent(machine_state m)" "journal_agreement balances m"
  shows "ownership_consistent(machine_state(run_reservations balances actions m))"
  using assms
  by (induction actions arbitrary:m)
     (auto intro: reservation_step_preserves_ownership reservation_step_preserves_journal)

theorem generated_reservations_have_consistent_owners:
  "ownership_consistent(machine_state(run_reservations balances actions(initial_reservation_machine balances)))"
proof (rule finite_interleaving_preserves_ownership)
  show "ownership_consistent(machine_state(initial_reservation_machine balances))"
    by (simp add: initial_reservation_machine_def ownership_initial)
  show "journal_agreement balances(initial_reservation_machine balances)"
    by (rule initial_journal_agreement)
qed

end

theorem active_footprints_cannot_overlap:
  assumes "ownership_consistent s" "reservation_at s key=Some first" "reservation_at s other=Some second"
    "active_reservation_phase(reservation_phase first)" "active_reservation_phase(reservation_phase second)"
    "asset\<in>set(reservation_footprint first)" "asset\<in>set(reservation_footprint second)"
  shows "key=other"
proof -
  have first_owner: "asset_owner s asset=Some key"
    using assms(1,2,4,6) unfolding ownership_consistent_def by blast
  have second_owner: "asset_owner s asset=Some other"
    using assms(1,3,5,7) unfolding ownership_consistent_def by blast
  show ?thesis using first_owner second_owner by simp
qed

theorem active_reservation_is_owned_by_source_key:
  assumes "ownership_consistent s" "reservation_at s key=Some res"
    "active_reservation_phase(reservation_phase res)"
  shows "asset_owner s(binding_asset(reservation_binding res))=Some key"
  using assms unfolding ownership_consistent_def by blast

end
