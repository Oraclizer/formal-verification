(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Progress
  imports Reservation_Frame
begin

section \<open>Completed Conflicts and Conditional Recovery\<close>

definition completed_busy_conflicts :: "lock_context \<Rightarrow> execution_request set \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> reservation_machine \<Rightarrow>
  (source_key \<times> source_key) set" where
  "completed_busy_conflicts c requests versions duration m =
    {(key,owner). \<exists>r asset. r\<in>requests \<and> key=binding_key(request_binding r) \<and>
      snd(acquire_reservation c r versions duration m)=Reservation_Busy \<and>
      asset\<in>set(required_footprint c(request_binding r)) \<and>
      asset_owner(machine_state m)asset=Some owner}"

lemma busy_acquisition_key_is_fresh:
  assumes "snd(acquire_reservation c r versions duration m)=Reservation_Busy"
  shows "reservation_at(machine_state m)(binding_key(request_binding r))=None"
  using assms by (auto simp: acquire_reservation_def record_observation_def Let_def split: if_splits)

lemma busy_conflict_source_has_no_reservation:
  assumes "(key,owner)\<in>completed_busy_conflicts c requests versions duration m"
  shows "reservation_at(machine_state m)key=None"
proof -
  obtain r where key: "key=binding_key(request_binding r)"
    and busy: "snd(acquire_reservation c r versions duration m)=Reservation_Busy"
    using assms unfolding completed_busy_conflicts_def by auto
  show ?thesis using busy_acquisition_key_is_fresh[OF busy] key by simp
qed

lemma busy_conflict_target_has_reservation:
  assumes "ownership_consistent(machine_state m)"
    "(key,owner)\<in>completed_busy_conflicts c requests versions duration m"
  shows "reservation_at(machine_state m)owner\<noteq>None"
  using assms unfolding completed_busy_conflicts_def ownership_consistent_def by fastforce

theorem completed_busy_conflicts_have_no_two_edges:
  assumes "ownership_consistent(machine_state m)"
    "(first,second)\<in>completed_busy_conflicts c requests versions duration m"
  shows "(second,third)\<notin>completed_busy_conflicts c requests versions duration m"
proof
  assume edge: "(second,third)\<in>completed_busy_conflicts c requests versions duration m"
  have empty: "reservation_at(machine_state m)second=None"
    by (rule busy_conflict_source_has_no_reservation[OF edge])
  have occupied: "reservation_at(machine_state m)second\<noteq>None"
    by (rule busy_conflict_target_has_reservation[OF assms])
  show False using empty occupied by contradiction
qed

lemma completed_busy_conflicts_irreflexive:
  assumes "ownership_consistent(machine_state m)"
  shows "(key,key)\<notin>completed_busy_conflicts c requests versions duration m"
proof
  assume edge: "(key,key)\<in>completed_busy_conflicts c requests versions duration m"
  have absent: "(key,key)\<notin>completed_busy_conflicts c requests versions duration m"
    by (rule completed_busy_conflicts_have_no_two_edges[OF assms edge])
  show False using edge absent by contradiction
qed

lemma completed_busy_conflict_path_is_single:
  assumes own: "ownership_consistent(machine_state m)"
    and path: "(first,last_key)\<in>(completed_busy_conflicts c requests versions duration m)\<^sup>+"
  shows "(first,last_key)\<in>completed_busy_conflicts c requests versions duration m"
  using path
  by (induction rule: trancl_induct)
     (auto dest: completed_busy_conflicts_have_no_two_edges[OF own])

theorem completed_busy_conflicts_are_acyclic:
  assumes "ownership_consistent(machine_state m)"
  shows "acyclic(completed_busy_conflicts c requests versions duration m)"
  unfolding acyclic_def
proof (intro allI notI)
  fix key
  assume path: "(key,key)\<in>(completed_busy_conflicts c requests versions duration m)\<^sup>+"
  have edge: "(key,key)\<in>completed_busy_conflicts c requests versions duration m"
    by (rule completed_busy_conflict_path_is_single[OF assms path])
  have absent: "(key,key)\<notin>completed_busy_conflicts c requests versions duration m"
    by (rule completed_busy_conflicts_irreflexive[OF assms])
  show False using edge absent by contradiction
qed

text \<open>The relation records the owners encountered by acquisition attempts
  evaluated against one current state. A Busy response completes without
  retaining any partial acquisition. Its source key has no reservation; its
  target key has one. Consequently it cannot form a reservation-key wait cycle.
  There is no scheduler, persistent waiter queue, or client workflow in this
  state machine. The theorem does not claim that an external worker holding
  another reservation cannot stall its own workflow.\<close>

lemma expired_worker_reassignment_activates:
  assumes "reservation_at(machine_state m)(binding_key(request_binding r))=Some res"
    "current_use_allowed(lock_authority c) r" "duration>0"
    "reservation_binding res=request_binding r"
    "active_reservation_phase(reservation_phase res)"
    "reservation_deadline res\<le>reservation_clock(machine_state m)"
  shows "snd(reassign_worker c r duration m)=Worker_Reassigned \<and>
    reservation_at(machine_state(fst(reassign_worker c r duration m)))(binding_key(request_binding r))=
      Some(res\<lparr>reservation_worker:=request_caller r,
        reservation_generation:=Suc(reservation_generation res),
        reservation_deadline:=reservation_clock(machine_state m)+duration\<rparr>)"
  using assms by (simp add: reassign_worker_def record_observation_def commit_reservation_event_def)

lemma reassignment_preserves_phase_and_evidence:
  fixes c :: lock_context and r :: execution_request and duration :: nat and m :: reservation_machine
  defines "taken \<equiv> machine_state(fst(reassign_worker c r duration m))"
  shows "phase_at taken key=phase_at(machine_state m)key \<and>
    source_effects taken=source_effects(machine_state m) \<and>
    issued_certificates taken=issued_certificates(machine_state m) \<and>
    received_messages taken=received_messages(machine_state m)"
  unfolding taken_def
  by (auto simp: reassign_worker_def record_observation_def commit_reservation_event_def phase_at_def
      split: option.splits if_splits)

theorem reassignment_establishes_current_recorded_lease:
  assumes own: "ownership_consistent(machine_state m)"
    and at: "reservation_at(machine_state m)(binding_key(request_binding r))=Some res"
    and permission: "current_use_allowed(lock_authority c) r"
    and duration: "duration>0"
    and binding: "reservation_binding res=request_binding r"
    and active: "active_reservation_phase(reservation_phase res)"
    and expired: "reservation_deadline res\<le>reservation_clock(machine_state m)"
  shows "owns_recorded_reservation c r (Suc(reservation_generation res))
    (asset_version(machine_state m))(machine_state(fst(reassign_worker c r duration m)))"
proof -
  have footprint: "\<forall>asset\<in>set(reservation_footprint res).
    asset_owner(machine_state m)asset=Some(binding_key(request_binding r))"
    using own at active unfolding ownership_consistent_def by blast
  show ?thesis using at permission duration binding active expired footprint
    by (auto simp: reassign_worker_def record_observation_def commit_reservation_event_def
        owns_recorded_reservation_def)
qed

lemma cancel_enabled_releases_all_owned_assets:
  assumes "owns_recorded_reservation c r g versions(machine_state m)"
    "phase_at(machine_state m)(binding_key(request_binding r))=Some Reservation_Held"
  shows "snd(cancel_before_dispatch c r g versions m)=Reservation_Released \<and>
    (\<forall>asset. asset_owner(machine_state(fst(cancel_before_dispatch c r g versions m)))asset
      \<noteq>Some(binding_key(request_binding r)))"
  using assms by (auto simp: cancel_before_dispatch_def record_observation_def commit_reservation_event_def
      finish_reservation_def set_phase_def)

theorem expired_held_reservation_recovers_in_two_calls:
  assumes own: "ownership_consistent(machine_state m)"
    and at: "reservation_at(machine_state m)(binding_key(request_binding r))=Some res"
    and permission: "current_use_allowed(lock_authority c) r"
    and duration: "duration>0"
    and binding: "reservation_binding res=request_binding r"
    and held: "reservation_phase res=Reservation_Held"
    and expired: "reservation_deadline res\<le>reservation_clock(machine_state m)"
  defines "taken \<equiv> fst(reassign_worker c r duration m)"
  shows "snd(reassign_worker c r duration m)=Worker_Reassigned \<and>
    snd(cancel_before_dispatch c r(Suc(reservation_generation res))(asset_version(machine_state m))taken)
      =Reservation_Released \<and>
    (\<forall>asset. asset_owner(machine_state(fst(cancel_before_dispatch c r(Suc(reservation_generation res))
      (asset_version(machine_state m))taken)))asset\<noteq>Some(binding_key(request_binding r)))"
proof -
  have active: "active_reservation_phase(reservation_phase res)" using held by simp
  have lease: "owns_recorded_reservation c r(Suc(reservation_generation res))
    (asset_version(machine_state m))(machine_state taken)"
    unfolding taken_def by (rule reassignment_establishes_current_recorded_lease[OF own at permission duration binding active expired])
  have takeover: "snd(reassign_worker c r duration m)=Worker_Reassigned"
    using expired_worker_reassignment_activates[OF at permission duration binding active expired] by blast
  have phase: "phase_at(machine_state taken)(binding_key(request_binding r))=Some Reservation_Held"
    using expired_worker_reassignment_activates[OF at permission duration binding active expired] held
    unfolding taken_def phase_at_def by simp
  show ?thesis using takeover cancel_enabled_releases_all_owned_assets[OF lease phase] by blast
qed

context source_attestation
begin

theorem recorded_credit_enables_one_call_cleanup:
  assumes "owns_recorded_reservation c r g versions(machine_state m)"
    "phase_at(machine_state m)(binding_key(request_binding r))=Some Source_Pending"
    "request_binding r\<in>set(credit_history(received_messages(machine_state m)))"
  shows "snd(reconcile_recorded_credit c r g versions m)=Reservation_Released \<and>
    (\<forall>asset. asset_owner(machine_state(fst(reconcile_recorded_credit c r g versions m)))asset
      \<noteq>Some(binding_key(request_binding r)))"
  using assms by (auto simp: reconcile_recorded_credit_def record_observation_def commit_reservation_event_def
      finish_reservation_def set_phase_def)

theorem reversed_evidence_enables_one_call_cleanup:
  assumes "owns_recorded_reservation c r g versions(machine_state m)"
    "phase_at(machine_state m)(binding_key(request_binding r))=Some Source_Pending"
    "reversed_source_evidence(lock_authority c)r(machine_state m)"
  shows "snd(release_to_source c r g versions m)=Reservation_Released \<and>
    (\<forall>asset. asset_owner(machine_state(fst(release_to_source c r g versions m)))asset
      \<noteq>Some(binding_key(request_binding r)))"
  using assms by (auto simp: release_to_source_def record_observation_def commit_reservation_event_def
      finish_reservation_def set_phase_def)

theorem expired_pending_credit_recovers_in_two_calls:
  assumes own: "ownership_consistent(machine_state m)"
    and at: "reservation_at(machine_state m)(binding_key(request_binding r))=Some res"
    and permission: "current_use_allowed(lock_authority c) r"
    and duration: "duration>0"
    and binding: "reservation_binding res=request_binding r"
    and pending: "reservation_phase res=Source_Pending"
    and expired: "reservation_deadline res\<le>reservation_clock(machine_state m)"
    and credit: "request_binding r\<in>set(credit_history(received_messages(machine_state m)))"
  defines "taken \<equiv> fst(reassign_worker c r duration m)"
  shows "snd(reassign_worker c r duration m)=Worker_Reassigned \<and>
    snd(reconcile_recorded_credit c r(Suc(reservation_generation res))(asset_version(machine_state m))taken)
      =Reservation_Released \<and>
    (\<forall>asset. asset_owner(machine_state(fst(reconcile_recorded_credit c r(Suc(reservation_generation res))
      (asset_version(machine_state m))taken)))asset\<noteq>Some(binding_key(request_binding r)))"
proof -
  have active: "active_reservation_phase(reservation_phase res)" using pending by simp
  have lease: "owns_recorded_reservation c r(Suc(reservation_generation res))
    (asset_version(machine_state m))(machine_state taken)"
    unfolding taken_def by (rule reassignment_establishes_current_recorded_lease[OF own at permission duration binding active expired])
  have takeover: "snd(reassign_worker c r duration m)=Worker_Reassigned"
    using expired_worker_reassignment_activates[OF at permission duration binding active expired] by blast
  have phase: "phase_at(machine_state taken)(binding_key(request_binding r))=Some Source_Pending"
    using reassignment_preserves_phase_and_evidence[of c r duration m "binding_key(request_binding r)"]
      at pending unfolding taken_def phase_at_def by simp
  have credited: "request_binding r\<in>set(credit_history(received_messages(machine_state taken)))"
    using reassignment_preserves_phase_and_evidence[of c r duration m "binding_key(request_binding r)"]
      credit unfolding taken_def by simp
  show ?thesis using takeover recorded_credit_enables_one_call_cleanup[OF lease phase credited] by blast
qed

theorem expired_pending_reversal_recovers_in_two_calls:
  assumes own: "ownership_consistent(machine_state m)"
    and at: "reservation_at(machine_state m)(binding_key(request_binding r))=Some res"
    and permission: "current_use_allowed(lock_authority c) r"
    and duration: "duration>0"
    and binding: "reservation_binding res=request_binding r"
    and pending: "reservation_phase res=Source_Pending"
    and expired: "reservation_deadline res\<le>reservation_clock(machine_state m)"
    and reversal: "reversed_source_evidence(lock_authority c)r(machine_state m)"
  defines "taken \<equiv> fst(reassign_worker c r duration m)"
  shows "snd(reassign_worker c r duration m)=Worker_Reassigned \<and>
    snd(release_to_source c r(Suc(reservation_generation res))(asset_version(machine_state m))taken)
      =Reservation_Released \<and>
    (\<forall>asset. asset_owner(machine_state(fst(release_to_source c r(Suc(reservation_generation res))
      (asset_version(machine_state m))taken)))asset\<noteq>Some(binding_key(request_binding r)))"
proof -
  have active: "active_reservation_phase(reservation_phase res)" using pending by simp
  have lease: "owns_recorded_reservation c r(Suc(reservation_generation res))
    (asset_version(machine_state m))(machine_state taken)"
    unfolding taken_def by (rule reassignment_establishes_current_recorded_lease[OF own at permission duration binding active expired])
  have takeover: "snd(reassign_worker c r duration m)=Worker_Reassigned"
    using expired_worker_reassignment_activates[OF at permission duration binding active expired] by blast
  have phase: "phase_at(machine_state taken)(binding_key(request_binding r))=Some Source_Pending"
    using reassignment_preserves_phase_and_evidence[of c r duration m "binding_key(request_binding r)"]
      at pending unfolding taken_def phase_at_def by simp
  have evidence: "reversed_source_evidence(lock_authority c)r(machine_state taken)"
    using reassignment_preserves_phase_and_evidence[of c r duration m "binding_key(request_binding r)"]
      reversal unfolding taken_def reversed_source_evidence_def by simp
  show ?thesis using takeover reversed_evidence_enables_one_call_cleanup[OF lease phase evidence] by blast
qed

end

theorem authoritative_non_effect_enables_one_call_cleanup:
  assumes "owns_recorded_reservation c r g versions(machine_state m)"
    "phase_at(machine_state m)(binding_key(request_binding r))\<in>{Some Source_Submitted,Some Source_Pending}"
    "\<not>source_was_debited(machine_state m)(binding_key(request_binding r))"
    "context_endpoint(lock_authority c)=fst(binding_key(request_binding r))"
  shows "snd(fence_unexecuted_source c r g versions m)=Source_Fenced \<and>
    (\<forall>asset. asset_owner(machine_state(fst(fence_unexecuted_source c r g versions m)))asset
      \<noteq>Some(binding_key(request_binding r)))"
  using assms by (auto simp: fence_unexecuted_source_def record_observation_def commit_reservation_event_def
      finish_reservation_def set_phase_def)

section \<open>Executed Lease and Acquisition Controls\<close>

definition sample_new_worker_request :: execution_request where
  "sample_new_worker_request=(sample_request 17)\<lparr>request_caller:=8\<rparr>"

definition sample_new_worker_context :: lock_context where
  "sample_new_worker_context=(sample_source_context ACTIVE)\<lparr>
    lock_authority:=(lock_authority(sample_source_context ACTIVE))\<lparr>context_permissions:={p. fst p\<in>{7,8}}\<rparr>,
    lock_write_permissions:={(8,17,12)}\<rparr>"

definition sample_expired_held :: reservation_machine where
  "sample_expired_held=advance_reservation_time 10 sample_held_for_write"

definition sample_taken_over :: reservation_machine where
  "sample_taken_over=fst(reassign_worker sample_new_worker_context sample_new_worker_request 5 sample_expired_held)"

lemmas sample_takeover_defs = sample_new_worker_request_def sample_new_worker_context_def
  sample_expired_held_def sample_taken_over_def sample_held_for_write_def
  sample_data_defs acquire_reservation_def advance_reservation_time_def reassign_worker_def
  record_observation_def commit_reservation_event_def Let_def

lemma expired_held_takeover_control_activates:
  "snd(reassign_worker sample_new_worker_context sample_new_worker_request 5 sample_expired_held)=Worker_Reassigned \<and>
    (\<exists>res. reservation_at(machine_state sample_taken_over)(0,17)=Some res \<and>
      reservation_worker res=8 \<and> reservation_generation res=1 \<and>
      reservation_deadline res=15 \<and> reservation_binding res=sample_binding 17) \<and>
    asset_owner(machine_state sample_taken_over)17=Some(0,17)"
  by (simp add: sample_takeover_defs)

lemma replaced_generation_control_rejects:
  "snd(write_asset_data sample_new_worker_context sample_new_worker_request 0(\<lambda>_.0)12
    sample_taken_over)=Request_Rejected \<and>
    snd(write_asset_data sample_new_worker_context sample_new_worker_request 1(\<lambda>_.0)12
    sample_taken_over)=Data_Updated"
  by (simp add: sample_takeover_defs write_asset_data_def)

lemma current_worker_cleanup_control_activates:
  "snd(cancel_before_dispatch sample_new_worker_context sample_new_worker_request 1(\<lambda>_.0)
    sample_taken_over)=Reservation_Released \<and>
    asset_owner(machine_state(fst(cancel_before_dispatch sample_new_worker_context
      sample_new_worker_request 1(\<lambda>_.0)sample_taken_over)))17=None"
  by (simp add: sample_takeover_defs cancel_before_dispatch_def)

definition sample_pair_context :: lock_context where
  "sample_pair_context=(sample_source_context ACTIVE)\<lparr>
    lock_dependencies:=(\<lambda>asset. if asset=17 then [30] else if asset=30 then [17] else [])\<rparr>"

definition sample_pair_held :: reservation_machine where
  "sample_pair_held=fst(acquire_reservation sample_pair_context(sample_request 17)(\<lambda>_.0)10 sample_initial)"

lemma opposite_order_acquisition_keeps_no_partial_reservation:
  "snd(acquire_reservation sample_pair_context(sample_request 30)(\<lambda>_.0)10 sample_pair_held)=Reservation_Busy \<and>
    reservation_at(machine_state(fst(acquire_reservation sample_pair_context(sample_request 30)
      (\<lambda>_.0)10 sample_pair_held)))(0,30)=None \<and>
    asset_owner(machine_state sample_pair_held)17=Some(0,17) \<and>
    asset_owner(machine_state sample_pair_held)30=Some(0,17)"
  by (simp add: sample_pair_context_def sample_pair_held_def sample_data_defs acquire_reservation_def
      record_observation_def commit_reservation_event_def Let_def)

text \<open>The call bounds apply once the stated conditions hold. They require
  a current authorized caller, fresh stored-footprint versions, an unexpired
  assigned lease, and execution of the cleanup call. A scheduler must eventually
  execute enabled recovery calls; timely external evidence is a separate
  assumption. No wall-clock or unconditional eventual-completion bound follows
  for a submitted source effect whose outcome remains unknown. Advancing time
  grants neither source-reversal evidence nor destination delivery authority.\<close>

end
