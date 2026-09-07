(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Frame
  imports Reservation_Examples
begin

section \<open>Current Writes and Asset Frames\<close>

lemma current_owner_at_primary:
  assumes "owns_current_reservation c r g versions s"
  shows "asset_owner s(binding_asset(request_binding r))=Some(binding_key(request_binding r)) \<and>
    versions(binding_asset(request_binding r))=asset_version s(binding_asset(request_binding r))"
  using assms unfolding owns_current_reservation_def owns_recorded_reservation_def
    required_footprint_def by auto

lemma successful_write_guard:
  "snd(write_asset_data c r g versions value m)=Data_Updated \<longleftrightarrow>
    owns_current_reservation c r g versions(machine_state m) \<and>
    phase_at(machine_state m)(binding_key(request_binding r))=Some Reservation_Held \<and>
    (request_caller r,binding_asset(request_binding r),value)\<in>lock_write_permissions c"
  by (simp add: write_asset_data_def record_observation_def)

theorem successful_write_current_owner_and_version:
  assumes "snd(write_asset_data c r g versions value m)=Data_Updated"
  shows "current_use_allowed(lock_authority c) r \<and>
    asset_owner(machine_state m)(binding_asset(request_binding r))=Some(binding_key(request_binding r)) \<and>
    versions(binding_asset(request_binding r))=asset_version(machine_state m)(binding_asset(request_binding r))"
  using assms current_owner_at_primary[of c r g versions "machine_state m"]
  by (auto simp: successful_write_guard owns_current_reservation_def owns_recorded_reservation_def)

lemma successful_write_value_and_version:
  assumes "snd(write_asset_data c r g versions value m)=Data_Updated"
  shows "asset_value(machine_state(fst(write_asset_data c r g versions value m)))
       (binding_asset(request_binding r))=value \<and>
    asset_version(machine_state(fst(write_asset_data c r g versions value m)))
       (binding_asset(request_binding r))=Suc(asset_version(machine_state m)(binding_asset(request_binding r)))"
  using successful_write_guard[THEN iffD1,OF assms]
  by (simp add: write_asset_data_def record_observation_def commit_reservation_event_def)

theorem successful_write_rejects_stale_version:
  assumes first: "snd(write_asset_data c r g versions value m)=Data_Updated"
    and same_asset: "binding_asset(request_binding next)=binding_asset(request_binding r)"
  shows "snd(write_asset_data next_context next next_generation versions next_value
    (fst(write_asset_data c r g versions value m)))=Request_Rejected"
proof -
  let ?m = "fst(write_asset_data c r g versions value m)"
  have old: "versions(binding_asset(request_binding r))=
    asset_version(machine_state m)(binding_asset(request_binding r))"
    using successful_write_current_owner_and_version[OF first] by blast
  have new: "asset_version(machine_state ?m)(binding_asset(request_binding r))=
    Suc(asset_version(machine_state m)(binding_asset(request_binding r)))"
    using successful_write_value_and_version[OF first] by blast
  have "\<not>owns_current_reservation next_context next next_generation versions(machine_state ?m)"
    using current_owner_at_primary[of next_context "next" next_generation versions "machine_state ?m"]
      old new same_asset by auto
  then show ?thesis by (simp add: write_asset_data_def record_observation_def)
qed

theorem write_preserves_other_asset_data:
  assumes "asset\<noteq>binding_asset(request_binding r)"
  shows "asset_value(machine_state(fst(write_asset_data c r g versions value m)))asset=
      asset_value(machine_state m)asset \<and>
    asset_version(machine_state(fst(write_asset_data c r g versions value m)))asset=
      asset_version(machine_state m)asset"
  using assms by (simp add: write_asset_data_def record_observation_def commit_reservation_event_def)

theorem write_preserves_financial_and_reservation_state:
  fixes c :: lock_context and r :: execution_request and g :: nat
    and versions :: "nat \<Rightarrow> nat" and "value" :: nat and m :: reservation_machine
  defines "after \<equiv> machine_state(fst(write_asset_data c r g versions value m))"
  shows "asset_owner after=asset_owner(machine_state m) \<and>
    reservation_at after=reservation_at(machine_state m) \<and>
    source_units after=source_units(machine_state m) \<and>
    destination_units after=destination_units(machine_state m) \<and>
    funded_units after=funded_units(machine_state m) \<and>
    source_effects after=source_effects(machine_state m) \<and>
    issued_certificates after=issued_certificates(machine_state m) \<and>
    received_messages after=received_messages(machine_state m) \<and>
    lawful_descendants after=lawful_descendants(machine_state m) \<and>
    reservation_clock after=reservation_clock(machine_state m)"
  unfolding after_def by (simp add: write_asset_data_def record_observation_def commit_reservation_event_def)

theorem foreign_reservation_cannot_overwrite_owned_asset:
  assumes owner: "asset_owner(machine_state m)asset=Some key"
    and foreign: "binding_key(request_binding r)\<noteq>key"
  shows "asset_value(machine_state(fst(write_asset_data c r g versions value m)))asset=
      asset_value(machine_state m)asset \<and>
    asset_version(machine_state(fst(write_asset_data c r g versions value m)))asset=
      asset_version(machine_state m)asset"
proof (cases "asset=binding_asset(request_binding r)")
  case True
  have "\<not>owns_current_reservation c r g versions(machine_state m)"
    using current_owner_at_primary[of c r g versions "machine_state m"] owner foreign True by auto
  then show ?thesis by (simp add: write_asset_data_def record_observation_def)
next
  case False
  then show ?thesis by (rule write_preserves_other_asset_data)
qed

lemma rejected_write_preserves_state_and_journal:
  assumes "snd(write_asset_data c r g versions value m)=Request_Rejected"
  shows "machine_state(fst(write_asset_data c r g versions value m))=machine_state m \<and>
    machine_journal(fst(write_asset_data c r g versions value m))=machine_journal m"
  using assms by (auto simp: write_asset_data_def record_observation_def commit_reservation_event_def)

lemma acquisition_failure_is_atomic:
  assumes "snd(acquire_reservation c r versions duration m)\<in>{Request_Rejected,Reservation_Busy}"
  shows "machine_state(fst(acquire_reservation c r versions duration m))=machine_state m \<and>
    machine_journal(fst(acquire_reservation c r versions duration m))=machine_journal m"
  using assms by (auto simp: acquire_reservation_def record_observation_def Let_def)

lemma acquisition_preserves_outside_footprint:
  assumes "asset\<notin>set(required_footprint c(request_binding r))"
  shows "asset_owner(machine_state(fst(acquire_reservation c r versions duration m)))asset=
    asset_owner(machine_state m)asset"
  using assms by (simp add: acquire_reservation_def record_observation_def commit_reservation_event_def Let_def)

lemma finished_reservation_preserves_foreign_owner:
  assumes "asset_owner s asset\<noteq>Some key"
  shows "asset_owner(finish_reservation key phase s)asset=asset_owner s asset"
  using assms by (simp add: finish_reservation_def set_phase_def)

lemma finished_reservation_preserves_data:
  "asset_value(finish_reservation key phase s)=asset_value s \<and>
    asset_version(finish_reservation key phase s)=asset_version s"
  by (simp add: finish_reservation_def set_phase_def)

theorem cancellation_does_not_undo_committed_data:
  "asset_value(machine_state(fst(cancel_before_dispatch c r g versions m)))=asset_value(machine_state m) \<and>
    asset_version(machine_state(fst(cancel_before_dispatch c r g versions m)))=asset_version(machine_state m)"
  by (simp add: cancel_before_dispatch_def record_observation_def commit_reservation_event_def
      finish_reservation_def set_phase_def)

theorem fence_does_not_undo_committed_data:
  "asset_value(machine_state(fst(fence_unexecuted_source c r g versions m)))=asset_value(machine_state m) \<and>
    asset_version(machine_state(fst(fence_unexecuted_source c r g versions m)))=asset_version(machine_state m)"
  by (simp add: fence_unexecuted_source_def record_observation_def commit_reservation_event_def
      finish_reservation_def set_phase_def)

lemma worker_reassignment_preserves_asset_state:
  fixes c :: lock_context and r :: execution_request and duration :: nat and m :: reservation_machine
  defines "after \<equiv> machine_state(fst(reassign_worker c r duration m))"
  shows "asset_owner after=asset_owner(machine_state m) \<and>
    asset_value after=asset_value(machine_state m) \<and>
    asset_version after=asset_version(machine_state m) \<and>
    source_units after=source_units(machine_state m) \<and>
    destination_units after=destination_units(machine_state m) \<and>
    funded_units after=funded_units(machine_state m) \<and>
    source_effects after=source_effects(machine_state m) \<and>
    received_messages after=received_messages(machine_state m)"
  unfolding after_def by (auto simp: reassign_worker_def record_observation_def commit_reservation_event_def
      split: option.splits)

lemma reassignment_invalidates_previous_generation:
  assumes at: "reservation_at(machine_state m)(binding_key(request_binding r))=Some res"
    and success: "snd(reassign_worker c r duration m)=Worker_Reassigned"
    and same: "binding_key(request_binding old)=binding_key(request_binding r)"
  shows "\<not>owns_recorded_reservation old_context old(reservation_generation res)versions
    (machine_state(fst(reassign_worker c r duration m)))"
proof -
  let ?taken = "machine_state(fst(reassign_worker c r duration m))"
  let ?assigned = "res\<lparr>reservation_worker:=request_caller r,
    reservation_generation:=Suc(reservation_generation res),
    reservation_deadline:=reservation_clock(machine_state m)+duration\<rparr>"
  have lookup: "reservation_at ?taken(binding_key(request_binding r))=Some ?assigned"
    using at success
    by (auto simp: reassign_worker_def record_observation_def commit_reservation_event_def
        split: if_splits)
  have old_lookup: "reservation_at ?taken(binding_key(request_binding old))=Some ?assigned"
    using lookup same by simp
  show ?thesis by (simp add: owns_recorded_reservation_def old_lookup)
qed

context source_attestation
begin

theorem reservation_step_never_decreases_data_version:
  assumes journal: "journal_agreement balances m"
  shows "asset_version(machine_state m)asset \<le>
    asset_version(machine_state(reservation_step balances action m))asset"
  using restart_reconstructs_committed_state[OF journal]
  by (cases action)
     (auto simp: protocol_definitions Let_def record_observation_def commit_reservation_event_def
       set_phase_def finish_reservation_def split: option.splits message_reply.splits)

theorem finite_interleaving_never_decreases_data_version:
  assumes "journal_agreement balances m"
  shows "asset_version(machine_state m)asset \<le>
    asset_version(machine_state(run_reservations balances actions m))asset"
  using assms
proof (induction actions arbitrary:m)
  case Nil
  then show ?case by simp
next
  case (Cons action actions)
  have step: "asset_version(machine_state m)asset \<le>
    asset_version(machine_state(reservation_step balances action m))asset"
    by (rule reservation_step_never_decreases_data_version[OF Cons.prems])
  have rest: "asset_version(machine_state(reservation_step balances action m))asset \<le>
    asset_version(machine_state(run_reservations balances actions(reservation_step balances action m)))asset"
    by (rule Cons.IH, rule reservation_step_preserves_journal[OF Cons.prems])
  show ?case using order_trans[OF step rest] by simp
qed

theorem stale_version_stays_invalid_after_finite_continuation:
  assumes first: "snd(write_asset_data c r g versions value m)=Data_Updated"
    and journal: "journal_agreement balances m"
    and same: "binding_asset(request_binding next)=binding_asset(request_binding r)"
  shows "snd(write_asset_data next_context next next_generation versions next_value
    (run_reservations balances continuation(fst(write_asset_data c r g versions value m))))=Request_Rejected"
proof -
  let ?written = "fst(write_asset_data c r g versions value m)"
  let ?later = "run_reservations balances continuation ?written"
  have old: "versions(binding_asset(request_binding r))=
    asset_version(machine_state m)(binding_asset(request_binding r))"
    using successful_write_current_owner_and_version[OF first] by blast
  have new: "asset_version(machine_state ?written)(binding_asset(request_binding r))=
    Suc(asset_version(machine_state m)(binding_asset(request_binding r)))"
    using successful_write_value_and_version[OF first] by blast
  have written_journal: "journal_agreement balances ?written"
    using reservation_step_preserves_journal[OF journal,of "Write_Action c r g versions value"] by simp
  have monotone: "asset_version(machine_state ?written)(binding_asset(request_binding r)) \<le>
    asset_version(machine_state ?later)(binding_asset(request_binding r))"
    by (rule finite_interleaving_never_decreases_data_version[OF written_journal])
  have "\<not>owns_current_reservation next_context next next_generation versions(machine_state ?later)"
    using current_owner_at_primary[of next_context "next" next_generation versions "machine_state ?later"]
      old new monotone same by auto
  then show ?thesis by (simp add: write_asset_data_def record_observation_def)
qed

end

section \<open>Executed Update Controls\<close>

definition sample_held_for_write :: reservation_machine where
  "sample_held_for_write=fst(acquire_reservation(sample_source_context ACTIVE)(sample_request 17)
    (\<lambda>_.0)10 sample_initial)"

definition sample_written_nine :: reservation_machine where
  "sample_written_nine=fst(write_asset_data(sample_source_context ACTIVE)(sample_request 17)
    0(\<lambda>_.0)9 sample_held_for_write)"

definition write_without_expected_version_check :: "lock_context \<Rightarrow> execution_request \<Rightarrow>
  nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> reservation_machine \<Rightarrow>
  reservation_machine \<times> reservation_reply" where
  "write_without_expected_version_check c r g supplied value m =
    write_asset_data c r g(asset_version(machine_state m))value m"

lemma current_write_control_activates:
  "snd(write_asset_data(sample_source_context ACTIVE)(sample_request 17)0(\<lambda>_.0)9
    sample_held_for_write)=Data_Updated \<and>
    asset_value(machine_state sample_written_nine)17=9 \<and>
    asset_version(machine_state sample_written_nine)17=1"
  by (simp add: sample_held_for_write_def sample_written_nine_def sample_data_defs
      acquire_reservation_def write_asset_data_def record_observation_def commit_reservation_event_def Let_def)

lemma stale_write_control_rejects:
  "snd(write_asset_data(sample_source_context ACTIVE)(sample_request 17)0(\<lambda>_.0)12
    sample_written_nine)=Request_Rejected \<and>
    asset_value(machine_state(fst(write_asset_data(sample_source_context ACTIVE)(sample_request 17)
      0(\<lambda>_.0)12 sample_written_nine)))17=9"
  by (simp add: sample_held_for_write_def sample_written_nine_def sample_data_defs
      acquire_reservation_def write_asset_data_def record_observation_def commit_reservation_event_def Let_def)

lemma omitted_expected_version_overwrites_committed_value:
  "snd(write_without_expected_version_check(sample_source_context ACTIVE)(sample_request 17)
    0(\<lambda>_.0)12 sample_written_nine)=Data_Updated \<and>
    asset_value(machine_state(fst(write_without_expected_version_check(sample_source_context ACTIVE)
      (sample_request 17)0(\<lambda>_.0)12 sample_written_nine)))17=12 \<and>
    asset_version(machine_state(fst(write_without_expected_version_check(sample_source_context ACTIVE)
      (sample_request 17)0(\<lambda>_.0)12 sample_written_nine)))17=2"
  by (simp add: write_without_expected_version_check_def sample_held_for_write_def
      sample_written_nine_def sample_data_defs acquire_reservation_def write_asset_data_def
      record_observation_def commit_reservation_event_def Let_def)

lemma refreshed_expected_version_allows_next_write:
  "snd(write_asset_data(sample_source_context ACTIVE)(sample_request 17)
    0(asset_version(machine_state sample_written_nine))12 sample_written_nine)=Data_Updated"
  by (simp add: sample_held_for_write_def sample_written_nine_def sample_data_defs
      acquire_reservation_def write_asset_data_def record_observation_def commit_reservation_event_def Let_def)

text \<open>A successful data write is committed application state. Its version
  increment makes another request with the same expected version fail, even
  if the later request presents a newly authorized caller. Reservation cleanup
  does not roll back an earlier successful write. These statements concern
  the atomic model operations; the runtime must implement the version check
  and write together and provide the current permission and dependency view.\<close>

end
