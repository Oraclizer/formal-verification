(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Access
  imports Reservation_Scenarios Reservation_Frame
begin

section \<open>Completed Reads and Current Authorization\<close>

lemma current_read_activates_without_reservation:
  "snd(read_source_data(sample_source_context ACTIVE)(sample_request 17)sample_initial)=Value_Response 0"
  by (simp add: read_source_data_def current_read_allowed_def sample_data_defs
      record_observation_def)

lemma current_read_completes_busy_on_reserved_asset:
  "snd(read_source_data(sample_source_context ACTIVE)(sample_request 17)(sample_burnt 17))=Reservation_Busy"
  by (simp add: read_source_data_def current_read_allowed_def sample_data_defs sample.protocol_definitions
      sample.run_reservations.simps sample.reservation_step.simps record_observation_def
      commit_reservation_event_def Let_def)

lemma read_only_caller_cannot_acquire:
  "snd(read_source_data(sample_source_context ACTIVE)((sample_request 17)\<lparr>request_caller:=8\<rparr>)
      sample_initial)=Value_Response 0 \<and>
   snd(acquire_reservation(sample_source_context ACTIVE)((sample_request 17)\<lparr>request_caller:=8\<rparr>)
      (\<lambda>_.0)10 sample_initial)=Request_Rejected"
  by (simp add: read_source_data_def current_read_allowed_def acquire_reservation_def sample_data_defs
      record_observation_def Let_def)

lemma stale_read_version_is_rejected:
  "snd(read_source_data(sample_source_context ACTIVE)((sample_request 17)\<lparr>request_version:=3\<rparr>)
    sample_initial)=Request_Rejected"
  by (simp add: read_source_data_def current_read_allowed_def sample_data_defs record_observation_def)

lemma busy_read_retains_state_and_completes_observation:
  assumes "snd(read_source_data c r m)=Reservation_Busy"
  shows "machine_state(fst(read_source_data c r m))=machine_state m \<and>
    length(machine_observations(fst(read_source_data c r m)))=Suc(length(machine_observations m))"
  using assms by (auto simp: read_source_data_def record_observation_def)

lemma stale_authority_cannot_restore_source:
  "snd(sample.release_to_source
    ((sample_source_context ACTIVE)\<lparr>lock_authority:=
      (lock_authority(sample_source_context ACTIVE))\<lparr>context_authority_epoch:=10\<rparr>\<rparr>)
    (sample_request 22)0(\<lambda>_.0)sample_return_ready)=Request_Rejected"
  by (simp add: sample_return_ready_def sample_data_defs sample_auth_defs sample.protocol_definitions
      sample.run_reservations.simps sample.reservation_step.simps record_observation_def
      commit_reservation_event_def Let_def)

definition current_other_caller_context where
  "current_other_caller_context=(sample_source_context ACTIVE)\<lparr>lock_authority:=
    (lock_authority(sample_source_context ACTIVE))\<lparr>context_permissions:=UNIV\<rparr>\<rparr>"

lemma current_permission_does_not_replace_worker_ownership:
  "current_use_allowed(lock_authority current_other_caller_context)
      ((sample_request 22)\<lparr>request_caller:=8\<rparr>) \<and>
    snd(sample.release_to_source current_other_caller_context
      ((sample_request 22)\<lparr>request_caller:=8\<rparr>)0(\<lambda>_.0)sample_return_ready)=Request_Rejected"
  by (simp add: current_other_caller_context_def sample_return_ready_def sample_data_defs sample_auth_defs
      sample.protocol_definitions sample.run_reservations.simps sample.reservation_step.simps
      record_observation_def commit_reservation_event_def Let_def)

text \<open>Busy is a completed response with a recorded observation. Read
  permission is distinct from permission to acquire or mutate a reservation.
  A newly permitted caller still needs the current assigned worker lease;
  authority does not reset that ownership or the immutable source identity.\<close>

definition write_to_unrelated_asset where
  "write_to_unrelated_asset c r g versions value victim m =
    (if owns_current_reservation c r g versions(machine_state m) \<and>
        phase_at(machine_state m)(binding_key(request_binding r))=Some Reservation_Held \<and>
        (request_caller r,binding_asset(request_binding r),value)\<in>lock_write_permissions c
     then record_observation r Data_Updated(commit_reservation_event
       (Data_Event victim value(Suc(asset_version(machine_state m)victim)))m)
     else record_observation r Request_Rejected m)"

lemma correct_write_preserves_unrelated_asset:
  "asset_value(machine_state(fst(write_asset_data(sample_source_context ACTIVE)(sample_request 17)
      0(\<lambda>_.0)9 sample_held_for_write)))30=0"
  by (simp add: sample_held_for_write_def sample_data_defs acquire_reservation_def write_asset_data_def
      record_observation_def commit_reservation_event_def Let_def)

lemma wrong_target_write_changes_unrelated_asset:
  "snd(write_to_unrelated_asset(sample_source_context ACTIVE)(sample_request 17)
      0(\<lambda>_.0)9 30 sample_held_for_write)=Data_Updated \<and>
   asset_value(machine_state(fst(write_to_unrelated_asset(sample_source_context ACTIVE)(sample_request 17)
      0(\<lambda>_.0)9 30 sample_held_for_write)))30=9"
  by (simp add: write_to_unrelated_asset_def sample_held_for_write_def sample_data_defs acquire_reservation_def
      record_observation_def commit_reservation_event_def Let_def)

definition independent_asset_context where
  "independent_asset_context=(sample_source_context ACTIVE)\<lparr>lock_write_permissions:={(7,30,12)}\<rparr>"

definition independent_asset_acquired where
  "independent_asset_acquired=fst(acquire_reservation independent_asset_context(sample_request 30)
    (\<lambda>_.0)10(sample_burnt 17))"

lemma unrelated_asset_makes_progress_during_source_pending:
  "snd(acquire_reservation independent_asset_context(sample_request 30)(\<lambda>_.0)10(sample_burnt 17))=
      Reservation_Acquired \<and>
   snd(write_asset_data independent_asset_context(sample_request 30)0(\<lambda>_.0)12 independent_asset_acquired)=
      Data_Updated \<and>
   asset_value(machine_state(fst(write_asset_data independent_asset_context(sample_request 30)
      0(\<lambda>_.0)12 independent_asset_acquired)))30=12 \<and>
   asset_owner(machine_state(fst(write_asset_data independent_asset_context(sample_request 30)
      0(\<lambda>_.0)12 independent_asset_acquired)))17=Some(0,17) \<and>
   source_effects(machine_state(fst(write_asset_data independent_asset_context(sample_request 30)
      0(\<lambda>_.0)12 independent_asset_acquired)))=[sample_binding 17]"
  by (simp add: independent_asset_context_def independent_asset_acquired_def sample_data_defs
      sample.protocol_definitions sample.run_reservations.simps sample.reservation_step.simps
      record_observation_def commit_reservation_event_def Let_def)

end
