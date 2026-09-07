(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Scenarios
  imports Reservation_Examples Reservation_Evidence
begin

section \<open>Release, Source Fencing and Completed Credit\<close>

declare sample.reversed_source_evidence_def [simp]

definition sample_return_ready where
  "sample_return_ready=sample.publish_source_certificate(sample_certificate 22)(sample_burnt 22)"

lemma actual_reversal_release_activates:
  "snd(sample.release_to_source(sample_source_context ACTIVE)(sample_request 22)0(\<lambda>_.0)
      sample_return_ready)=Reservation_Released \<and>
   source_units(machine_state(fst(sample.release_to_source(sample_source_context ACTIVE)
      (sample_request 22)0(\<lambda>_.0)sample_return_ready)))(0,22)=5 \<and>
   phase_at(machine_state(fst(sample.release_to_source(sample_source_context ACTIVE)
      (sample_request 22)0(\<lambda>_.0)sample_return_ready)))(0,22)=Some Source_Returned"
  by (simp add: sample_return_ready_def sample_data_defs sample_auth_defs sample.protocol_definitions
      sample.run_reservations.simps sample.reservation_step.simps record_observation_def
      commit_reservation_event_def Let_def)

lemma valid_finalized_evidence_cannot_refund:
  "snd(sample.release_to_source(sample_source_context ACTIVE)(sample_request 17)0(\<lambda>_.0)
      (sample.publish_source_certificate(sample_certificate 17)(sample_burnt 17)))=Request_Rejected"
  by (simp add: sample_data_defs sample_auth_defs sample.protocol_definitions
      sample.run_reservations.simps sample.reservation_step.simps record_observation_def
      commit_reservation_event_def Let_def)

definition sample_submitted where
  "sample_submitted=fst(dispatch_source(sample_source_context ACTIVE)(sample_request 17)0(\<lambda>_.0)
    (fst(acquire_reservation(sample_source_context ACTIVE)(sample_request 17)(\<lambda>_.0)10 sample_initial)))"

lemma authoritative_fence_activates_and_late_source_is_rejected:
  "snd(fence_unexecuted_source(sample_source_context ACTIVE)(sample_request 17)0(\<lambda>_.0)
      sample_submitted)=Source_Fenced \<and>
   snd(execute_source_effect(sample_source_context ACTIVE)(sample_request 17)0(\<lambda>_.0)
     (fst(fence_unexecuted_source(sample_source_context ACTIVE)(sample_request 17)0(\<lambda>_.0)
       sample_submitted)))=Request_Rejected \<and>
   source_units(machine_state(fst(fence_unexecuted_source(sample_source_context ACTIVE)
     (sample_request 17)0(\<lambda>_.0)sample_submitted)))(0,17)=10"
  by (simp add: sample_submitted_def sample_data_defs sample.protocol_definitions
      record_observation_def commit_reservation_event_def Let_def)

lemma burnt_source_cannot_use_no_effect_fence:
  "snd(fence_unexecuted_source(sample_source_context ACTIVE)(sample_request 17)0(\<lambda>_.0)
      (sample_burnt 17))=Request_Rejected"
  by (simp add: sample_data_defs sample.protocol_definitions sample.run_reservations.simps
      sample.reservation_step.simps record_observation_def commit_reservation_event_def Let_def)

definition sample_confirmed_record :: "nat \<Rightarrow> asset_reservation" where
  "sample_confirmed_record event=\<lparr>reservation_binding=sample_binding event,
    reservation_footprint=[binding_asset(sample_binding event)],reservation_worker=7,
    reservation_generation=0,reservation_deadline=10,reservation_phase=Source_Confirmed\<rparr>"

lemma sample_credited_state:
  "machine_state sample_credited=(initial_reservation_state sample_balances)\<lparr>
    reservation_at:=(\<lambda>_.None)((0,17):=Some(sample_confirmed_record 17)),
    source_units:=sample_balances((0,17):=5),
    source_effects:=[sample_binding 17],issued_certificates:=[sample_certificate 17],
    received_messages:=record_credit(sample_binding 17)empty_message_state,
    destination_units:=(\<lambda>_.0)((2,17,3):=5),funded_units:=(\<lambda>_.0)(((0,17),(2,17,3)):=5)\<rparr>"
  by (simp add: sample_confirmed_record_def sample_data_defs sample_auth_defs sample.protocol_definitions
      sample.published_receive_expansion sample.run_reservations.simps sample.reservation_step.simps
      record_observation_def commit_reservation_event_def record_credit_def empty_message_state_def Let_def fun_eq_iff)

context source_attestation
begin

definition publication_without_source_origin where
  "publication_without_source_origin cert m =
    (if certificate_ok cert \<and> statement_status(certificate_statement cert)\<noteq>Observed
     then commit_reservation_event(Certificate_Event cert)m else m)"

definition release_without_reversal_evidence where
  "release_without_reversal_evidence c r g versions m =
    (if owns_recorded_reservation c r g versions(machine_state m) \<and>
        phase_at(machine_state m)(binding_key(request_binding r))=Some Source_Pending
     then record_observation r Reservation_Released(commit_reservation_event(Return_Event(request_binding r))m)
     else record_observation r Request_Rejected m)"

end

lemma removing_publication_origin_creates_unfunded_credit:
  "source_effects(machine_state(fst(sample.deliver_reserved_credit Validated_Route example_context
    (sample_request 17)(sample.publication_without_source_origin(sample_certificate 17)sample_initial))))=[] \<and>
   credit_history(received_messages(machine_state(fst(sample.deliver_reserved_credit Validated_Route example_context
    (sample_request 17)(sample.publication_without_source_origin(sample_certificate 17)sample_initial)))))=[sample_binding 17]"
  by (simp add: sample.publication_without_source_origin_def sample_data_defs sample_auth_defs
      sample.protocol_definitions sample.published_receive_expansion record_observation_def
      commit_reservation_event_def record_credit_def empty_message_state_def Let_def)

lemma publication_origin_control_rejects_unfunded_delivery:
  "snd(sample.deliver_reserved_credit Validated_Route example_context(sample_request 17)
    (sample.publish_source_certificate(sample_certificate 17)sample_initial))=Delivery_Response Message_Rejected"
  by (simp add: sample_data_defs sample_auth_defs sample.protocol_definitions sample.published_receive_expansion
      record_observation_def commit_reservation_event_def empty_message_state_def Let_def)

definition sample_credit_before_ack where
  "sample_credit_before_ack=fst(sample.deliver_reserved_credit Validated_Route example_context(sample_request 17)
    (sample.publish_source_certificate(sample_certificate 17)(sample_burnt 17)))"

lemma credit_without_ack_is_still_pending:
  "phase_at(machine_state sample_credit_before_ack)(0,17)=Some Source_Pending \<and>
   credit_history(received_messages(machine_state sample_credit_before_ack))=[sample_binding 17]"
  by (simp add: sample_credit_before_ack_def sample_data_defs sample_auth_defs sample.protocol_definitions
      sample.published_receive_expansion sample.run_reservations.simps sample.reservation_step.simps
      record_observation_def commit_reservation_event_def record_credit_def empty_message_state_def Let_def)

lemma removing_reversal_evidence_duplicates_money_despite_both_once_counts:
  defines "bad \<equiv> fst(sample.release_without_reversal_evidence(sample_source_context ACTIVE)
    (sample_request 17)0(\<lambda>_.0)sample_credit_before_ack)"
  shows "source_units(machine_state bad)(0,17)=10 \<and>
    destination_units(machine_state bad)(2,17,3)=5 \<and>
    source_effects(machine_state bad)=[sample_binding 17] \<and>
    credit_history(received_messages(machine_state bad))=[sample_binding 17]"
  unfolding bad_def
  by (simp add: sample.release_without_reversal_evidence_def sample_credit_before_ack_def sample_data_defs
      sample_auth_defs sample.protocol_definitions sample.published_receive_expansion sample.run_reservations.simps
      sample.reservation_step.simps record_observation_def commit_reservation_event_def
      record_credit_def empty_message_state_def Let_def)

lemma stale_generation_cannot_release_reversed_source:
  "snd(sample.release_to_source(sample_source_context ACTIVE)(sample_request 22)1(\<lambda>_.0)
    sample_return_ready)=Request_Rejected"
  by (simp add: sample_return_ready_def sample_data_defs sample_auth_defs sample.protocol_definitions
      sample.run_reservations.simps sample.reservation_step.simps record_observation_def
      commit_reservation_event_def Let_def)

end
