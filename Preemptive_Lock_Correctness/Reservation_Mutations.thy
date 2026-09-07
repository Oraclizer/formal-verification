(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Mutations
  imports Reservation_Examples Reservation_Message_Link
begin

section \<open>Source and Destination Guard Mutations\<close>

definition source_without_once :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat
  \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> reservation_machine \<Rightarrow>
  reservation_machine \<times> reservation_reply" where
  "source_without_once c r g versions m =
    (let s=machine_state m; b=request_binding r in
     if current_use_allowed(lock_authority c) r \<and> binding_is_registered s b \<and>
        owns_current_reservation c r g versions s \<and>
        phase_at s(binding_key b)\<in>{Some Source_Submitted,Some Source_Pending} \<and>
        binding_operation b=Destination_Credit \<and> 0<binding_amount b \<and>
        binding_amount b\<le>source_units s(source_account_of b) \<and>
        context_endpoint(lock_authority c)=fst(binding_key b) \<and>
        metadata_permission c r(fst(binding_key b))
     then record_observation r Source_Debited(commit_reservation_event(Source_Effect_Event b)m)
     else record_observation r Request_Rejected m)"

lemma source_repeat_control:
  "snd(execute_source_effect(sample_source_context ACTIVE)(sample_request 17)0(\<lambda>_.0)
      (sample_burnt 17))=Source_Already_Debited \<and>
    source_effects(machine_state(fst(execute_source_effect(sample_source_context ACTIVE)
      (sample_request 17)0(\<lambda>_.0)(sample_burnt 17))))=[sample_binding 17]"
  by (simp add: sample_data_defs sample.protocol_definitions sample.run_reservations.simps
      sample.reservation_step.simps record_observation_def commit_reservation_event_def Let_def)

lemma omitted_source_once_repeats_burn:
  "count_list(map binding_key(source_effects(machine_state(fst(source_without_once
    (sample_source_context ACTIVE)(sample_request 17)0(\<lambda>_.0)(sample_burnt 17))))))(0,17)=2"
  by (simp add: source_without_once_def sample_data_defs sample.protocol_definitions
      sample.run_reservations.simps sample.reservation_step.simps record_observation_def
      commit_reservation_event_def Let_def)

context source_attestation
begin

definition destination_without_once :: "execution_context \<Rightarrow> execution_request \<Rightarrow>
  reservation_machine \<Rightarrow> reservation_machine \<times> reservation_reply" where
  "destination_without_once c r m =
    (if credit_admissible c r \<and> request_certificate r\<in>set(issued_certificates(machine_state m))
     then record_observation r(Delivery_Response(New_Credit(request_binding r)))
       (commit_reservation_event(Credit_Event(request_binding r))m)
     else record_observation r(Delivery_Response Message_Rejected)m)"

end

lemma destination_repeat_control:
  "snd(sample.deliver_reserved_credit Validated_Route example_context(sample_request 17)sample_credited)=
    Delivery_Response(Duplicate_Credit(sample_binding 17))"
  by (simp add: sample_data_defs sample_auth_defs sample.protocol_definitions
      sample.published_receive_expansion sample.run_reservations.simps sample.reservation_step.simps
      record_observation_def commit_reservation_event_def record_credit_def credit_marker_def
      empty_message_state_def Let_def)

lemma omitted_destination_once_repeats_credit:
  "count_list(map binding_key(credit_history(received_messages(machine_state(fst
    (sample.destination_without_once example_context(sample_request 17)sample_credited))))))(0,17)=2"
  by (simp add: sample.destination_without_once_def sample_data_defs sample_auth_defs
      sample.protocol_definitions sample.published_receive_expansion sample.run_reservations.simps
      sample.reservation_step.simps record_observation_def commit_reservation_event_def
      record_credit_def empty_message_state_def Let_def)

text \<open>Each mutation removes the corresponding once check while retaining
  the other admission checks. The source and destination effects are counted
  as executions, including repeated effects with identical values.\<close>

end
