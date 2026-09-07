(* SPDX-License-Identifier: BSD-3-Clause *)
theory Finality_Scenarios
  imports Finality_Records Finality_Calls
begin

lemma empty_vector_represents_zero_versions:
  "vector_lookup []=(\<lambda>_.0)"
  by (rule ext) (simp add: vector_lookup_def)

definition finality_sample_initial where
  "finality_sample_initial=initial_finality_core sample_balances(sample_metadata ACTIVE)
    (\<lambda>endpoint. if endpoint=0 then sample_source_context ACTIVE else sample_context ACTIVE)"

definition finality_sample_prefix where
  "finality_sample_prefix event=[
    Invoke_Protocol 0 0 0(Reserve_Intent(sample_request event)[]10),
    Invoke_Protocol 0 1 0(Dispatch_Intent(sample_request event)0[]),
    Invoke_Protocol 0 2 0(Source_Intent(sample_request event)0[])]"

definition finality_sample_source where
  "finality_sample_source event=sample.run_finality(finality_sample_prefix event)finality_sample_initial"

lemma finality_source_prefix_is_the_actual_parent_prefix:
  "core_parent(finality_sample_source event)=sample_burnt event \<and>
    core_records(finality_sample_source event)=(\<lambda>_.None) \<and>
    core_published(finality_sample_source event)={} \<and>
    core_epoch(finality_sample_source event)=3 \<and>
    current_lock_view(finality_sample_source event)0=sample_source_context ACTIVE \<and>
    current_lock_view(finality_sample_source event)2=sample_context ACTIVE"
  by (simp add: finality_sample_source_def finality_sample_prefix_def finality_sample_initial_def
      initial_finality_core_def sample.finality_step_def sample.invoke_protocol_def
      sample_burnt_def sample_prefix_def sample_initial_def current_lock_view_def
      sample_source_context_def sample_context_def lift_protocol_result_def empty_vector_represents_zero_versions Let_def)

definition finality_sample_recorded where
  "finality_sample_recorded event=fst(sample.execute_finality_client
    (Client_Terminal(sample_certificate event))(finality_sample_source event))"

definition finality_sample_certified where
  "finality_sample_certified event=fst(sample.execute_finality_client
    (Client_Protocol 0 0(Certificate_Intent(sample_certificate event)))(finality_sample_recorded event))"

lemma actual_source_supports_terminal_record_creation:
  assumes "event\<in>{17,22}"
  shows "core_records(finality_sample_recorded event)(0,event)=Some
      \<lparr>terminal_binding=sample_binding event,
        terminal_kind=(if event=22 then Reversed_Decision else Confirmed_Decision),
        terminal_evidence=[sample_certificate event]\<rparr> \<and>
    core_parent(finality_sample_recorded event)=sample_burnt event"
proof -
  have alternatives: "event=17 \<or> event=22" using assms by auto
  show ?thesis using alternatives
    unfolding finality_sample_recorded_def sample.execute_finality_client_def
      sample.finality_step_def
    by (elim disjE)
      (simp_all add: sample.record_terminal_def source_origin_present_def
        finality_source_prefix_is_the_actual_parent_prefix sample_data_defs sample_auth_defs
        sample.protocol_definitions sample.run_reservations.simps sample.reservation_step.simps
        record_observation_def commit_reservation_event_def Let_def)
qed

lemma finality_recording_is_not_primary_publication:
  "core_published(finality_sample_recorded event)={}"
  by (simp add: finality_sample_recorded_def sample.execute_finality_client_def
      sample.finality_step_def sample.record_terminal_def Let_def
      finality_source_prefix_is_the_actual_parent_prefix split: option.splits if_splits)

lemma terminal_certificate_publishes_the_actual_parent_evidence:
  assumes "event\<in>{17,22}"
  shows "core_parent(finality_sample_certified event)=
    sample.publish_source_certificate(sample_certificate event)(sample_burnt event) \<and>
    core_records(finality_sample_certified event)=core_records(finality_sample_recorded event)"
  using actual_source_supports_terminal_record_creation[OF assms]
  by (auto simp: finality_sample_certified_def sample.execute_finality_client_def sample.finality_step_def
      sample.invoke_protocol_def exact_record_reference_def record_reference_def
      sample_certificate_def sample_statement_def sample_binding_def example_binding_def Let_def)

context source_attestation
begin

lemma terminal_recording_preserves_current_view:
  "current_lock_view(fst(record_terminal cert s))endpoint=current_lock_view s endpoint"
  by (auto simp: record_terminal_def current_lock_view_def Let_def split: option.splits if_splits)

lemma protocol_invocation_preserves_current_view:
  "current_lock_view(fst(invoke_protocol consumer epoch index intent s))endpoint=current_lock_view s endpoint"
  by (auto simp: invoke_protocol_def reject_protocol_intent_def current_lock_view_def Let_def
      split: option.splits if_splits)

end

lemma current_view_ignores_internal_epoch_update:
  "current_lock_view(s\<lparr>core_epoch:=epoch\<rparr>)endpoint=current_lock_view s endpoint"
  by (simp add: current_lock_view_def)

lemma finality_sample_current_contexts:
  "current_lock_view(finality_sample_certified event)0=sample_source_context ACTIVE"
  "current_lock_view(finality_sample_certified event)2=sample_context ACTIVE"
  by (simp_all add: finality_sample_certified_def finality_sample_recorded_def
      sample.execute_finality_client_def sample.finality_step_def current_view_ignores_internal_epoch_update
      sample.terminal_recording_preserves_current_view sample.protocol_invocation_preserves_current_view
      finality_source_prefix_is_the_actual_parent_prefix)

lemma normal_bypass_credit_uses_the_terminal_record:
  "snd(sample.execute_finality_client(Client_Protocol 2 0
    (Deliver_Intent Bypass_Route(sample_request 17)))(finality_sample_certified 17))=
    Protocol_Response(Delivery_Response(New_Credit(sample_binding 17)))"
  by (simp add: sample.execute_finality_client_def sample.invoke_protocol_def
      terminal_certificate_publishes_the_actual_parent_evidence actual_source_supports_terminal_record_creation
      exact_record_reference_def record_reference_def sample_request_def finality_sample_current_contexts
      sample_data_defs sample_auth_defs sample.protocol_definitions sample.published_receive_expansion
      sample.run_reservations.simps sample.reservation_step.simps lift_protocol_result_def
      record_observation_def commit_reservation_event_def Let_def empty_message_state_def)

lemma normal_reverse_returns_the_recorded_source:
  "snd(sample.execute_finality_client(Client_Protocol 0 0
    (Return_Intent(sample_request 22)0[]))(finality_sample_certified 22))=
    Protocol_Response Reservation_Released"
proof -
  have stored: "core_records(finality_sample_certified 22)(0,22)=Some
    \<lparr>terminal_binding=sample_binding 22,terminal_kind=Reversed_Decision,
      terminal_evidence=[sample_certificate 22]\<rparr>"
    using terminal_certificate_publishes_the_actual_parent_evidence[of 22]
      actual_source_supports_terminal_record_creation[of 22] by auto
  have guard: "exact_record_reference(finality_sample_certified 22)0
    (request_binding(sample_request 22))Reversed_Decision(request_certificate(sample_request 22))"
    by (simp add: exact_record_reference_def record_reference_def sample_request_def
        sample_binding_def example_binding_def stored)
  have reply: "snd(sample.release_to_source(sample_source_context ACTIVE)(sample_request 22)0(\<lambda>_.0)
    (sample.publish_source_certificate(sample_certificate 22)(sample_burnt 22)))=Reservation_Released"
    using actual_reversal_release_activates unfolding sample_return_ready_def by blast
  show ?thesis
    by (simp add: sample.execute_finality_client_def sample.invoke_protocol_def guard
      terminal_certificate_publishes_the_actual_parent_evidence finality_sample_current_contexts
      lift_protocol_result_def empty_vector_represents_zero_versions reply Let_def)
qed

context source_attestation
begin

definition invoke_without_terminal_reference where
  "invoke_without_terminal_reference endpoint epoch index intent s=
    (if epoch=core_epoch s
     then let result=intent_result(current_lock_view s endpoint)intent(core_parent s)
       in (s\<lparr>core_parent:=fst result\<rparr>,snd result)
     else (reject_protocol_intent intent s,Finality_Rejected))"

lemma wrong_record_index_is_rejected:
  assumes "record_reference s index(request_binding r)Confirmed_Decision=None"
  shows "snd(invoke_protocol endpoint epoch index(Deliver_Intent route r)s)=Finality_Rejected"
  using assms by (simp add: invoke_protocol_def exact_record_reference_def Let_def)

end

lemma removal_accepts_a_wrong_reference_at_a_generated_state:
  "snd(sample.invoke_protocol 2(core_epoch(finality_sample_certified 17))1
      (Deliver_Intent Bypass_Route(sample_request 17))(finality_sample_certified 17))=Finality_Rejected \<and>
    snd(sample.invoke_without_terminal_reference 2(core_epoch(finality_sample_certified 17))1
      (Deliver_Intent Bypass_Route(sample_request 17))(finality_sample_certified 17))=
      Protocol_Response(Delivery_Response(New_Credit(sample_binding 17)))"
proof -
  let ?s = "finality_sample_certified 17"
  let ?intent = "Deliver_Intent Bypass_Route(sample_request 17)"
  have stored: "core_records ?s(0,17)=Some
    \<lparr>terminal_binding=sample_binding 17,terminal_kind=Confirmed_Decision,
      terminal_evidence=[sample_certificate 17]\<rparr>"
    using terminal_certificate_publishes_the_actual_parent_evidence[of 17]
      actual_source_supports_terminal_record_creation[of 17] by auto
  have missing: "record_reference ?s 1(request_binding(sample_request 17))Confirmed_Decision=None"
    by (simp add: record_reference_def sample_request_def sample_binding_def example_binding_def stored)
  have rejected: "snd(sample.invoke_protocol 2(core_epoch ?s)1 ?intent ?s)=Finality_Rejected"
    by (rule sample.wrong_record_index_is_rejected[OF missing])
  have actual: "snd(sample.intent_result(current_lock_view ?s 2)?intent(core_parent ?s))=
    Protocol_Response(Delivery_Response(New_Credit(sample_binding 17)))"
    using normal_bypass_credit_uses_the_terminal_record
    by (auto simp: sample.execute_finality_client_def sample.invoke_protocol_def Let_def split: if_splits)
  have removed: "snd(sample.invoke_without_terminal_reference 2(core_epoch ?s)1 ?intent ?s)=
    Protocol_Response(Delivery_Response(New_Credit(sample_binding 17)))"
  proof -
    have "snd(sample.invoke_without_terminal_reference 2(core_epoch ?s)1 ?intent ?s)=
      snd(sample.intent_result(current_lock_view ?s 2)?intent(core_parent ?s))"
      by (simp add: sample.invoke_without_terminal_reference_def Let_def)
    also have "\<dots>=Protocol_Response(Delivery_Response(New_Credit(sample_binding 17)))"
      by (rule actual)
    finally show ?thesis .
  qed
  show ?thesis using rejected removed by blast
qed

lemma raw_source_and_destination_expose_a_partial_effect:
  "source_units(machine_state(core_parent(finality_sample_source 17)))(0,17)=5 \<and>
    destination_units(machine_state(core_parent(finality_sample_source 17)))(2,17,3)=0"
  by (simp add: finality_source_prefix_is_the_actual_parent_prefix sample_data_defs
      sample.protocol_definitions sample.run_reservations.simps sample.reservation_step.simps
      record_observation_def commit_reservation_event_def Let_def)

lemma no_exact_atomic_endpoint_observer_for_the_raw_intermediate_pair:
  "(5::nat,0::nat)\<noteq>(10,0) \<and> (5::nat,0::nat)\<noteq>(5,5)"
  by simp

text \<open>The source prefix is an execution of the child dispatcher from
  its actual initial state. The wrong-reference mutation starts from that
  generated source, terminal-record and certificate-publication trace. It
  removes only the terminal-reference guard and retains the current epoch
  check and the actual parent consumer. Its violation is missing reference
  provenance, not a new claim that the parent accounting conservation law
  depends on this guard. The raw pair is preserved as an explicit obstruction
  to exact two-endpoint atomic observations during an intermediate debit.\<close>

end
