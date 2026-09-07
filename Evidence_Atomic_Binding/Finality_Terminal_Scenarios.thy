(* SPDX-License-Identifier: BSD-3-Clause *)
theory Finality_Terminal_Scenarios
  imports Finality_Terminal_Progress Source_Coupling_Conservation
begin

section \<open>Actual Prefixes Before Receipt Issuance\<close>

definition terminal_confirm_cut :: source_coupling_state where
  "terminal_confirm_cut=linked.run_source_coupling(take 5 conservation_credit_word)conservation_initial"

definition terminal_reverse_cut :: source_coupling_state where
  "terminal_reverse_cut=linked.run_source_coupling(take 5 coupling_return_word)coupling_example_start"

lemma terminal_confirm_prefix:
  "take 5 conservation_credit_word=coupling_prepare 17@[
    Coupling_Source True True(Controlled_Boundary(Boundary_Apply(sample_binding 17))),
    Coupling_Client True(Client_Protocol 0 0(Source_Intent(sample_request 17)0[])),
    Coupling_Source True True(Controlled_Finalize(sample_binding 17))]"
  by (simp add: conservation_credit_word_def coupling_prepare_def)

lemma terminal_reverse_prefix:
  "take 5 coupling_return_word=coupling_prepare 22@[
    Coupling_Source True False(Controlled_Boundary(Boundary_Apply(sample_binding 22))),
    Coupling_Client True(Client_Protocol 0 0(Source_Intent(sample_request 22)0[])),
    Coupling_Source True True(Controlled_Reverse(sample_binding 22))]"
  by (simp add: coupling_return_word_def coupling_prepare_def)

lemmas terminal_cut_execution =
  linked.run_source_coupling.simps linked.source_coupling_step.simps
  linked.coupling_client_step_def linked.coupling_client_result.simps
  linked.execute_finality_client_def linked.finality_step_def linked.core_result.simps
  linked.invoke_protocol_def linked.intent_result.simps
  coupling_source_result_def coupling_monetary_def coupling_effect_witness_def
  boundary_evidence_exact boundary_has_effect_def
  controlled_boundary_def controlled_finalize_def controlled_reverse_def
  controlled_record_finalized_def controlled_record_reversed_def controlled_source_fact_def
  initial_controlled_source_def initial_source_boundary_def boundary_apply_def
  boundary_record_effect_def boundary_valid_binding_def
  initial_source_coupling_def initial_finality_core_def current_lock_view_def
  acquire_reservation_def dispatch_source_def execute_source_effect_def
  lift_protocol_result_def record_observation_def commit_reservation_event_def vector_lookup_def

lemma terminal_confirm_cut_fields:
  "core_parent(coupled_core terminal_confirm_cut)=sample_burnt 17"
  "current_lock_view(coupled_core terminal_confirm_cut)2=sample_context ACTIVE"
  "core_records(coupled_core terminal_confirm_cut)=(\<lambda>_.None)"
  "coupled_receipts terminal_confirm_cut=[]"
  "controlled_source_fact(coupled_source terminal_confirm_cut)(0,17)=Some(sample_statement 17)"
  unfolding terminal_confirm_cut_def terminal_confirm_prefix
  by (simp_all add: conservation_initial_def conservation_contexts_def coupling_prepare_def
    terminal_cut_execution sample_data_defs sample.run_reservations.simps sample.reservation_step.simps Let_def)

lemma terminal_reverse_cut_fields:
  "core_parent(coupled_core terminal_reverse_cut)=sample_burnt 22"
  "current_lock_view(coupled_core terminal_reverse_cut)0=sample_source_context ACTIVE"
  "core_records(coupled_core terminal_reverse_cut)=(\<lambda>_.None)"
  "coupled_receipts terminal_reverse_cut=[]"
  "controlled_source_fact(coupled_source terminal_reverse_cut)(0,22)=Some(sample_statement 22)"
  unfolding terminal_reverse_cut_def terminal_reverse_prefix
  by (simp_all add: coupling_example_start_def coupling_prepare_def terminal_cut_execution
    sample_data_defs sample.run_reservations.simps sample.reservation_step.simps Let_def)

lemma terminal_confirm_parent_fields:
  "source_effects(machine_state(sample_burnt 17))=[sample_binding 17]"
  "received_messages(machine_state(sample_burnt 17))=empty_message_state"
  by (simp_all add: sample_data_defs sample.run_reservations.simps sample.reservation_step.simps
    acquire_reservation_def dispatch_source_def execute_source_effect_def
    record_observation_def commit_reservation_event_def Let_def)

lemma terminal_reverse_parent_fields:
  "source_effects(machine_state(sample_burnt 22))=[sample_binding 22]"
  "owns_recorded_reservation(sample_source_context ACTIVE)linked_return_request 0
    (vector_lookup [])(machine_state(sample_burnt 22))"
  "phase_at(machine_state(sample_burnt 22))(0,22)=Some Source_Pending"
  by (simp_all add: linked_return_request_def linked_certificate_def sample_data_defs
    sample.run_reservations.simps sample.reservation_step.simps vector_lookup_def
    acquire_reservation_def dispatch_source_def execute_source_effect_def
    record_observation_def commit_reservation_event_def Let_def)

lemma terminal_confirm_cut_has_the_generated_contract:
  "linked.source_coupling_invariant sample_balances terminal_confirm_cut"
  unfolding terminal_confirm_cut_def conservation_initial_def
  by (rule linked.all_finite_joint_executions_have_source_provenance)

lemma terminal_reverse_cut_has_the_generated_contract:
  "linked.source_coupling_invariant sample_balances terminal_reverse_cut"
  unfolding terminal_reverse_cut_def coupling_example_start_def
  by (rule linked.all_finite_joint_executions_have_source_provenance)

lemma terminal_confirm_cut_has_all_evidence_inputs:
  "linked.terminal_evidence_inputs(linked_certificate 17)terminal_confirm_cut"
proof -
  have checked: "linked.certificate_ok(linked_certificate 17)"
    using linked_certificates_pass_the_parent_checker[of 17] by simp
  show ?thesis using checked
    unfolding linked.terminal_evidence_inputs_def
    by (simp add: terminal_confirm_cut_fields terminal_confirm_parent_fields
      linked_certificate_def source_receipt_slot_available_def sample_statement_def
      sample_binding_def example_binding_def)
qed

lemma terminal_reverse_cut_has_all_evidence_inputs:
  "linked.terminal_evidence_inputs(linked_certificate 22)terminal_reverse_cut"
proof -
  have checked: "linked.certificate_ok(linked_certificate 22)"
    using linked_certificates_pass_the_parent_checker[of 22] by simp
  show ?thesis using checked
    unfolding linked.terminal_evidence_inputs_def
    by (simp add: terminal_reverse_cut_fields terminal_reverse_parent_fields
      linked_certificate_def source_receipt_slot_available_def sample_statement_def
      sample_binding_def example_binding_def)
qed

lemma terminal_confirm_cut_has_actual_admission:
  "linked.credit_admissible(lock_authority(current_lock_view(coupled_core terminal_confirm_cut)2))
    conservation_credit_request"
proof -
  have checked: "linked.certificate_ok(linked_certificate 17)"
    using linked_certificates_pass_the_parent_checker[of 17] by simp
  show ?thesis using checked
    unfolding linked.credit_admissible_def linked.authenticated_request_def
    by (simp add: terminal_confirm_cut_fields conservation_credit_request_def sample_request_def
      sample_context_def linked_certificate_def sample_statement_def sample_binding_def
      example_binding_def example_context_def current_use_allowed_def)
qed

lemma terminal_confirm_cut_has_no_consumed_credit:
  "credit_marker(request_binding conservation_credit_request)\<notin>
    consumed_at(received_messages(machine_state(core_parent(coupled_core terminal_confirm_cut))))"
  by (simp add: terminal_confirm_cut_fields terminal_confirm_parent_fields empty_message_state_def)

section \<open>The General Conditional Programs Are Actually Activated\<close>

definition terminal_confirm_ready :: source_coupling_state where
  "terminal_confirm_ready=linked.run_source_coupling
    (terminal_evidence_actions 2(linked_certificate 17))terminal_confirm_cut"

definition terminal_confirm_effect :: source_coupling_state where
  "terminal_confirm_effect=linked.run_source_coupling
    (terminal_effect_actions 2(linked_certificate 17)(Deliver_Intent Bypass_Route conservation_credit_request))
    terminal_confirm_cut"

definition terminal_confirm_finished :: source_coupling_state where
  "terminal_confirm_finished=linked.run_source_coupling
    (terminal_finish_actions 2(linked_certificate 17)(Deliver_Intent Bypass_Route conservation_credit_request))
    terminal_confirm_cut"

theorem actual_confirm_prefix_activates_the_terminal_program:
  "snd(linked.source_coupling_step(Coupling_Client True(Client_Protocol 2 0
      (Deliver_Intent Bypass_Route conservation_credit_request)))terminal_confirm_ready)=
      Coupling_Client_Reply(Protocol_Response(Delivery_Response(New_Credit(sample_binding 17)))) \<and>
    snd(linked.source_coupling_step(Coupling_Client True(Client_Publication(0,17)))terminal_confirm_effect)=
      Coupling_Client_Reply Primary_Published \<and>
    (0,17)\<in>core_published(coupled_core terminal_confirm_finished) \<and>
    sample_binding 17\<in>set(credit_history(received_messages
      (machine_state(core_parent(coupled_core terminal_confirm_finished))))) \<and>
    coupled_source terminal_confirm_finished=coupled_source terminal_confirm_cut"
proof -
  have bound: "statement_binding(certificate_statement(linked_certificate 17))=
      request_binding conservation_credit_request"
    and certificate: "request_certificate conservation_credit_request=linked_certificate 17"
    and status: "statement_status(certificate_statement(linked_certificate 17))=Finalized"
    by (simp_all add: conservation_credit_request_def sample_request_def linked_certificate_def sample_statement_def)
  note activated = linked.confirmed_source_has_a_finite_primary_program
    [OF terminal_confirm_cut_has_all_evidence_inputs terminal_confirm_cut_has_the_generated_contract
      bound certificate status terminal_confirm_cut_has_actual_admission terminal_confirm_cut_has_no_consumed_credit,
      where route=Bypass_Route]
  show ?thesis using activated
    by (auto simp: terminal_confirm_ready_def terminal_confirm_effect_def terminal_confirm_finished_def
      conservation_credit_request_def sample_request_def sample_binding_def example_binding_def)
qed

definition terminal_reverse_ready :: source_coupling_state where
  "terminal_reverse_ready=linked.run_source_coupling
    (terminal_evidence_actions 0(linked_certificate 22))terminal_reverse_cut"

definition terminal_reverse_effect :: source_coupling_state where
  "terminal_reverse_effect=linked.run_source_coupling
    (terminal_effect_actions 0(linked_certificate 22)(Return_Intent linked_return_request 0 []))terminal_reverse_cut"

definition terminal_reverse_finished :: source_coupling_state where
  "terminal_reverse_finished=linked.run_source_coupling
    (terminal_finish_actions 0(linked_certificate 22)(Return_Intent linked_return_request 0 []))terminal_reverse_cut"

theorem actual_reverse_prefix_activates_the_terminal_program:
  "snd(linked.source_coupling_step(Coupling_Client True(Client_Protocol 0 0
      (Return_Intent linked_return_request 0 [])))terminal_reverse_ready)=
      Coupling_Client_Reply(Protocol_Response Reservation_Released) \<and>
    snd(linked.source_coupling_step(Coupling_Client True(Client_Publication(0,22)))terminal_reverse_effect)=
      Coupling_Client_Reply Primary_Published \<and>
    (0,22)\<in>core_published(coupled_core terminal_reverse_finished) \<and>
    phase_at(machine_state(core_parent(coupled_core terminal_reverse_finished)))(0,22)=Some Source_Returned \<and>
    coupled_source terminal_reverse_finished=coupled_source terminal_reverse_cut"
proof -
  have bound: "statement_binding(certificate_statement(linked_certificate 22))=request_binding linked_return_request"
    and certificate: "request_certificate linked_return_request=linked_certificate 22"
    and status: "statement_status(certificate_statement(linked_certificate 22))=Reversed"
    by (simp_all add: linked_return_request_def sample_request_def linked_certificate_def sample_statement_def)
  have epoch: "certificate_epoch(linked_certificate 22)=
    context_relay_epoch(lock_authority(current_lock_view(coupled_core terminal_reverse_cut)0))"
    by (simp add: terminal_reverse_cut_fields linked_certificate_def sample_source_context_def
      sample_context_def example_context_def)
  have owner: "owns_recorded_reservation(current_lock_view(coupled_core terminal_reverse_cut)0)
    linked_return_request 0(vector_lookup [])(machine_state(core_parent(coupled_core terminal_reverse_cut)))"
    by (simp add: terminal_reverse_cut_fields terminal_reverse_parent_fields)
  have key: "binding_key(request_binding linked_return_request)=(0,22)"
    using linked_return_request_projection by blast
  have pending: "phase_at(machine_state(core_parent(coupled_core terminal_reverse_cut)))
      (binding_key(request_binding linked_return_request))=Some Source_Pending"
    by (simp add: terminal_reverse_cut_fields terminal_reverse_parent_fields key)
  note activated = linked.reversed_source_has_a_finite_primary_program
    [OF terminal_reverse_cut_has_all_evidence_inputs terminal_reverse_cut_has_the_generated_contract
      bound certificate status epoch owner pending]
  show ?thesis using activated
    by (auto simp: terminal_reverse_ready_def terminal_reverse_effect_def terminal_reverse_finished_def
      linked_return_request_def sample_request_def sample_binding_def example_binding_def)
qed

text \<open>Both initial cuts are prefixes of previously defined joint executions,
  immediately after the actual controlled finalization or reversal and before
  receipt issuance. The evidence conjunction and the current parent guards are
  proved for those same cuts, then supplied to the general terminal theorems.
  The confirmation program publishes evidence at destination endpoint two;
  certificate publication uses its exact record reference and does not replace
  the destination's actual credit-admission check. These examples add no source
  producer or agreement assumption.\<close>

end
