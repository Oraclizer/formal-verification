(* SPDX-License-Identifier: BSD-3-Clause *)
theory Finality_Terminal_Progress
  imports Finality_Progress Source_Coupling
begin

section \<open>Delivered Terminal Programs with Explicit Current Inputs\<close>

definition terminal_evidence_actions :: "nat \<Rightarrow> source_certificate \<Rightarrow>
  source_coupling_action list" where
  "terminal_evidence_actions endpoint cert=[Coupling_Issue True cert,
    Coupling_Client True (Client_Terminal cert),
    Coupling_Client True (Client_Protocol endpoint 0 (Certificate_Intent cert))]"

definition terminal_effect_actions :: "nat \<Rightarrow> source_certificate \<Rightarrow>
  protocol_intent \<Rightarrow> source_coupling_action list" where
  "terminal_effect_actions endpoint cert intent=terminal_evidence_actions endpoint cert@
    [Coupling_Client True (Client_Protocol endpoint 0 intent)]"

definition terminal_finish_actions :: "nat \<Rightarrow> source_certificate \<Rightarrow>
  protocol_intent \<Rightarrow> source_coupling_action list" where
  "terminal_finish_actions endpoint cert intent=terminal_effect_actions endpoint cert intent@
    [Coupling_Client True (Client_Publication
      (binding_key (statement_binding (certificate_statement cert))))]"

definition progress_terminal_record :: "source_certificate \<Rightarrow> terminal_kind \<Rightarrow>
  terminal_record" where
  "progress_terminal_record cert kind=\<lparr>terminal_binding=statement_binding(certificate_statement cert),
    terminal_kind=kind,terminal_evidence=[cert]\<rparr>"

definition progress_prepared_core :: "source_certificate \<Rightarrow> terminal_kind \<Rightarrow>
  finality_core \<Rightarrow> finality_core" where
  "progress_prepared_core cert kind core=core\<lparr>
    core_parent:=commit_reservation_event(Certificate_Event cert)(core_parent core),
    core_records:=(core_records core)(binding_key(statement_binding(certificate_statement cert)):=
      Some(progress_terminal_record cert kind)),core_epoch:=Suc(Suc(core_epoch core))\<rparr>"

context source_attestation
begin

definition terminal_evidence_inputs :: "source_certificate \<Rightarrow> source_coupling_state \<Rightarrow>
  bool" where
  "terminal_evidence_inputs cert s \<longleftrightarrow>
    certificate_ok cert \<and>
    controlled_source_fact(coupled_source s)(binding_key(statement_binding(certificate_statement cert)))=
      Some(certificate_statement cert) \<and>
    source_receipt_slot_available cert(coupled_receipts s) \<and>
    binding_operation(statement_binding(certificate_statement cert))=Destination_Credit \<and>
    0<binding_amount(statement_binding(certificate_statement cert)) \<and>
    statement_binding(certificate_statement cert)\<in>
      set(source_effects(machine_state(core_parent(coupled_core s)))) \<and>
    core_records(coupled_core s)(binding_key(statement_binding(certificate_statement cert)))=None"

lemma progress_source_run_append:
  "run_source_coupling (first@second) s=run_source_coupling second(run_source_coupling first s)"
  by (induction first arbitrary:s) simp_all

lemma current_fact_issues_a_live_receipt:
  assumes "terminal_evidence_inputs cert s"
  shows "cert\<in>set(issue_source_receipt(coupled_source s)cert(coupled_receipts s))"
  using assms by (auto simp: terminal_evidence_inputs_def issue_source_receipt_def)

lemma terminal_evidence_program_records_and_publishes:
  assumes inputs: "terminal_evidence_inputs cert s"
    and kind: "kind_from_source(statement_status(certificate_statement cert))=Some kind"
  shows "run_source_coupling(terminal_evidence_actions endpoint cert)s=
    s\<lparr>coupled_receipts:=issue_source_receipt(coupled_source s)cert(coupled_receipts s),
      coupled_core:=progress_prepared_core cert kind(coupled_core s)\<rparr>"
proof -
  have issued: "cert\<in>set(issue_source_receipt(coupled_source s)cert(coupled_receipts s))"
    by (rule current_fact_issues_a_live_receipt[OF inputs])
  have terminal: "statement_status(certificate_statement cert)\<noteq>Observed"
    using kind by (cases "statement_status(certificate_statement cert)") auto
  have checked: "certificate_ok cert"
    and source: "controlled_source_fact(coupled_source s)(binding_key(statement_binding(certificate_statement cert)))=
      Some(certificate_statement cert)"
    and monetary: "binding_operation(statement_binding(certificate_statement cert))=Destination_Credit"
    and positive: "0<binding_amount(statement_binding(certificate_statement cert))"
    and debit: "statement_binding(certificate_statement cert)\<in>
      set(source_effects(machine_state(core_parent(coupled_core s))))"
    and empty: "core_records(coupled_core s)(binding_key(statement_binding(certificate_statement cert)))=None"
    using inputs unfolding terminal_evidence_inputs_def by blast+
  show ?thesis using checked source monetary positive debit empty kind issued terminal
    by (simp add: terminal_evidence_actions_def
      coupling_issue_result_def coupling_client_step_def coupling_live_receipt_def coupling_monetary_def
      execute_finality_client_def finality_step_def record_terminal_def source_origin_present_def
      invoke_protocol_def exact_record_reference_def record_reference_def publish_source_certificate_def
      progress_prepared_core_def progress_terminal_record_def Let_def)
qed

lemma prepared_core_current_view:
  "current_lock_view(progress_prepared_core cert kind core)endpoint=current_lock_view core endpoint"
  by (simp add: progress_prepared_core_def current_lock_view_def)

lemma prepared_core_has_exact_reference:
  "exact_record_reference(progress_prepared_core cert kind core)0
    (statement_binding(certificate_statement cert))kind cert"
  by (simp add: progress_prepared_core_def progress_terminal_record_def
    exact_record_reference_def record_reference_def)

lemma prepared_confirmation_executes_credit:
  assumes bound: "statement_binding(certificate_statement cert)=request_binding r"
    and certificate: "request_certificate r=cert"
    and admitted: "credit_admissible(lock_authority(current_lock_view core endpoint))r"
    and fresh: "credit_marker(request_binding r)\<notin>consumed_at(received_messages(machine_state(core_parent core)))"
  defines "ready \<equiv> progress_prepared_core cert Confirmed_Decision core"
  shows "snd(execute_finality_client(Client_Protocol endpoint 0(Deliver_Intent route r))ready)=
      Protocol_Response(Delivery_Response(New_Credit(request_binding r))) \<and>
    core_parent(fst(execute_finality_client(Client_Protocol endpoint 0(Deliver_Intent route r))ready))=
      fst(record_observation r(Delivery_Response(New_Credit(request_binding r)))
        (commit_reservation_event(Credit_Event(request_binding r))(core_parent ready)))"
proof -
  have reference: "exact_record_reference ready 0(request_binding r)Confirmed_Decision(request_certificate r)"
    by (simp add: ready_def certificate bound[symmetric] prepared_core_has_exact_reference)
  have view: "current_lock_view ready endpoint=current_lock_view core endpoint"
    by (simp add: ready_def prepared_core_current_view)
  have issued: "request_certificate r\<in>set(issued_certificates(machine_state(core_parent ready)))"
    by (simp add: ready_def progress_prepared_core_def commit_reservation_event_def certificate)
  have unused: "credit_marker(request_binding r)\<notin>consumed_at(received_messages(machine_state(core_parent ready)))"
    using fresh by (simp add: ready_def progress_prepared_core_def commit_reservation_event_def)
  have parent: "deliver_reserved_credit route(lock_authority(current_lock_view core endpoint))r(core_parent ready)=
    record_observation r(Delivery_Response(New_Credit(request_binding r)))
      (commit_reservation_event(Credit_Event(request_binding r))(core_parent ready))"
    using admitted issued unused by (simp add: deliver_reserved_credit_def published_receive_expansion)
  show ?thesis by (simp add: execute_finality_client_def finality_step_def invoke_protocol_def
    reference view lift_protocol_result_def parent record_observation_def Let_def)
qed

lemma prepared_reversal_executes_return:
  assumes bound: "statement_binding(certificate_statement cert)=request_binding r"
    and certificate: "request_certificate r=cert" and checked: "certificate_ok cert"
    and status: "statement_status(certificate_statement cert)=Reversed"
    and epoch: "certificate_epoch cert=context_relay_epoch(lock_authority(current_lock_view core endpoint))"
    and owner: "owns_recorded_reservation(current_lock_view core endpoint)r generation
      (vector_lookup versions)(machine_state(core_parent core))"
    and pending: "phase_at(machine_state(core_parent core))(binding_key(request_binding r))=Some Source_Pending"
  defines "ready \<equiv> progress_prepared_core cert Reversed_Decision core"
  shows "snd(execute_finality_client(Client_Protocol endpoint 0(Return_Intent r generation versions))ready)=
      Protocol_Response Reservation_Released \<and>
    core_parent(fst(execute_finality_client(Client_Protocol endpoint 0(Return_Intent r generation versions))ready))=
      fst(release_to_source(current_lock_view core endpoint)r generation(vector_lookup versions)(core_parent ready))"
proof -
  have reference: "exact_record_reference ready 0(request_binding r)Reversed_Decision(request_certificate r)"
    by (simp add: ready_def certificate bound[symmetric] prepared_core_has_exact_reference)
  have guards: "owns_recorded_reservation(current_lock_view core endpoint)r generation
      (vector_lookup versions)(machine_state(core_parent ready)) \<and>
    phase_at(machine_state(core_parent ready))(binding_key(request_binding r))=Some Source_Pending \<and>
    reversed_source_evidence(lock_authority(current_lock_view core endpoint))r(machine_state(core_parent ready))"
    using owner pending bound certificate checked status epoch
    by (simp add: ready_def progress_prepared_core_def source_link_certificate_event_frames
      reversed_source_evidence_def commit_reservation_event_def source_link_issued_certificate_update_frames)
  have released: "snd(release_to_source(current_lock_view core endpoint)r generation
    (vector_lookup versions)(core_parent ready))=Reservation_Released"
    using guards evidence_release_exact_guard by blast
  have view: "current_lock_view ready endpoint=current_lock_view core endpoint"
    by (simp add: ready_def prepared_core_current_view)
  show ?thesis by (simp add: execute_finality_client_def finality_step_def invoke_protocol_def
    reference view lift_protocol_result_def released Let_def)
qed

lemma terminal_protocol_keeps_core_metadata:
  "core_records(fst(execute_finality_client(Client_Protocol endpoint index intent)core))=core_records core"
  "core_regulatory(fst(execute_finality_client(Client_Protocol endpoint index intent)core))=core_regulatory core"
  "core_contexts(fst(execute_finality_client(Client_Protocol endpoint index intent)core))=core_contexts core"
  by (simp_all add: execute_finality_client_def finality_step_def invoke_protocol_def
    reject_protocol_intent_def Let_def split: option.splits)

lemma actual_return_preserves_registration:
  assumes owner: "owns_recorded_reservation c r generation versions(machine_state parent)"
  shows "binding_is_registered(machine_state(fst(release_to_source c r generation versions parent)))(request_binding r)"
  using owner
  by (auto simp: owns_recorded_reservation_def binding_is_registered_def release_to_source_def
    record_observation_def commit_reservation_event_def finish_reservation_def set_phase_def)

lemma terminal_publication_completes_a_recorded_effect:
  assumes recorded: "core_records core(binding_key(terminal_binding entry))=Some entry"
    and effect: "terminal_effect_completed core entry"
  shows "snd(execute_finality_client(Client_Publication(binding_key(terminal_binding entry)))core)=Primary_Published \<and>
    binding_key(terminal_binding entry)\<in>core_published
      (fst(execute_finality_client(Client_Publication(binding_key(terminal_binding entry)))core))"
  using recorded effect
  by (simp add: execute_finality_client_def finality_step_def publish_primary_def Let_def)

lemma terminal_publication_preserves_parent_and_records:
  "core_parent(fst(execute_finality_client(Client_Publication key)core))=core_parent core"
  "core_records(fst(execute_finality_client(Client_Publication key)core))=core_records core"
  by (simp_all add: execute_finality_client_def finality_step_def publish_primary_def Let_def
    split: option.splits)

lemma terminal_nonclosing_source_step:
  assumes guard: "coupling_guard True s command"
    and closes: "coupling_closed_binding command(snd(execute_finality_client command(coupled_core s)))=None"
  shows "source_coupling_step(Coupling_Client True command)s=
    (s\<lparr>coupled_core:=fst(execute_finality_client command(coupled_core s))\<rparr>,
      Coupling_Client_Reply(snd(execute_finality_client command(coupled_core s))))"
  using guard closes guarded_client_is_the_actual_child[OF guard]
  by (simp add: coupling_client_step_def Let_def)

lemma terminal_program_composition:
  assumes prepared: "ready=run_source_coupling(terminal_evidence_actions endpoint cert)s"
    and guard: "coupling_guard True ready(Client_Protocol endpoint 0 intent)"
    and closes: "coupling_closed_binding(Client_Protocol endpoint 0 intent)
      (snd(execute_finality_client(Client_Protocol endpoint 0 intent)(coupled_core ready)))=None"
  defines "effect \<equiv> fst(execute_finality_client(Client_Protocol endpoint 0 intent)(coupled_core ready))"
  shows "run_source_coupling(terminal_effect_actions endpoint cert intent)s=ready\<lparr>coupled_core:=effect\<rparr>"
    "run_source_coupling(terminal_finish_actions endpoint cert intent)s=
      ready\<lparr>coupled_core:=fst(execute_finality_client(Client_Publication
        (binding_key(statement_binding(certificate_statement cert))))effect)\<rparr>"
proof -
  have step: "source_coupling_step(Coupling_Client True(Client_Protocol endpoint 0 intent))ready=
    (ready\<lparr>coupled_core:=effect\<rparr>,Coupling_Client_Reply
      (snd(execute_finality_client(Client_Protocol endpoint 0 intent)(coupled_core ready))))"
    using terminal_nonclosing_source_step[OF guard closes] by (simp only: effect_def)
  show first: "run_source_coupling(terminal_effect_actions endpoint cert intent)s=ready\<lparr>coupled_core:=effect\<rparr>"
    by (simp only: terminal_effect_actions_def progress_source_run_append prepared[symmetric]
      run_source_coupling.simps step fst_conv)
  show "run_source_coupling(terminal_finish_actions endpoint cert intent)s=
    ready\<lparr>coupled_core:=fst(execute_finality_client(Client_Publication
      (binding_key(statement_binding(certificate_statement cert))))effect)\<rparr>"
    by (simp add: terminal_finish_actions_def progress_source_run_append first coupling_client_step_def Let_def)
qed

theorem confirmed_source_has_a_finite_primary_program:
  fixes s :: source_coupling_state and r :: execution_request
    and cert :: source_certificate and endpoint :: nat and route :: message_route
  assumes inputs: "terminal_evidence_inputs cert s"
    and healthy: "source_coupling_invariant balances s"
    and bound: "statement_binding(certificate_statement cert)=request_binding r"
    and certificate: "request_certificate r=cert"
    and status: "statement_status(certificate_statement cert)=Finalized"
    and admitted: "credit_admissible(lock_authority(current_lock_view(coupled_core s)endpoint))r"
    and fresh: "credit_marker(request_binding r)\<notin>
      consumed_at(received_messages(machine_state(core_parent(coupled_core s))))"
  defines "ready \<equiv> run_source_coupling(terminal_evidence_actions endpoint cert)s"
    and "effect \<equiv> run_source_coupling(terminal_effect_actions endpoint cert(Deliver_Intent route r))s"
    and "finished \<equiv> run_source_coupling(terminal_finish_actions endpoint cert(Deliver_Intent route r))s"
  shows "snd(source_coupling_step(Coupling_Client True(Client_Protocol endpoint 0(Deliver_Intent route r)))ready)=
      Coupling_Client_Reply(Protocol_Response(Delivery_Response(New_Credit(request_binding r)))) \<and>
    snd(source_coupling_step(Coupling_Client True(Client_Publication(binding_key(request_binding r))))effect)=
      Coupling_Client_Reply Primary_Published \<and>
    binding_key(request_binding r)\<in>core_published(coupled_core finished) \<and>
    request_binding r\<in>set(credit_history(received_messages(machine_state(core_parent(coupled_core finished))))) \<and>
    core_records(coupled_core finished)(binding_key(request_binding r))=
      Some(progress_terminal_record cert Confirmed_Decision) \<and>
    coupled_source finished=coupled_source s \<and> source_coupling_invariant balances finished \<and>
    call_completions(finality_calls.run_calls
      (complete_call_program call_id(Client_Publication(binding_key(request_binding r))))
      (initial_call_machine(coupled_core effect)))call_id=Some Primary_Published"
proof -
  have ready_shape: "ready=s\<lparr>coupled_receipts:=issue_source_receipt(coupled_source s)cert(coupled_receipts s),
      coupled_core:=progress_prepared_core cert Confirmed_Decision(coupled_core s)\<rparr>"
    unfolding ready_def by (rule terminal_evidence_program_records_and_publishes[OF inputs]) (simp add: status)
  have ready_core: "coupled_core ready=progress_prepared_core cert Confirmed_Decision(coupled_core s)"
    by (simp add: ready_shape)
  have live: "coupling_live_receipt ready cert"
    using inputs current_fact_issues_a_live_receipt[OF inputs]
    by (simp add: ready_shape coupling_live_receipt_def terminal_evidence_inputs_def)
  have guard: "coupling_guard True ready(Client_Protocol endpoint 0(Deliver_Intent route r))"
    using live certificate by simp
  let ?core = "fst(execute_finality_client(Client_Protocol endpoint 0(Deliver_Intent route r))(coupled_core ready))"
  have credit: "snd(execute_finality_client(Client_Protocol endpoint 0(Deliver_Intent route r))(coupled_core ready))=
      Protocol_Response(Delivery_Response(New_Credit(request_binding r))) \<and>
    core_parent ?core=fst(record_observation r(Delivery_Response(New_Credit(request_binding r)))
      (commit_reservation_event(Credit_Event(request_binding r))(core_parent(coupled_core ready))))"
    using prepared_confirmation_executes_credit[OF bound certificate admitted fresh, where route=route]
    by (simp only: ready_core)
  have preparation: "ready=run_source_coupling(terminal_evidence_actions endpoint cert)s"
    by (simp only: ready_def)
  have no_close: "coupling_closed_binding(Client_Protocol endpoint 0(Deliver_Intent route r))
    (snd(execute_finality_client(Client_Protocol endpoint 0(Deliver_Intent route r))(coupled_core ready)))=None"
    by simp
  have composition: "effect=ready\<lparr>coupled_core:=?core\<rparr>"
    "finished=ready\<lparr>coupled_core:=fst(execute_finality_client(Client_Publication(binding_key(request_binding r)))?core)\<rparr>"
    using terminal_program_composition[OF preparation guard no_close] bound
    by (simp_all add: effect_def finished_def)
  have stored_record: "core_records ?core(binding_key(request_binding r))=Some(progress_terminal_record cert Confirmed_Decision)"
    by (simp add: terminal_protocol_keeps_core_metadata ready_shape progress_prepared_core_def bound)
  have completed: "terminal_effect_completed ?core(progress_terminal_record cert Confirmed_Decision)"
    using credit bound inputs
    by (simp add: terminal_effect_completed_def progress_terminal_record_def terminal_evidence_inputs_def
      record_observation_def commit_reservation_event_def record_credit_def Let_def)
  have record_key: "core_records ?core(binding_key(terminal_binding(progress_terminal_record cert Confirmed_Decision)))=
    Some(progress_terminal_record cert Confirmed_Decision)"
    using stored_record by (simp add: progress_terminal_record_def bound)
  have primary: "snd(execute_finality_client(Client_Publication(binding_key(request_binding r)))?core)=Primary_Published \<and>
      binding_key(request_binding r)\<in>core_published(fst(execute_finality_client(Client_Publication(binding_key(request_binding r)))?core))"
    using terminal_publication_completes_a_recorded_effect[OF record_key completed]
    by (simp add: progress_terminal_record_def bound)
  have invariant: "source_coupling_invariant balances finished"
    unfolding finished_def by (rule source_coupling_run_preserves_invariant[OF healthy])
  have call: "call_completions(finality_calls.run_calls
      (complete_call_program call_id(Client_Publication(binding_key(request_binding r))))
      (initial_call_machine ?core))call_id=Some Primary_Published"
    using finality_calls.a_fresh_initial_call_has_a_four_action_completion
      [of call_id "Client_Publication(binding_key(request_binding r))" ?core] primary by simp
  have member: "request_binding r\<in>set(credit_history(received_messages(machine_state(core_parent ?core))))"
    using credit by (simp add: record_observation_def commit_reservation_event_def record_credit_def)
  have source_frame: "coupled_source ready=coupled_source s" by (simp add: ready_shape)
  show ?thesis using credit primary stored_record invariant guard call member source_frame
    by (simp add: composition coupling_client_step_def guarded_client_is_the_actual_child[OF guard]
      terminal_publication_preserves_parent_and_records Let_def)
qed

theorem reversed_source_has_a_finite_primary_program:
  fixes s :: source_coupling_state and r :: execution_request
    and cert :: source_certificate and endpoint generation :: nat and versions :: version_vector
  assumes inputs: "terminal_evidence_inputs cert s"
    and healthy: "source_coupling_invariant balances s"
    and bound: "statement_binding(certificate_statement cert)=request_binding r"
    and certificate: "request_certificate r=cert"
    and status: "statement_status(certificate_statement cert)=Reversed"
    and epoch: "certificate_epoch cert=context_relay_epoch(lock_authority(current_lock_view(coupled_core s)endpoint))"
    and owner: "owns_recorded_reservation(current_lock_view(coupled_core s)endpoint)r generation
      (vector_lookup versions)(machine_state(core_parent(coupled_core s)))"
    and pending: "phase_at(machine_state(core_parent(coupled_core s)))(binding_key(request_binding r))=Some Source_Pending"
  defines "ready \<equiv> run_source_coupling(terminal_evidence_actions endpoint cert)s"
    and "effect \<equiv> run_source_coupling(terminal_effect_actions endpoint cert(Return_Intent r generation versions))s"
    and "finished \<equiv> run_source_coupling(terminal_finish_actions endpoint cert(Return_Intent r generation versions))s"
  shows "snd(source_coupling_step(Coupling_Client True(Client_Protocol endpoint 0(Return_Intent r generation versions)))ready)=
      Coupling_Client_Reply(Protocol_Response Reservation_Released) \<and>
    snd(source_coupling_step(Coupling_Client True(Client_Publication(binding_key(request_binding r))))effect)=
      Coupling_Client_Reply Primary_Published \<and>
    binding_key(request_binding r)\<in>core_published(coupled_core finished) \<and>
    phase_at(machine_state(core_parent(coupled_core finished)))(binding_key(request_binding r))=Some Source_Returned \<and>
    source_units(machine_state(core_parent(coupled_core finished)))(source_account_of(request_binding r))=
      source_units(machine_state(core_parent(coupled_core s)))(source_account_of(request_binding r))+
        binding_amount(request_binding r) \<and>
    core_records(coupled_core finished)(binding_key(request_binding r))=
      Some(progress_terminal_record cert Reversed_Decision) \<and>
    coupled_source finished=coupled_source s \<and> source_coupling_invariant balances finished \<and>
    call_completions(finality_calls.run_calls
      (complete_call_program call_id(Client_Publication(binding_key(request_binding r))))
      (initial_call_machine(coupled_core effect)))call_id=Some Primary_Published"
proof -
  have checked: "certificate_ok cert" using inputs unfolding terminal_evidence_inputs_def by blast
  have ready_shape: "ready=s\<lparr>coupled_receipts:=issue_source_receipt(coupled_source s)cert(coupled_receipts s),
      coupled_core:=progress_prepared_core cert Reversed_Decision(coupled_core s)\<rparr>"
    unfolding ready_def by (rule terminal_evidence_program_records_and_publishes[OF inputs]) (simp add: status)
  have ready_core: "coupled_core ready=progress_prepared_core cert Reversed_Decision(coupled_core s)"
    by (simp add: ready_shape)
  have live: "coupling_live_receipt ready cert"
    using inputs current_fact_issues_a_live_receipt[OF inputs]
    by (simp add: ready_shape coupling_live_receipt_def terminal_evidence_inputs_def)
  have source: "controlled_source_fact(coupled_source ready)(binding_key(request_binding r))=
      Some \<lparr>statement_binding=request_binding r,statement_status=Reversed\<rparr>"
  proof -
    have whole: "certificate_statement cert=\<lparr>statement_binding=request_binding r,statement_status=Reversed\<rparr>"
      using bound status by (cases "certificate_statement cert") auto
    show ?thesis using live bound whole by (simp add: coupling_live_receipt_def)
  qed
  have guard: "coupling_guard True ready(Client_Protocol endpoint 0(Return_Intent r generation versions))"
    using live source certificate by simp
  let ?view = "current_lock_view(coupled_core s)endpoint"
  let ?parent = "core_parent(coupled_core ready)"
  let ?result = "release_to_source ?view r generation(vector_lookup versions)?parent"
  let ?core = "fst(execute_finality_client(Client_Protocol endpoint 0(Return_Intent r generation versions))(coupled_core ready))"
  have returned: "snd(execute_finality_client(Client_Protocol endpoint 0(Return_Intent r generation versions))(coupled_core ready))=
      Protocol_Response Reservation_Released \<and> core_parent ?core=fst ?result"
    using prepared_reversal_executes_return[OF bound certificate checked status epoch owner pending]
    by (simp only: ready_core)
  have owner_ready: "owns_recorded_reservation ?view r generation(vector_lookup versions)(machine_state ?parent)"
    using owner by (simp add: ready_shape progress_prepared_core_def source_link_certificate_event_frames
      source_link_issued_certificate_update_frames)
  have released: "snd ?result=Reservation_Released"
    using owner_ready pending checked status epoch bound certificate
    by (simp add: evidence_release_exact_guard reversed_source_evidence_def ready_shape
      progress_prepared_core_def source_link_certificate_event_frames commit_reservation_event_def
      source_link_issued_certificate_update_frames)
  have closed: "source_units(machine_state(fst ?result))(source_account_of(request_binding r))=
      source_units(machine_state ?parent)(source_account_of(request_binding r))+binding_amount(request_binding r) \<and>
    phase_at(machine_state(fst ?result))(binding_key(request_binding r))=Some Source_Returned"
    using successful_release_restores_exact_amount_and_closes[OF released] by blast
  have registered: "binding_is_registered(machine_state(fst ?result))(request_binding r)"
    by (rule actual_return_preserves_registration[OF owner_ready])
  have preparation: "ready=run_source_coupling(terminal_evidence_actions endpoint cert)s"
    by (simp only: ready_def)
  have no_close: "coupling_closed_binding(Client_Protocol endpoint 0(Return_Intent r generation versions))
    (snd(execute_finality_client(Client_Protocol endpoint 0(Return_Intent r generation versions))(coupled_core ready)))=None"
    by simp
  have actual_return_reply: "snd(source_coupling_step(Coupling_Client True
      (Client_Protocol endpoint 0(Return_Intent r generation versions)))ready)=
    Coupling_Client_Reply(Protocol_Response Reservation_Released)"
    by (simp only: terminal_nonclosing_source_step[OF guard no_close] snd_conv returned[THEN conjunct1])
  have composition: "effect=ready\<lparr>coupled_core:=?core\<rparr>"
    "finished=ready\<lparr>coupled_core:=fst(execute_finality_client(Client_Publication(binding_key(request_binding r)))?core)\<rparr>"
    using terminal_program_composition[OF preparation guard no_close] bound
    by (simp_all add: effect_def finished_def)
  have stored_record: "core_records ?core(binding_key(request_binding r))=Some(progress_terminal_record cert Reversed_Decision)"
    by (simp add: terminal_protocol_keeps_core_metadata ready_shape progress_prepared_core_def bound)
  have completed: "terminal_effect_completed ?core(progress_terminal_record cert Reversed_Decision)"
    using returned closed registered bound
    by (simp add: terminal_effect_completed_def progress_terminal_record_def Let_def)
  have record_key: "core_records ?core(binding_key(terminal_binding(progress_terminal_record cert Reversed_Decision)))=
    Some(progress_terminal_record cert Reversed_Decision)"
    using stored_record by (simp add: progress_terminal_record_def bound)
  have primary: "snd(execute_finality_client(Client_Publication(binding_key(request_binding r)))?core)=Primary_Published \<and>
      binding_key(request_binding r)\<in>core_published(fst(execute_finality_client(Client_Publication(binding_key(request_binding r)))?core))"
    using terminal_publication_completes_a_recorded_effect[OF record_key completed]
    by (simp add: progress_terminal_record_def bound)
  have invariant: "source_coupling_invariant balances finished"
    unfolding finished_def by (rule source_coupling_run_preserves_invariant[OF healthy])
  have call: "call_completions(finality_calls.run_calls
      (complete_call_program call_id(Client_Publication(binding_key(request_binding r))))
      (initial_call_machine ?core))call_id=Some Primary_Published"
    using finality_calls.a_fresh_initial_call_has_a_four_action_completion
      [of call_id "Client_Publication(binding_key(request_binding r))" ?core] primary by simp
  have source_frame: "coupled_source ready=coupled_source s" by (simp add: ready_shape)
  have units_frame: "source_units(machine_state ?parent)=source_units(machine_state(core_parent(coupled_core s)))"
    by (simp add: ready_core progress_prepared_core_def source_link_certificate_event_frames
      source_link_issued_certificate_update_frames)
  show ?thesis
    by (rule conjI[OF actual_return_reply])
      (use returned primary stored_record invariant guard call closed source_frame units_frame in
        \<open>simp add: composition coupling_client_step_def guarded_client_is_the_actual_child[OF guard]
          terminal_publication_preserves_parent_and_records Let_def\<close>)
qed

section \<open>Missing Evidence Is an Actual Obstruction\<close>

theorem observed_evidence_cannot_record_a_terminal:
  assumes "statement_status(certificate_statement cert)=Observed"
  shows "snd(record_terminal cert core)=Finality_Rejected"
  using assms by (simp add: record_terminal_def Let_def)

theorem unissued_monetary_evidence_rejects_the_actual_terminal_call:
  assumes "binding_operation(statement_binding(certificate_statement cert))=Destination_Credit"
    "cert\<notin>set(coupled_receipts s)"
  shows "source_coupling_step(Coupling_Client True(Client_Terminal cert))s=(s,Coupling_Rejected)"
  using assms by (simp add: coupling_client_step_def coupling_monetary_def coupling_live_receipt_def)

theorem unknown_source_outcome_does_not_enable_return:
  assumes "controlled_source_fact(coupled_source s)(binding_key(request_binding r))=None"
  shows "source_coupling_step(Coupling_Client available
    (Client_Protocol endpoint index(Return_Intent r generation versions)))s=(s,Coupling_Rejected)"
  using assms by (simp add: coupling_client_step_def)

theorem absent_current_fact_does_not_issue_terminal_evidence:
  assumes "controlled_source_fact(coupled_source s)
    (binding_key(statement_binding(certificate_statement cert)))\<noteq>Some(certificate_statement cert)"
  shows "coupled_receipts(fst(source_coupling_step(Coupling_Issue True cert)s))=coupled_receipts s"
  using absent_source_fact_produces_no_receipt[OF assms]
  by (simp add: coupling_issue_result_def Let_def)

text \<open>The terminal programs start after an exact source debit has been
  mirrored and the controlled producer has supplied its current terminal fact.
  Their premises name certificate checking, signature-slot availability,
  current credit admission or reservation ownership, pending phase, relay
  epoch and the existing credit marker. They do not assume a successful
  terminal reply or a release-safety proposition.

  The finite lists explicitly deliver issuance, recording, publication of
  evidence, the financial effect and primary publication without an intervening
  source or context change. Their conclusions include the actual successful
  financial and publication replies, not merely completion of an arbitrary
  callback or a decreasing list length. The final primary command also has a
  fresh durable invocation/dispatch/collection/completion execution.

  This is conditional terminal progress in a quiescent delivery interval.
  It does not prove eventual source evidence, network fairness, replicated
  decision agreement or unconditional termination. An observed statement,
  an unissued monetary receipt or an unknown source outcome has the concrete
  rejecting behavior stated above. Reversal updates the local mirror of the
  already returned allocation; the controlled source is not refunded twice.\<close>

end

end
