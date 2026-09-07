(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Examples
  imports Reservation_Ownership Source_Non_Reuse
begin

section \<open>Constructed Sources and Current Contexts\<close>

definition sample_binding :: "nat \<Rightarrow> transfer_binding" where
  "sample_binding event=(example_binding event)\<lparr>binding_asset:=(if event=23 then 17 else event)\<rparr>"
definition sample_statement :: "nat \<Rightarrow> source_statement" where
  "sample_statement event=\<lparr>statement_binding=sample_binding event,
    statement_status=(if event=22 then Reversed else Finalized)\<rparr>"
definition sample_truth :: "source_statement \<Rightarrow> bool" where
  "sample_truth statement \<longleftrightarrow> statement\<in>{sample_statement 17,sample_statement 22,sample_statement 23}"
definition sample_source :: "source_key \<Rightarrow> source_statement option" where
  "sample_source key=(if key=(0,17) then Some(sample_statement 17)
    else if key=(0,22) then Some(sample_statement 22)
    else if key=(0,23) then Some(sample_statement 23) else None)"
definition sample_signed :: "nat \<Rightarrow> nat \<Rightarrow> source_statement \<Rightarrow> bool" where
  "sample_signed signer epoch statement \<longleftrightarrow> signer=0 \<or> sample_truth statement"
definition sample_verifies :: "source_certificate \<Rightarrow> bool" where
  "sample_verifies cert \<longleftrightarrow> certificate_signature cert=42 \<and>
    (\<forall>signer\<in>set(certificate_signers cert).
      sample_signed signer(certificate_epoch cert)(certificate_statement cert))"

interpretation sample: source_attestation example_roster example_faulty example_bound example_threshold
  sample_verifies sample_signed sample_truth sample_source
proof unfold_locales
  fix epoch
  show "finite(example_roster epoch)" by (simp add: example_roster_def)
  show "example_faulty epoch\<subseteq>example_roster epoch" by (simp add: example_faulty_def example_roster_def)
  show "card(example_faulty epoch)\<le>example_bound epoch" by (simp add: example_faulty_def example_bound_def)
  show "example_bound epoch<example_threshold epoch" by (simp add: example_bound_def example_threshold_def)
next
  fix cert signer
  assume "sample_verifies cert" "signer\<in>set(certificate_signers cert)"
  then show "sample_signed signer(certificate_epoch cert)(certificate_statement cert)"
    by (simp add: sample_verifies_def)
next
  fix signer epoch statement
  assume "signer\<in>example_roster epoch" "signer\<notin>example_faulty epoch" "sample_signed signer epoch statement"
  then show "sample_truth statement" by (simp add: sample_signed_def example_faulty_def)
next
  fix statement
  assume "sample_truth statement" "statement_status statement\<noteq>Observed"
  then show "sample_source(binding_key(statement_binding statement))=Some statement"
    by (auto simp: sample_truth_def sample_source_def sample_statement_def sample_binding_def example_binding_def)
qed

definition sample_certificate :: "nat \<Rightarrow> source_certificate" where
  "sample_certificate event=\<lparr>certificate_statement=sample_statement event,certificate_epoch=8,
    certificate_signers=[1,2],certificate_signature=42\<rparr>"
definition sample_request :: "nat \<Rightarrow> execution_request" where
  "sample_request event=\<lparr>request_binding=sample_binding event,request_certificate=sample_certificate event,
    request_caller=7,request_authority_epoch=9,request_version=4\<rparr>"
definition sample_metadata :: "reg_state \<Rightarrow> global_state" where
  "sample_metadata state=\<lparr>gs_chains=(\<lambda>domain asset.
    if domain\<in>{0,2} \<and> asset\<in>{17,22,30} then Some\<lparr>as_reg_state=state\<rparr> else None),
    gs_locks=(\<lambda>_.False)\<rparr>"
definition sample_context :: "reg_state \<Rightarrow> lock_context" where
  "sample_context state=\<lparr>lock_authority=example_context,lock_metadata=sample_metadata state,
    lock_restrictions=(\<lambda>_.True),lock_dependencies=(\<lambda>_.[]),
    lock_write_permissions={(7,17,9),(7,17,12),(7,17,8)},lock_spend_permissions=UNIV\<rparr>"
definition sample_source_context :: "reg_state \<Rightarrow> lock_context" where
  "sample_source_context state=(sample_context state)\<lparr>
    lock_authority:=example_context\<lparr>context_endpoint:=0\<rparr>\<rparr>"
definition sample_balances :: "source_account \<Rightarrow> nat" where
  "sample_balances account=(if account=(0,17) then 10 else if account=(0,22) then 5 else 0)"
definition sample_initial :: reservation_machine where
  "sample_initial=initial_reservation_machine sample_balances"
definition sample_prefix :: "nat \<Rightarrow> reservation_action list" where
  "sample_prefix event=[Acquire_Action(sample_source_context ACTIVE)(sample_request event)(\<lambda>_.0)10,
    Dispatch_Action(sample_source_context ACTIVE)(sample_request event)0(\<lambda>_.0),
    Source_Action(sample_source_context ACTIVE)(sample_request event)0(\<lambda>_.0)]"
definition sample_burnt :: "nat \<Rightarrow> reservation_machine" where
  "sample_burnt event=sample.run_reservations sample_balances(sample_prefix event)sample_initial"
definition sample_credit_trace :: "nat \<Rightarrow> reservation_action list" where
  "sample_credit_trace event=sample_prefix event@[
    Publish_Action(sample_certificate event),Deliver_Action Bypass_Route example_context(sample_request event),
    Reconcile_Action(sample_source_context ACTIVE)(sample_request event)0(\<lambda>_.0)]"
definition sample_credited :: reservation_machine where
  "sample_credited=sample.run_reservations sample_balances(sample_credit_trace 17)sample_initial"

lemmas sample_data_defs = sample_binding_def example_binding_def sample_statement_def sample_certificate_def
  sample_request_def sample_context_def sample_source_context_def sample_metadata_def example_context_def
  sample_balances_def sample_initial_def initial_reservation_machine_def initial_reservation_state_def
  sample_prefix_def sample_burnt_def sample_credit_trace_def sample_credited_def
  current_use_allowed_def required_footprint_def owns_current_reservation_def owns_recorded_reservation_def
  phase_at_def set_phase_def finish_reservation_def binding_is_registered_def source_was_debited_def
  source_account_of_def destination_account_of_def holder_account_def metadata_permission_def
  get_reg_state_def get_asset_state_def ordinary_transfer_allowed_def

lemmas sample_auth_defs = sample.certificate_ok_def sample.credit_admissible_def sample.authenticated_request_def
  sample_verifies_def sample_signed_def sample_truth_def example_roster_def example_threshold_def

lemma sample_fact_accepted:
  "event\<in>{17,22,23} \<Longrightarrow> sample.certificate_ok(sample_certificate event)"
  by (auto simp: sample_auth_defs sample_data_defs)

lemma sample_metadata_is_valid:
  "valid_state(sample_metadata state)"
  by (auto simp: sample_metadata_def valid_state_def consistent_state_def no_locked_without_reason_def
      get_reg_state_def get_asset_state_def is_locked_def split: if_splits)

lemma source_acquire_dispatch_effect_activates:
  "source_effects(machine_state(sample_burnt 17))=[sample_binding 17] \<and>
    source_units(machine_state(sample_burnt 17))(0,17)=5 \<and>
    asset_owner(machine_state(sample_burnt 17))17=Some(0,17)"
  by (simp add: sample_data_defs sample.protocol_definitions sample.run_reservations.simps
      sample.reservation_step.simps record_observation_def commit_reservation_event_def Let_def)

lemma full_credit_consumer_activates:
  "credit_history(received_messages(machine_state sample_credited))=[sample_binding 17] \<and>
    destination_units(machine_state sample_credited)(2,17,3)=5 \<and>
    funded_units(machine_state sample_credited)((0,17),(2,17,3))=5 \<and>
    asset_owner(machine_state sample_credited)17=None"
  by (simp add: sample_data_defs sample_auth_defs sample.protocol_definitions
      sample.published_receive_expansion sample.run_reservations.simps sample.reservation_step.simps
      record_observation_def commit_reservation_event_def record_credit_def empty_message_state_def Let_def)

lemma competing_acquisition_is_busy:
  "snd(acquire_reservation(sample_source_context ACTIVE)
    ((sample_request 23)\<lparr>request_binding:=(sample_binding 23)\<lparr>binding_asset:=17\<rparr>\<rparr>)
    (\<lambda>_.0)10(sample_burnt 17))=Reservation_Busy"
  by (simp add: sample_data_defs sample.protocol_definitions sample.run_reservations.simps
      sample.reservation_step.simps record_observation_def commit_reservation_event_def Let_def)

lemma malformed_zero_dispatch_is_rejected:
  fixes m :: reservation_machine
  assumes "binding_amount(request_binding r)=0"
  shows "snd(dispatch_source c r g versions m)=Request_Rejected \<and>
    machine_state(fst(dispatch_source c r g versions m))=machine_state m"
  using assms by (simp add: dispatch_source_def record_observation_def)

text \<open>The context gives a privileged application operator explicit access
  while preserving the independent regulatory and balance checks. The source
  instance certifies two different events crediting the same account and a
  separate reversed outcome. It is a finite witness of the assumptions, not
  a cryptographic implementation.\<close>

end
