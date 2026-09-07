(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Lineage
  imports Reservation_Scenarios
begin

context source_attestation
begin

lemma reservation_run_append:
  "run_reservations balances(first@second)m =
    run_reservations balances second(run_reservations balances first m)"
  by (induction first arbitrary:m) auto

end

section \<open>Different Roots Sharing the Same Account\<close>

definition mixed_base where
  "mixed_base = sample.run_reservations sample_balances
    (sample_credit_trace 17 @ sample_credit_trace 23) sample_initial"

lemma mixed_base_staged:
  "mixed_base=sample.run_reservations sample_balances(sample_credit_trace 23)sample_credited"
  by (simp only: mixed_base_def sample.reservation_run_append sample_credited_def)

lemmas staged_trace_defs = sample_binding_def example_binding_def sample_statement_def sample_certificate_def
  sample_request_def sample_context_def sample_source_context_def sample_metadata_def example_context_def
  sample_balances_def initial_reservation_state_def sample_prefix_def sample_credit_trace_def
  current_use_allowed_def required_footprint_def owns_current_reservation_def owns_recorded_reservation_def
  phase_at_def set_phase_def finish_reservation_def binding_is_registered_def source_was_debited_def
  source_account_of_def destination_account_of_def holder_account_def metadata_permission_def
  get_reg_state_def get_asset_state_def ordinary_transfer_allowed_def sample_auth_defs sample.protocol_definitions
  sample.published_receive_expansion sample.run_reservations.simps sample.reservation_step.simps
  record_observation_def commit_reservation_event_def record_credit_def credit_marker_def empty_message_state_def Let_def

lemma mixed_base_state:
  "machine_state mixed_base=(machine_state sample_credited)\<lparr>
    reservation_at:=(reservation_at(machine_state sample_credited))((0,23):=Some(sample_confirmed_record 23)),
    source_units:=(source_units(machine_state sample_credited))((0,17):=0),
    source_effects:=[sample_binding 17,sample_binding 23],
    issued_certificates:=[sample_certificate 17,sample_certificate 23],
    received_messages:=record_credit(sample_binding 23)(received_messages(machine_state sample_credited)),
    destination_units:=(destination_units(machine_state sample_credited))((2,17,3):=10),
    funded_units:=(funded_units(machine_state sample_credited))(((0,23),(2,17,3)):=5)\<rparr>"
  by (simp add: mixed_base_staged sample_credited_state sample_confirmed_record_def staged_trace_defs fun_eq_iff)

definition spend_request where
  "spend_request root recipient amount = (sample_request root)\<lparr>
    request_binding := descendant_binding (sample_binding root) recipient amount Ordinary_Transfer_Effect\<rparr>"
definition lineage_history where
  "lineage_history root = fst(execute_descendant (sample_context ACTIVE)
    (spend_request root 4 5) (sample_binding root) 3 4 5 mixed_base)"

lemmas lineage_trace_defs = spend_request_def lineage_history_def execute_descendant_def descendant_binding_def
  mixed_base_state sample_credited_state staged_trace_defs

lemma equal_balances_and_credit_records_different_lineage:
  "source_units(machine_state(lineage_history 17)) = source_units(machine_state(lineage_history 23)) \<and>
   destination_units(machine_state(lineage_history 17)) = destination_units(machine_state(lineage_history 23)) \<and>
   received_messages(machine_state(lineage_history 17)) = received_messages(machine_state(lineage_history 23)) \<and>
   funded_units(machine_state(lineage_history 17))((0,17),(2,17,4))=5 \<and>
   funded_units(machine_state(lineage_history 23))((0,17),(2,17,4))=0"
  by (simp add: lineage_trace_defs)

lemma same_current_continuation_distinguishes_lineage:
  "snd(execute_descendant (sample_context ACTIVE) (spend_request 17 5 1)
     (sample_binding 17) 4 5 1 (lineage_history 17))=Descendant_Executed \<and>
   snd(execute_descendant (sample_context ACTIVE) (spend_request 17 5 1)
     (sample_binding 17) 4 5 1 (lineage_history 23))=Request_Rejected"
  by (simp add: lineage_trace_defs)

definition pooled_observation where
  "pooled_observation m=(source_units(machine_state m),destination_units(machine_state m),
    received_messages(machine_state m))"

theorem pooled_balances_and_credit_records_do_not_determine_continuation:
  "\<not>(\<exists>decide. \<forall>m\<in>{lineage_history 17,lineage_history 23}.
    decide(pooled_observation m)=snd(execute_descendant(sample_context ACTIVE)
      (spend_request 17 5 1)(sample_binding 17)4 5 1 m))"
  using equal_balances_and_credit_records_different_lineage same_current_continuation_distinguishes_lineage
  by (auto simp: pooled_observation_def)

text \<open>Both histories start with two actual source effects and actual
  message credits to a shared account. They agree on total balances and the
  complete credit records, but move different roots to the next holder. The
  same current authorized continuation succeeds in only one. Rooted funding
  therefore carries information consumed by onward spending that this pooled
  observation loses.\<close>

end
