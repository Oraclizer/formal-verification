theory Pilot_Debit_Frame
  imports Pilot_Debit
begin

lemma an_applied_reference_debit_is_one_exact_source_event:
  assumes applied: "reference_debit_transition cfg request generation versions owner_total owner_funded machine =
      (next, Source_Debited)"
  shows "machine_state next = apply_reservation_event (Source_Effect_Event (request_binding request)) (machine_state machine) \<and>
    machine_journal next = machine_journal machine @ [Source_Effect_Event (request_binding request)]"
  using applied
  by (cases "reservation_at (machine_state machine) (binding_key (request_binding request))")
     (auto simp: reference_debit_transition_def execute_source_effect_def
        record_observation_def commit_reservation_event_def Let_def split: if_splits)

lemma a_refused_reference_debit_cannot_change_the_ledger_or_its_effect_journal:
  assumes refused: "reference_debit_transition cfg request generation versions owner_total owner_funded machine =
      (next, Request_Rejected)"
  shows "machine_state next = machine_state machine \<and> machine_journal next = machine_journal machine"
  using refused
  by (cases "reservation_at (machine_state machine) (binding_key (request_binding request))")
     (auto simp: reference_debit_transition_def execute_source_effect_def
        record_observation_def commit_reservation_event_def Let_def split: if_splits)

lemma a_debit_does_not_change_other_pools_or_destination_funding:
  assumes applied: "reference_debit_transition cfg request generation versions owner_total owner_funded machine =
      (next, Source_Debited)"
    and other: "pool \<noteq> source_account_of (request_binding request)"
  shows "source_units (machine_state next) pool = source_units (machine_state machine) pool"
    "destination_units (machine_state next) = destination_units (machine_state machine)"
    "funded_units (machine_state next) = funded_units (machine_state machine)"
  using conjunct1[OF an_applied_reference_debit_is_one_exact_source_event[OF applied]] other
  by (simp_all add: set_phase_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms an_applied_reference_debit_is_one_exact_source_event
      a_refused_reference_debit_cannot_change_the_ledger_or_its_effect_journal
      a_debit_does_not_change_other_pools_or_destination_funding})
  then () else error "Unexpected oracle in the pilot debit frame"
\<close>

end
