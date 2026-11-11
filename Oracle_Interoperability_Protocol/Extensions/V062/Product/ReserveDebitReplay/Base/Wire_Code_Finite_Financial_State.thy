theory Wire_Code_Finite_Financial_State
  imports Wire_Code_Finite_Maps
begin

record code_finite_financial_state =
  finite_asset_owners :: "(nat \<times> source_key) list"
  finite_reservations :: "(source_key \<times> asset_reservation) list"
  finite_asset_values :: "(nat \<times> nat) list"
  finite_asset_versions :: "(nat \<times> nat) list"
  finite_source_units :: "(source_account \<times> nat) list"
  finite_destination_units :: "(destination_account \<times> nat) list"
  finite_funded_units :: "((source_key \<times> destination_account) \<times> nat) list"
  finite_source_effects :: "transfer_binding list"
  finite_issued_certificates :: "source_certificate list"
  finite_consumed_at :: "(nat \<times> source_key) list"
  finite_credit_history :: "transfer_binding list"
  finite_descendants :: "descendant_effect list"
  finite_clock :: nat

definition code_interpret_finite_financial :: "code_finite_financial_state \<Rightarrow> reservation_state" where
  "code_interpret_finite_financial financial =
    \<lparr>asset_owner = map_of (finite_asset_owners financial),reservation_at = map_of (finite_reservations financial),
     asset_value = code_finite_nat_default (finite_asset_values financial),
     asset_version = code_finite_nat_default (finite_asset_versions financial),
     source_units = code_finite_nat_default (finite_source_units financial),
     destination_units = code_finite_nat_default (finite_destination_units financial),
     funded_units = code_finite_nat_default (finite_funded_units financial),
     source_effects = finite_source_effects financial,issued_certificates = finite_issued_certificates financial,
     received_messages = \<lparr>consumed_at = set (finite_consumed_at financial),credit_history = finite_credit_history financial\<rparr>,
     lawful_descendants = finite_descendants financial,reservation_clock = finite_clock financial\<rparr>"

record code_finite_reservation_machine =
  finite_machine_state :: code_finite_financial_state
  finite_machine_journal :: "reservation_event list"
  finite_machine_observations :: "completed_observation list"

definition code_interpret_finite_machine :: "code_finite_reservation_machine \<Rightarrow> reservation_machine" where
  "code_interpret_finite_machine machine =
    \<lparr>machine_state = code_interpret_finite_financial (finite_machine_state machine),
     machine_journal = finite_machine_journal machine,machine_observations = finite_machine_observations machine\<rparr>"

definition code_finite_set_phase :: "source_key \<Rightarrow> reservation_phase \<Rightarrow> code_finite_financial_state \<Rightarrow> code_finite_financial_state" where
  "code_finite_set_phase key phase financial =
    financial\<lparr>finite_reservations := code_finite_alter key (\<lambda>stored. stored\<lparr>reservation_phase := phase\<rparr>)
      (finite_reservations financial)\<rparr>"

definition code_finite_source_effect :: "transfer_binding \<Rightarrow> code_finite_financial_state \<Rightarrow> code_finite_financial_state" where
  "code_finite_source_effect binding financial =
    (code_finite_set_phase (binding_key binding) Source_Pending financial)\<lparr>
      finite_source_units := code_finite_put (source_account_of binding)
        (code_finite_nat_default (finite_source_units financial) (source_account_of binding) - binding_amount binding)
        (finite_source_units financial),finite_source_effects := finite_source_effects financial @ [binding]\<rparr>"

definition code_finite_commit_source_effect :: "transfer_binding \<Rightarrow> code_finite_reservation_machine \<Rightarrow> code_finite_reservation_machine" where
  "code_finite_commit_source_effect binding machine = machine\<lparr>
    finite_machine_state := code_finite_source_effect binding (finite_machine_state machine),
    finite_machine_journal := finite_machine_journal machine @ [Source_Effect_Event binding]\<rparr>"

definition code_finite_record_observation :: "execution_request \<Rightarrow> reservation_reply \<Rightarrow>
  code_finite_reservation_machine \<Rightarrow> (code_finite_reservation_machine \<times> reservation_reply)" where
  "code_finite_record_observation request reply machine =
    (machine\<lparr>finite_machine_observations := finite_machine_observations machine @
      [\<lparr>observation_key = binding_key (request_binding request),observation_binding = request_binding request,
        observation_asset = binding_asset (request_binding request),observation_caller = request_caller request,
        observation_version = request_version request,observation_authority_epoch = request_authority_epoch request,
        observation_reply = reply\<rparr>]\<rparr>,reply)"

lemma finite_phase_update_interprets_the_same_frozen_phase_update:
  "code_interpret_finite_financial (code_finite_set_phase key phase financial) =
    set_phase key phase (code_interpret_finite_financial financial)"
  by (simp add: code_interpret_finite_financial_def code_finite_set_phase_def set_phase_def
    finite_alter_preserves_absence_and_changes_only_the_selected_value)

lemma finite_source_event_interprets_exactly_the_existing_source_event:
  "code_interpret_finite_financial (code_finite_source_effect binding financial) =
    apply_reservation_event (Source_Effect_Event binding) (code_interpret_finite_financial financial)"
  by (simp add: code_finite_source_effect_def code_finite_set_phase_def code_interpret_finite_financial_def
    set_phase_def finite_alter_preserves_absence_and_changes_only_the_selected_value
    finite_zero_default_put_is_the_exact_frozen_nat_function_update)

lemma finite_source_commit_interprets_the_same_state_and_appended_journal_event:
  "code_interpret_finite_machine (code_finite_commit_source_effect binding machine) =
    commit_reservation_event (Source_Effect_Event binding) (code_interpret_finite_machine machine)"
  by (simp add: code_interpret_finite_machine_def code_finite_commit_source_effect_def
    finite_source_event_interprets_exactly_the_existing_source_event commit_reservation_event_def)

lemma finite_observation_interprets_the_same_complete_existing_observation:
  "map_prod code_interpret_finite_machine id (code_finite_record_observation request reply machine) =
    record_observation request reply (code_interpret_finite_machine machine)"
  by (simp add: code_finite_record_observation_def code_interpret_finite_machine_def record_observation_def)

text \<open>
  Every component of reservation_state is explicit. No field of its
  financial state is set from a predicted/observed output. The machine
  interpretation keeps the complete existing journal and observation list.
  These are exact equalities to existing frozen operations, not a claim of
  source compiler refinement or a standalone full reference runtime.
\<close>

end
