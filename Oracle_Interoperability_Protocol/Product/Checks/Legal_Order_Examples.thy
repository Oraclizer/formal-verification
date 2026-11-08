theory Legal_Order_Examples
  imports "../Legal_Product" "OIP_Product_Base.Lock_Endpoint_Examples"
begin

definition legal_example_order where
  "legal_example_order action event prior deadline destination = \<lparr>legal_origin = (0,event),
    legal_binding = (example_binding event)\<lparr>binding_asset := 17, binding_operation := Regulatory_State_Effect action\<rparr>,
    legal_asset = 17, legal_action = action, legal_officer = 7, legal_jurisdiction = 1, legal_basis = 1,
    legal_scope = {17}, legal_issuance_epoch = 9, legal_predecessor = prior,
    legal_appeal_deadline = deadline, legal_destination = destination\<rparr>"

abbreviation example_freeze_order where
  "example_freeze_order \<equiv> legal_example_order FREEZE 40 None None None"

abbreviation example_seize_order where
  "example_seize_order \<equiv> legal_example_order SEIZE 41 (Some (0,40)) (Some 5) None"

abbreviation example_confiscate_order where
  "example_confiscate_order \<equiv> legal_example_order CONFISCATE 42 (Some (0,41)) (Some 5) (Some 3)"

definition legal_example_reads where
  "legal_example_reads mode ticks m = initial_product_reads 100 (initial_settlement_world 99
    (initial_origin_world ((lock_example_world m)\<lparr>product_calls := initial_call_machine
      ((initial_finality_core sample_balances (sample_metadata mode) lock_example_contexts)\<lparr>
        core_parent := advance_reservation_time ticks m\<rparr>)\<rparr>)))"

definition legal_example_world where
  "legal_example_world mode ticks m = (initial_legal_world (legal_example_reads mode ticks m))\<lparr>
    issued_legal_orders := (\<lambda>_. None)((0,42) := Some example_confiscate_order),
    committed_legal_events := (\<lambda>_. None)((0,40) := Some
       \<lparr>applied_order = example_freeze_order, applied_legal_cut = \<lparr>cut_authority_epoch = 9, cut_revision = 0\<rparr>\<rparr>,
       (0,41) := Some \<lparr>applied_order = example_seize_order,
          applied_legal_cut = \<lparr>cut_authority_epoch = 9, cut_revision = 0\<rparr>\<rparr>),
    active_freeze_event := (\<lambda>_. None)(17 := Some (0,40)),
    active_seizure_event := (\<lambda>_. None)(17 := Some (0,41))\<rparr>"

lemmas legal_example_defs = legal_example_world_def legal_example_order_def legal_example_reads_def initial_legal_world_def
  initial_product_reads_def initial_settlement_world_def initial_origin_world_def initial_outcome_world_def
  legal_current_core_def authoritative_read_core_def exact_calls_def outcome_calls_def observed_product_source_def
  legal_current_cut_def observed_product_cut_def current_product_cut_def lock_example_world_def initial_call_machine_def
  initial_finality_core_def sample_metadata_def get_reg_state_def get_asset_state_def legal_current_state_def
  legal_clock_def advance_reservation_time_def commit_reservation_event_def sample_initial_def initial_reservation_machine_def
  initial_reservation_state_def legal_state_gate_def exact_legal_predecessor_def
  recorded_appeal_deadline_def matching_appeal_deadline_def appeal_has_elapsed_def Let_def

lemma both_legal_entries_reject_confiscation_from_active_frozen_or_restricted:
  assumes "mode \<in> {ACTIVE, FROZEN, RESTRICTED}"
  shows "legal_admission_at_cut (\<lambda>_ _ _ _ _ _ _. True) (\<lambda>_ _ _ _. True)
    stage entry 7 example_confiscate_order (legal_example_world mode 5 sample_initial) = Legal_Refuse Missing_Prior_Seizure"
  using assms by (cases stage) (auto simp: legal_admission_at_cut_def legal_example_defs)

lemma both_legal_entries_reject_before_the_recorded_appeal_deadline:
  "legal_admission_at_cut (\<lambda>_ _ _ _ _ _ _. True) (\<lambda>_ _ _ _. True)
    stage entry 7 example_confiscate_order (legal_example_world SEIZED 4 sample_initial) = Legal_Refuse Appeal_Still_Open"
  by (cases stage) (simp_all add: legal_admission_at_cut_def legal_example_defs)

lemma exact_seizure_and_elapsed_deadline_activate_both_legal_entries:
  "legal_admission_at_cut (\<lambda>_ _ _ _ _ _ _. True) (\<lambda>_ _ _ _. True)
    stage entry 7 example_confiscate_order (legal_example_world SEIZED 5 sample_initial) = Legal_Admit"
  by (cases stage) (simp_all add: legal_admission_at_cut_def legal_example_defs)

lemma seized_state_without_the_seizure_record_is_insufficient:
  "let state = legal_example_world SEIZED 5 sample_initial;
       missing = state\<lparr>committed_legal_events := (committed_legal_events state)((0,41) := None)\<rparr>
   in legal_state_gate missing example_confiscate_order = Legal_Refuse Missing_Prior_Seizure"
  by (simp add: legal_example_defs)

lemma authority_refusal_is_distinct_even_after_the_appeal_deadline:
  "legal_admission_at_cut (\<lambda>_ _ _ _ _ _ _. False) (\<lambda>_ _ _ _. True)
    stage entry 7 example_confiscate_order (legal_example_world SEIZED 5 sample_initial) = Legal_Refuse Invalid_Legal_Authority"
  by (simp add: legal_admission_at_cut_def)

lemma actual_legal_callback_stops_an_early_confiscation:
  "sample.run_legal_effect (\<lambda>_ _ _ _ _ _ _. True) (\<lambda>_ _ _ _. True)
    permitted verified maintainers registered verified_ack stage entry 7 expected call_id example_confiscate_order payload
    (legal_example_world SEIZED 4 sample_initial) =
     (legal_example_world SEIZED 4 sample_initial, Legal_Blocked Appeal_Still_Open)"
  by (simp add: sample.run_legal_effect_def both_legal_entries_reject_before_the_recorded_appeal_deadline)

definition confiscation_gate_without_the_appeal_check where
  "confiscation_gate_without_the_appeal_check s order =
    (if legal_current_state s (fst (legal_origin order)) (legal_asset order) \<noteq> Some SEIZED \<or>
         \<not> exact_legal_predecessor s order (active_seizure_event s (legal_asset order)) SEIZE
     then Legal_Refuse Missing_Prior_Seizure
     else if \<not> matching_appeal_deadline s order then Legal_Refuse Appeal_Deadline_Mismatch
     else if legal_destination order = None then Legal_Refuse Missing_Confiscation_Destination else Legal_Admit)"

lemma removing_only_the_appeal_check_admits_the_same_early_confiscation:
  "legal_state_gate (legal_example_world SEIZED 4 sample_initial) example_confiscate_order = Legal_Refuse Appeal_Still_Open \<and>
    confiscation_gate_without_the_appeal_check (legal_example_world SEIZED 4 sample_initial) example_confiscate_order = Legal_Admit"
  by (simp add: confiscation_gate_without_the_appeal_check_def legal_example_defs)

abbreviation example_shortened_confiscate_order where
  "example_shortened_confiscate_order \<equiv> example_confiscate_order\<lparr>legal_appeal_deadline := Some 4\<rparr>"

lemma actual_legal_callback_rejects_a_shortened_deadline:
  "let initial = legal_example_world SEIZED 4 sample_initial;
       s = initial\<lparr>issued_legal_orders := (issued_legal_orders initial)((0,42) := Some example_shortened_confiscate_order)\<rparr>
    in sample.run_legal_effect (\<lambda>_ _ _ _ _ _ _. True) (\<lambda>_ _ _ _. True)
         permitted verified maintainers registered verified_ack stage entry 7 expected call_id
         example_shortened_confiscate_order payload s = (s, Legal_Blocked Appeal_Deadline_Mismatch)"
  by (cases stage) (simp_all add: sample.run_legal_effect_def legal_admission_at_cut_def legal_example_defs)

definition confiscation_gate_using_only_the_supplied_deadline where
  "confiscation_gate_using_only_the_supplied_deadline s order =
    (if legal_current_state s (fst (legal_origin order)) (legal_asset order) \<noteq> Some SEIZED \<or>
         \<not> exact_legal_predecessor s order (active_seizure_event s (legal_asset order)) SEIZE
     then Legal_Refuse Missing_Prior_Seizure
     else if \<not> (\<exists>deadline. legal_appeal_deadline order = Some deadline \<and> deadline \<le> legal_clock s)
       then Legal_Refuse Appeal_Still_Open
     else if legal_destination order = None then Legal_Refuse Missing_Confiscation_Destination else Legal_Admit)"

lemma removing_only_the_recorded_deadline_binding_admits_the_shortened_request:
  "let s = legal_example_world SEIZED 4 sample_initial in
    legal_state_gate s example_shortened_confiscate_order = Legal_Refuse Appeal_Deadline_Mismatch \<and>
    confiscation_gate_using_only_the_supplied_deadline s example_shortened_confiscate_order = Legal_Admit"
  by (simp add: confiscation_gate_using_only_the_supplied_deadline_def legal_example_defs)

lemma restriction_record_does_not_substitute_for_the_freeze_reference:
  "let prior = legal_example_order RESTRICT 40 None None None;
       state = legal_example_world FROZEN 0 sample_initial;
       wrong = state\<lparr>committed_legal_events := (committed_legal_events state)((0,40) := Some
         \<lparr>applied_order = prior, applied_legal_cut = \<lparr>cut_authority_epoch = 9, cut_revision = 0\<rparr>\<rparr>)\<rparr>
   in legal_state_gate wrong example_seize_order = Legal_Refuse Missing_Prior_Freeze \<and>
      legal_state_gate state example_seize_order = Legal_Admit"
  by (simp add: legal_example_defs)

lemma restriction_can_be_admitted_with_a_real_reservation:
  "legal_state_gate (legal_example_world ACTIVE 0 lock_example_held) (legal_example_order RESTRICT 43 None None None) = Legal_Admit \<and>
    asset_owner (machine_state (core_parent (legal_current_core (legal_example_world ACTIVE 0 lock_example_held)))) 17 = Some (0,17)"
  by (simp add: legal_example_defs lock_example_current_reservation)

lemma the_public_transition_without_the_legal_gate_accepts_active_confiscation:
  "\<exists>next. sync 0 CONFISCATE 17 (sample_metadata ACTIVE) = Some next \<and>
    get_reg_state next 0 17 = Some CONFISCATED"
  by (simp add: sync_def sample_metadata_def get_reg_state_def get_asset_state_def acquire_lock_def is_locked_def
    release_lock_def update_all_chains_def connected_chains_def asset_exists_def Let_def)

lemma the_public_transition_applies_lawful_seized_confiscation_to_both_domains:
  "\<exists>next. sync 0 CONFISCATE 17 (sample_metadata SEIZED) = Some next \<and>
    get_reg_state next 0 17 = Some CONFISCATED \<and> get_reg_state next 2 17 = Some CONFISCATED"
  by (simp add: sync_def sample_metadata_def get_reg_state_def get_asset_state_def acquire_lock_def is_locked_def
    release_lock_def update_all_chains_def connected_chains_def asset_exists_def Let_def)

end
