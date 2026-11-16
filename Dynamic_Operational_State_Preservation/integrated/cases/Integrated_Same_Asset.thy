theory Integrated_Same_Asset
  imports DOSP_Integrated_Authority.Integrated_Authority DOSP_EAB_Coupling_Cases.EAB_Billing_Cases
    Preemptive_Lock_Correctness.Reservation_Lineage
begin

interpretation joined_dosp: integrated_dosp_authority example_roster example_faulty example_bound
  example_threshold sample_verifies sample_signed sample_truth sample_source coupling_policy "{(12,4)}" "(17,7,3)"
  by unfold_locales

lemma coupling_policy_fields [simp]:
  "hub coupling_policy = 1"
  "domain_set coupling_policy = {0,2}"
  "allowed_sources coupling_policy = {0}"
  by (simp_all add: coupling_policy_def)

definition joined_initial :: integrated_authority where
  "joined_initial = \<lparr>consensus_now = 86399, next_publication_sequence = 50,
    metered_ledger = cycle_fixture\<rparr>"

abbreviation first_meter :: integrated_client_command where
  "first_meter \<equiv> Meter_Credit (17,7,3) coupling_ticket 0 Bypass_Route (sample_request 17)"

abbreviation second_meter :: integrated_client_command where
  "second_meter \<equiv> Meter_Credit (17,7,3) (promoted_metadata 12 4) 0 Bypass_Route (sample_request 23)"

abbreviation settlement_tick :: integrated_consensus_command where
  "settlement_tick \<equiv> Advance_Consensus_Time 86400"

abbreviation close_first_lock :: integrated_client_command where
  "close_first_lock \<equiv> Reconcile_Current_Lock 0 (sample_request 17) 0 []"

abbreviation promote_at_cut :: integrated_consensus_command where
  "promote_at_cut \<equiv> Confirm_Promotion_At_Consensus 12 4"

abbreviation reserve_second :: integrated_client_command where
  "reserve_second \<equiv> Prepare_Credit (Client_Protocol 0 0 (Reserve_Intent (sample_request 23) [] 10))"

abbreviation dispatch_second :: integrated_client_command where
  "dispatch_second \<equiv> Prepare_Credit (Client_Protocol 0 0 (Dispatch_Intent (sample_request 23) 0 []))"

abbreviation debit_second :: integrated_client_command where
  "debit_second \<equiv> Prepare_Credit (Client_Protocol 0 0 (Source_Intent (sample_request 23) 0 []))"

abbreviation record_second :: integrated_client_command where
  "record_second \<equiv> Prepare_Credit (Client_Terminal (sample_certificate 23))"

abbreviation certify_second :: integrated_client_command where
  "certify_second \<equiv> Prepare_Credit (Client_Protocol 0 0 (Certificate_Intent (sample_certificate 23)))"

abbreviation prepare_second_credit :: "integrated_event list" where
  "prepare_second_credit \<equiv> map Inl
     [reserve_second, dispatch_second, debit_second, record_second, certify_second]"

definition cutover_prefix :: "integrated_event list" where
  "cutover_prefix =
    [Inl first_meter, Inl close_first_lock, Inr settlement_tick, Inr promote_at_cut]"

definition same_asset_events :: "integrated_event list" where
  "same_asset_events = cutover_prefix @ prepare_second_credit @ [Inl second_meter]"

definition actual_metering_journal :: integrated_journal where
  "actual_metering_journal =
    joined_dosp.journal.run_calls (integrated_call_program 34 0 same_asset_events)
      (initial_call_machine joined_initial)"

abbreviation actual_authority :: integrated_authority where
  "actual_authority \<equiv> call_authority_state actual_metering_journal"

definition after_first_meter :: integrated_authority where
  "after_first_meter = fst (joined_dosp.execute_integrated_client first_meter joined_initial)"

lemma after_first_meter_shape:
  "after_first_meter =
     joined_initial\<lparr>metered_ledger := fst (run_consensus_fixture 86399),
       next_publication_sequence := 51\<rparr>"
  "snd (joined_dosp.execute_integrated_client first_meter joined_initial) =
     Credit_Result (Some (Credit_Metered fixture_billed_usage))"
  using consensus_fixture_commits_the_actual_metered_operation(3)[of 86399]
  by (simp_all add: after_first_meter_def joined_initial_def consensus_fixture_def cycle_fixture_def
      meter_fixture_def fixture_binding Let_def)

lemma actual_journal_replays_the_same_asset_program:
  "actual_authority = joined_dosp.run_integrated_events same_asset_events joined_initial"
proof -
  have ready: "source_call_ready 34 0 (initial_call_machine joined_initial)" by simp
  show ?thesis
    using joined_dosp.integrated_event_program_uses_the_actual_journal_callbacks[OF ready, of same_asset_events]
    by (simp add: actual_metering_journal_def initial_call_machine_def)
qed

definition after_cutover :: integrated_authority where
  "after_cutover = joined_dosp.run_integrated_events (tl cutover_prefix) after_first_meter"

lemmas source_run_defs =
  sample.execute_finality_client_def sample.finality_step_def sample.invoke_protocol_def sample.record_terminal_def
  sample.publish_primary_def sample.publish_at_sequence_def
  sample.protocol_definitions sample.published_receive_expansion
  terminal_effect_completed_def source_origin_present_def current_lock_view_def
  exact_record_reference_def record_reference_def lift_protocol_result_def
  empty_message_state_def record_credit_def record_observation_def commit_reservation_event_def
  vector_lookup_def kind_from_source.simps

lemma first_meter_ledger:
  "fst (run_consensus_fixture 86399) =
    \<lparr>operational_state = fst metered_fixture_result,
      committed_cycles = [successful_cycle (consensus_fixture 86399) fixture_billed_usage]\<rparr>"
  by (rule cycle_ledger_state.equality)
    (simp_all add: consensus_fixture_commits_the_actual_metered_operation)

lemma first_metered_operational_fields:
  "registered_asset (fst metered_fixture_result) = 17"
  "billing_history (degree_state (fst metered_fixture_result)) = [fixture_billed_usage]"
  "route_metadata (degree_state (fst metered_fixture_result)) = coupling_ticket"
  "\<not> unreconciled_soft_write (degree_state (fst metered_fixture_result))"
  using actual_credit_enables_primary_publication(1)
  by (simp_all add: metered_fixture_result_def sample.meter_source_credit_def meter_fixture_def
    primary_fixture_def fixture_binding actual_fixture_delivery_is_new fixture_before_publication
    billing_record_def coupling_policy_def coupling_ticket_def can_commit_def Let_def)

lemma fixture_epoch_value [simp]: "fixture_epoch = 5"
  by (simp add: finality_sample_certified_def finality_sample_recorded_def
      sample.execute_finality_client_def finality_source_prefix_is_the_actual_parent_prefix)

abbreviation first_delivered_machine :: reservation_machine where
  "first_delivered_machine \<equiv> fst (sample.deliver_reserved_credit Bypass_Route example_context
    (sample_request 17) (sample.publish_source_certificate (sample_certificate 17) (sample_burnt 17)))"

lemma first_record_reference:
  "exact_record_reference (finality_sample_certified 17) 0
     (request_binding (sample_request 17)) Confirmed_Decision (request_certificate (sample_request 17))"
  by (simp add: exact_record_reference_def record_reference_def fixture_before_publication fixture_binding sample_request_def)

lemma first_delivery_core:
  "fixture_native_delivery =
    (finality_sample_certified 17)\<lparr>core_parent := first_delivered_machine, core_epoch := 6\<rparr>"
  using first_record_reference
  by (simp add: sample.finality_step_def sample.invoke_protocol_def lift_protocol_result_def
    finality_sample_current_contexts sample_context_def
    terminal_certificate_publishes_the_actual_parent_evidence Let_def)

definition first_paid_core :: finality_core where
  "first_paid_core = (finality_sample_certified 17)\<lparr>core_parent := first_delivered_machine,
    core_epoch := 7, core_published := {(0,17)}\<rparr>"

lemma first_paid_authority:
  "source_authority (fst metered_fixture_result) =
    \<lparr>terminal_authority = first_paid_core, publication_slots = (\<lambda>_. None)(50 \<mapsto> (0,17))\<rparr>"
proof -
  have published: "snd (sample.publish_primary (0,17) (terminal_authority primary_fixture)) = Primary_Published"
    using actual_credit_enables_primary_publication(1)
    by (auto simp: sample.publish_at_sequence_def Let_def split: if_splits)
  have state: "sample.finality_step (Publish_Primary (0,17)) (terminal_authority primary_fixture) =
    (terminal_authority primary_fixture)\<lparr>core_published := insert (0,17)
      (core_published (terminal_authority primary_fixture)), core_epoch := Suc (core_epoch (terminal_authority primary_fixture))\<rparr>"
    using published by (auto simp: sample.finality_step_def sample.publish_primary_def split: option.splits if_splits)
  have authority: "fst fixture_publication = primary_fixture\<lparr>terminal_authority :=
     sample.finality_step (Publish_Primary (0,17)) (terminal_authority primary_fixture),
     publication_slots := (publication_slots primary_fixture)(50 \<mapsto> (0,17))\<rparr>"
    using actual_credit_enables_primary_publication(1)
    by (auto simp: sample.publish_at_sequence_def Let_def split: if_splits)
  show ?thesis
    unfolding metered_fixture_has_one_current_charge(1) authority state
    by (simp add: first_paid_core_def primary_fixture_def meter_fixture_def
      first_delivery_core[unfolded fixture_epoch_value] fixture_before_publication)
qed

lemma live_reconciliation_uses_the_credited_machine:
  "fst (sample.reconcile_recorded_credit (sample_source_context ACTIVE) (sample_request 17) 0
      (\<lambda>_. 0) first_delivered_machine) = sample_credited"
  by (simp add: sample_credited_def sample_credit_trace_def sample.reservation_run_append sample_burnt_def)

lemma first_reconciliation_result:
  "snd (sample.reconcile_recorded_credit (sample_source_context ACTIVE) (sample_request 17) 0
      (\<lambda>_. 0) first_delivered_machine) = Reservation_Released"
  by (simp add: sample_data_defs sample_auth_defs sample.protocol_definitions sample.published_receive_expansion
    sample.run_reservations.simps sample.reservation_step.simps record_observation_def commit_reservation_event_def
    record_credit_def empty_message_state_def Let_def)

lemma non_context_updates_keep_the_lock_view [simp]:
  "current_lock_view (core\<lparr>core_parent := m\<rparr>) endpoint = current_lock_view core endpoint"
  "current_lock_view (core\<lparr>core_published := keys\<rparr>) endpoint = current_lock_view core endpoint"
  "current_lock_view (core\<lparr>core_epoch := epoch\<rparr>) endpoint = current_lock_view core endpoint"
  by (simp_all add: current_lock_view_def)

lemma non_record_updates_keep_the_exact_reference [simp]:
  "exact_record_reference (core\<lparr>core_parent := m\<rparr>) i b k cert = exact_record_reference core i b k cert"
  "exact_record_reference (core\<lparr>core_epoch := n\<rparr>) i b k cert = exact_record_reference core i b k cert"
  "exact_record_reference (core\<lparr>core_published := keys\<rparr>) i b k cert = exact_record_reference core i b k cert"
  by (simp_all add: exact_record_reference_def record_reference_def)

lemma first_paid_reconciliation:
  "sample.execute_finality_client
    (Client_Protocol (fst (binding_key (request_binding (sample_request 17)))) 0
      (Reconcile_Intent (sample_request 17) 0 [])) first_paid_core =
   ((finality_sample_certified 17)\<lparr>core_parent := sample_credited,
         core_epoch := 8, core_published := {(0,17)}\<rparr>, Protocol_Response Reservation_Released)"
  by (simp add: sample.execute_finality_client_def sample.finality_step_def sample.invoke_protocol_def
    first_paid_core_def first_record_reference[unfolded fixture_binding(1)] fixture_binding finality_sample_current_contexts
    lift_protocol_result_def live_reconciliation_uses_the_credited_machine first_reconciliation_result
    empty_vector_represents_zero_versions Let_def)

lemma elapsed_time_keeps_lock_owners [simp]:
  "asset_owner (machine_state (advance_reservation_time elapsed m)) = asset_owner (machine_state m)"
  by (simp add: advance_reservation_time_def commit_reservation_event_def)

lemma a_clock_call_updates_only_time_and_the_native_epoch:
  "fst (sample.execute_finality_client (Client_Protocol endpoint i (Time_Intent elapsed)) core) =
    core\<lparr>core_parent := advance_reservation_time elapsed (core_parent core), core_epoch := Suc (core_epoch core)\<rparr>"
  by (simp add: sample.execute_finality_client_def sample.finality_step_def sample.invoke_protocol_def Let_def)

lemma the_first_asset_is_unlocked [simp]:
  "asset_owner (machine_state sample_credited) 17 = None"
  using full_credit_consumer_activates by blast

definition cutover_reference_state :: integrated_authority where
  "cutover_reference_state = \<lparr>consensus_now = 86400, next_publication_sequence = 51,
    metered_ledger = \<lparr>operational_state = (fst metered_fixture_result)\<lparr>
        degree_state := (degree_state (fst metered_fixture_result))\<lparr>route_metadata := promoted_metadata 12 4\<rparr>,
        source_authority := \<lparr>terminal_authority = (finality_sample_certified 17)\<lparr>
           core_parent := advance_reservation_time 1 sample_credited,
           core_epoch := 9, core_published := {(0,17)}\<rparr>,
           publication_slots = (\<lambda>_. None)(50 \<mapsto> (0,17))\<rparr>\<rparr>,
      committed_cycles = [successful_cycle (consensus_fixture 86399) fixture_billed_usage]\<rparr>\<rparr>"

lemma cutover_state_normal_form: "after_cutover = cutover_reference_state"
  unfolding cutover_reference_state_def after_cutover_def cutover_prefix_def
    after_first_meter_shape(1) first_meter_ledger
  by (simp add: joined_initial_def with_finality_core_def with_operational_state_def first_paid_authority
    first_paid_reconciliation a_clock_call_updates_only_time_and_the_native_epoch
    finality_sample_current_contexts
    promote_settled_asset_def promotion_locks_clear_def promotion_assets_def promotion_allowed_def
    first_metered_operational_fields sample_context_def sample_source_context_def coupling_ticket_def Let_def)

lemma first_meter_releases_then_promotes:
  fixes timed settled :: integrated_authority
  defines "settled \<equiv> fst (joined_dosp.execute_integrated_client close_first_lock after_first_meter)"
    and "timed \<equiv> fst (joined_dosp.execute_integrated_consensus settlement_tick settled)"
  shows "snd (joined_dosp.execute_integrated_client close_first_lock after_first_meter) = Lock_Result Reservation_Released"
    and "snd (joined_dosp.execute_integrated_consensus promote_at_cut timed) =
        Promotion_Result (transition_result.Accepted Promotion_Finalized)"
    and "route_metadata (degree_state (current_operational after_cutover)) = promoted_metadata 12 4"
  unfolding timed_def settled_def cutover_state_normal_form cutover_reference_state_def
    after_first_meter_shape(1) first_meter_ledger
  by (simp_all add: joined_initial_def with_finality_core_def with_operational_state_def first_paid_authority
    first_paid_reconciliation a_clock_call_updates_only_time_and_the_native_epoch
    finality_sample_current_contexts
    promote_settled_asset_def promotion_locks_clear_def promotion_assets_def promotion_allowed_def
    first_metered_operational_fields sample_context_def sample_source_context_def coupling_ticket_def Let_def)

definition before_second_meter :: integrated_authority where
  "before_second_meter = joined_dosp.run_integrated_events prepare_second_credit after_cutover"

lemma certified_fixture_has_only_its_first_terminal_record:
  "core_records (finality_sample_certified 17) = (\<lambda>_. None)((0,17) \<mapsto>
    \<lparr>terminal_binding = sample_binding 17, terminal_kind = Confirmed_Decision,
      terminal_evidence = [sample_certificate 17]\<rparr>)"
proof (rule ext)
  fix k
  show "core_records (finality_sample_certified 17) k =
    ((\<lambda>_. None)((0,17) \<mapsto> \<lparr>terminal_binding = sample_binding 17,
      terminal_kind = Confirmed_Decision, terminal_evidence = [sample_certificate 17]\<rparr>)) k"
  proof (cases "k = (0,17)")
    case True
    then show ?thesis by (simp add: fixture_before_publication)
  next
    case False
    then show ?thesis
      by (simp add: finality_sample_certified_def finality_sample_recorded_def
        sample.execute_finality_client_def sample.finality_step_def sample.invoke_protocol_def
        sample.record_terminal_def reject_protocol_intent_def finality_source_prefix_is_the_actual_parent_prefix
        sample_certificate_def sample_statement_def sample_binding_def example_binding_def Let_def
        split: option.splits if_splits)
  qed
qed

abbreviation reserved_authority :: integrated_authority where
  "reserved_authority \<equiv> fst (joined_dosp.execute_integrated_client reserve_second after_cutover)"

abbreviation dispatched_authority :: integrated_authority where
  "dispatched_authority \<equiv> fst (joined_dosp.execute_integrated_client dispatch_second reserved_authority)"

abbreviation debited_authority :: integrated_authority where
  "debited_authority \<equiv> fst (joined_dosp.execute_integrated_client debit_second dispatched_authority)"

abbreviation recorded_authority :: integrated_authority where
  "recorded_authority \<equiv> fst (joined_dosp.execute_integrated_client record_second debited_authority)"

lemma sample_protocol_updates_the_parent_through_its_actual_action:
  assumes "terminal_intent_guard core index intent"
  shows "fst (sample.execute_finality_client (Client_Protocol endpoint index intent) core) =
    core\<lparr>core_parent := sample.reservation_step sample_balances
      (parent_action (current_lock_view core endpoint) intent) (core_parent core),
      core_epoch := Suc (core_epoch core)\<rparr>"
  using assms
  by (simp add: sample.execute_finality_client_def sample.finality_step_def sample.invoke_protocol_def
    sample.intent_result_is_actual_parent_step[where balances=sample_balances] Let_def)

definition second_burned_machine :: reservation_machine where
  "second_burned_machine =
    sample.run_reservations sample_balances (sample_prefix 23) (advance_reservation_time 1 sample_credited)"

lemma second_debited_form:
  "debited_authority = with_finality_core ((finality_sample_certified 17)\<lparr>
     core_parent := second_burned_machine, core_epoch := 12, core_published := {(0,17)}\<rparr>) after_cutover"
  unfolding cutover_state_normal_form cutover_reference_state_def second_burned_machine_def sample_prefix_def
  by (simp add: with_finality_core_def with_operational_state_def
    sample_protocol_updates_the_parent_through_its_actual_action finality_sample_current_contexts
    empty_vector_represents_zero_versions Let_def)

lemma native_confirmation_records_the_fresh_terminal:
  assumes "sample.certificate_ok cert" "source_origin_present cert core"
      "statement_status (certificate_statement cert) = Finalized"
      "core_records core (binding_key (statement_binding (certificate_statement cert))) = None"
  defines "binding \<equiv> statement_binding (certificate_statement cert)"
  shows "sample.execute_finality_client (Client_Terminal cert) core =
    (core\<lparr>core_records := (core_records core)(binding_key binding \<mapsto>
       \<lparr>terminal_binding = binding, terminal_kind = Confirmed_Decision, terminal_evidence = [cert]\<rparr>),
       core_epoch := Suc (core_epoch core)\<rparr>, Terminal_Recorded)"
  using assms by (simp add: sample.execute_finality_client_def sample.finality_step_def
    sample.record_terminal_def binding_def Let_def)

abbreviation second_debited_core :: finality_core where
  "second_debited_core \<equiv> credit_core (current_operational debited_authority)"

lemma second_confirmation_is_supported_by_the_new_debit:
  "source_origin_present (sample_certificate 23) second_debited_core"
  "core_records second_debited_core (0,23) = None"
  unfolding second_debited_form
  by (simp_all add: with_finality_core_def with_operational_state_def certified_fixture_has_only_its_first_terminal_record
    source_origin_present_def second_burned_machine_def advance_reservation_time_def sample_credited_state
    sample_confirmed_record_def staged_trace_defs)

lemma second_confirmation_records_the_actual_terminal:
  "sample.execute_finality_client (Client_Terminal (sample_certificate 23)) second_debited_core =
   (second_debited_core\<lparr>core_records := (core_records second_debited_core)((0,23) \<mapsto>
       \<lparr>terminal_binding = sample_binding 23, terminal_kind = Confirmed_Decision,
          terminal_evidence = [sample_certificate 23]\<rparr>),
       core_epoch := Suc (core_epoch second_debited_core)\<rparr>, Terminal_Recorded)"
proof -
  have accepted: "sample.certificate_ok (sample_certificate 23)" by (simp add: sample_fact_accepted)
  have status: "statement_status (certificate_statement (sample_certificate 23)) = Finalized"
    by (simp add: sample_certificate_def sample_statement_def)
  have key: "binding_key (statement_binding (certificate_statement (sample_certificate 23))) = (0,23)"
    by (simp add: sample_certificate_def sample_statement_def sample_binding_def example_binding_def)
  have fresh: "core_records second_debited_core
       (binding_key (statement_binding (certificate_statement (sample_certificate 23)))) = None"
    using second_confirmation_is_supported_by_the_new_debit(2) by (simp only: key)
  show ?thesis using native_confirmation_records_the_fresh_terminal[OF
    accepted second_confirmation_is_supported_by_the_new_debit(1) status fresh]
    by (simp add: sample_certificate_def sample_statement_def sample_binding_def example_binding_def)
qed

schematic_goal second_recorded_form: "recorded_authority = ?state"
  by (simp only: joined_dosp.execute_integrated_client.simps(1)
    [where command="Client_Terminal (sample_certificate 23)" and a=debited_authority]
    credit_preparation.simps if_True
    second_confirmation_records_the_actual_terminal Let_def fst_conv)

definition second_recorded_core :: finality_core where
  "second_recorded_core = credit_core (current_operational recorded_authority)"

lemma second_reference_has_the_recorded_certificate:
  "exact_record_reference second_recorded_core 0 (sample_binding 23) Confirmed_Decision (sample_certificate 23)"
  unfolding second_recorded_core_def second_recorded_form
  by (simp add: exact_record_reference_def record_reference_def with_finality_core_def with_operational_state_def
     sample_binding_def example_binding_def)

lemma a_confirmed_native_credit_publishes_its_evidence:
  assumes "sample.certificate_ok cert" "source_origin_present cert core"
    "binding_operation (statement_binding (certificate_statement cert)) = Destination_Credit"
    "statement_status (certificate_statement cert) \<noteq> Observed"
  shows "sample.publish_source_certificate cert (core_parent core) =
    commit_reservation_event (Certificate_Event cert) (core_parent core)"
  using assms by (simp add: source_origin_present_def sample.publish_source_certificate_def Let_def)

lemma second_certificate_follows_the_native_debit:
  "sample.publish_source_certificate (sample_certificate 23) (core_parent second_recorded_core) =
    commit_reservation_event (Certificate_Event (sample_certificate 23)) (core_parent second_recorded_core)"
proof -
  have source: "source_origin_present (sample_certificate 23) second_debited_core"
    by (rule second_confirmation_is_supported_by_the_new_debit(1))
  have machine: "core_parent second_recorded_core = core_parent second_debited_core"
    unfolding second_recorded_core_def second_recorded_form
    by (simp add: with_finality_core_def with_operational_state_def)
  have accepted: "sample.certificate_ok (sample_certificate 23)" by (simp add: sample_fact_accepted)
  show ?thesis unfolding machine
    by (rule a_confirmed_native_credit_publishes_its_evidence[OF accepted source])
      (simp_all add: sample_certificate_def sample_statement_def sample_binding_def example_binding_def)
qed

lemma second_certification_uses_the_recorded_authority:
  "sample.execute_finality_client (Client_Protocol 0 0 (Certificate_Intent (sample_certificate 23))) second_recorded_core =
    (second_recorded_core\<lparr>core_parent := commit_reservation_event (Certificate_Event (sample_certificate 23))
       (core_parent second_recorded_core), core_epoch := Suc (core_epoch second_recorded_core)\<rparr>, Internal_Completed)"
proof -
  have certified_status: "statement_status (certificate_statement (sample_certificate 23)) = Finalized"
    by (simp add: sample_certificate_def sample_statement_def)
  have certified_binding: "statement_binding (certificate_statement (sample_certificate 23)) = sample_binding 23"
    by (simp add: sample_certificate_def sample_statement_def)
  have certified_kind: "kind_from_source (statement_status (certificate_statement (sample_certificate 23))) =
       Some Confirmed_Decision"
    unfolding certified_status by simp
  have guard: "terminal_intent_guard second_recorded_core 0 (Certificate_Intent (sample_certificate 23))"
    unfolding terminal_intent_guard.simps(1) certified_kind certified_binding
    by (simp add: second_reference_has_the_recorded_certificate)
  show ?thesis
    by (simp add: sample.execute_finality_client_def sample.finality_step_def sample.invoke_protocol_def
      guard second_certificate_follows_the_native_debit Let_def
      del: terminal_intent_guard.simps(1))
qed

schematic_goal prepared_authority_normal_form: "before_second_meter = ?state"
  unfolding before_second_meter_def list.map joined_dosp.run_integrated_events.simps
  by (simp only: joined_dosp.execute_integrated_client.simps(1)
    [where command="Client_Protocol 0 0 (Certificate_Intent (sample_certificate 23))" and a=recorded_authority]
    credit_preparation.simps if_True
    second_recorded_core_def[symmetric] second_certification_uses_the_recorded_authority Let_def fst_conv)

lemma final_authority_runs_the_second_meter:
  "actual_authority = fst (joined_dosp.execute_integrated_client second_meter before_second_meter)"
proof -
  have append:
    "joined_dosp.run_integrated_events (x @ y) a =
     joined_dosp.run_integrated_events y (joined_dosp.run_integrated_events x a)" for x y a
  proof (induction x arbitrary: a)
    case Nil
    then show ?case by simp
  next
    case (Cons event events)
    then show ?case by (cases event) simp_all
  qed
  have cutover:
    "joined_dosp.run_integrated_events cutover_prefix joined_initial = after_cutover"
    unfolding after_cutover_def cutover_prefix_def after_first_meter_def
    by (simp only: list.sel(3) joined_dosp.run_integrated_events.simps(2))
  show ?thesis
    unfolding actual_journal_replays_the_same_asset_program same_asset_events_def
    by (simp only: append cutover before_second_meter_def joined_dosp.run_integrated_events.simps(1,2))
qed

end
