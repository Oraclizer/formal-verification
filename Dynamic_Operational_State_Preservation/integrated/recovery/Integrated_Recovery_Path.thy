theory Integrated_Recovery_Path
  imports DOSP_Integrated_Cases.Integrated_Same_Asset
begin

definition issued_second_cycle :: consensus_cycle where
  "issued_second_cycle = \<lparr>consensus_session = (17,7,3), consensus_binding = (0,23),
      consensus_publication_sequence = 51, consensus_commit_second = 86400,
      consensus_route_ticket = promoted_metadata 12 4\<rparr>"

definition issued_second_receipt :: eab_primary_receipt where
  "issued_second_receipt = \<lparr>published_key = (0,23), published_sequence = 51,
     published_binding = sample_binding 23, published_kind = Confirmed_Decision\<rparr>"

abbreviation second_usage :: billing_entry where
  "second_usage \<equiv> billing_record (prod_encode (0,23)) (promoted_metadata 12 4)
     (transfer_commit (sample_binding 23))"

definition second_meter_core :: finality_core where
  "second_meter_core = second_recorded_core\<lparr>
      core_parent := commit_reservation_event (Certificate_Event (sample_certificate 23)) (core_parent second_recorded_core),
      core_epoch := Suc (core_epoch second_recorded_core)\<rparr>"

lemma prepared_second_authority:
  "before_second_meter = with_finality_core second_meter_core cutover_reference_state"
proof -
  have overwrite: "with_finality_core c (with_finality_core d a) = with_finality_core c a" for c d a
    by (simp add: with_finality_core_def with_operational_state_def)
  show ?thesis
    unfolding prepared_authority_normal_form
    unfolding second_meter_core_def[symmetric]
    unfolding second_recorded_form
    unfolding second_debited_form
    by (simp only: cutover_state_normal_form overwrite)
qed

lemma second_meter_operational_fields:
  "credit_core (current_operational before_second_meter) = second_meter_core"
  "registered_asset (current_operational before_second_meter) = 17"
  "route_metadata (degree_state (current_operational before_second_meter)) = promoted_metadata 12 4"
  "billing_history (degree_state (current_operational before_second_meter)) = [fixture_billed_usage]"
  "publication_slots (current_publication_authority before_second_meter) = (\<lambda>_. None)(50 \<mapsto> (0,17))"
  "consensus_now before_second_meter = 86400"
  "next_publication_sequence before_second_meter = 51"
  "committed_cycles (metered_ledger before_second_meter) =
     [successful_cycle (consensus_fixture 86399) fixture_billed_usage]"
  unfolding prepared_second_authority cutover_reference_state_def
  by (simp_all add: with_finality_core_def with_operational_state_def first_metered_operational_fields)

abbreviation second_record :: terminal_record where
  "second_record \<equiv> \<lparr>terminal_binding = sample_binding 23, terminal_kind = Confirmed_Decision,
    terminal_evidence = [sample_certificate 23]\<rparr>"

lemma second_meter_core_fields:
  "core_records second_meter_core = (core_records (finality_sample_certified 17))((0,23) \<mapsto> second_record)"
  "core_published second_meter_core = {(0,17)}"
  "current_lock_view second_meter_core 2 = sample_context ACTIVE"
  "core_parent second_meter_core = commit_reservation_event (Certificate_Event (sample_certificate 23)) second_burned_machine"
  unfolding second_meter_core_def second_recorded_core_def
  unfolding second_recorded_form
  unfolding second_debited_form
  by (simp_all add: with_finality_core_def with_operational_state_def current_lock_view_def
    finality_sample_current_contexts(2)[unfolded current_lock_view_def])

lemma second_request_fields:
  "request_binding (sample_request 23) = sample_binding 23"
  "request_certificate (sample_request 23) = sample_certificate 23"
  "binding_key (sample_binding 23) = (0,23)"
  "binding_asset (sample_binding 23) = 17"
  "binding_destination (sample_binding 23) = 2"
  "binding_operation (sample_binding 23) = Destination_Credit"
  "binding_amount (sample_binding 23) = 5"
  by (simp_all add: sample_request_def sample_binding_def example_binding_def)

definition second_delivered_core :: finality_core where
  "second_delivered_core = second_meter_core\<lparr>
     core_parent := fst (record_observation (sample_request 23) (Delivery_Response (New_Credit (sample_binding 23)))
       (commit_reservation_event (Credit_Event (sample_binding 23)) (core_parent second_meter_core))),
     core_epoch := Suc (core_epoch second_meter_core)\<rparr>"

abbreviation second_delivery_call :: finality_operation where
  "second_delivery_call \<equiv>
    Invoke_Protocol 2 (core_epoch second_meter_core) 0 (Deliver_Intent Bypass_Route (sample_request 23))"

lemma second_native_delivery:
  "snd (sample.core_result second_delivery_call second_meter_core) = Protocol_Response (Delivery_Response (New_Credit (sample_binding 23)))"
  "sample.finality_step second_delivery_call second_meter_core = second_delivered_core"
proof -
  have receive: "snd (sample.published_receive Bypass_Route example_context (sample_request 23)
      (machine_state (core_parent second_meter_core))) = New_Credit (sample_binding 23)"
    unfolding second_meter_core_fields(4) second_burned_machine_def
    by (simp add: sample_credited_state advance_reservation_time_def sample_confirmed_record_def staged_trace_defs)
  have deliver: "sample.deliver_reserved_credit Bypass_Route example_context (sample_request 23)
      (core_parent second_meter_core) =
    record_observation (sample_request 23) (Delivery_Response (New_Credit (sample_binding 23)))
      (commit_reservation_event (Credit_Event (sample_binding 23)) (core_parent second_meter_core))"
    by (simp add: sample.deliver_reserved_credit_def receive)
  have guard: "terminal_intent_guard second_meter_core 0 (Deliver_Intent Bypass_Route (sample_request 23))"
    by (simp add: exact_record_reference_def record_reference_def second_request_fields second_meter_core_fields(1))
  show "snd (sample.core_result second_delivery_call second_meter_core) =
      Protocol_Response (Delivery_Response (New_Credit (sample_binding 23)))"
    "sample.finality_step second_delivery_call second_meter_core = second_delivered_core"
    unfolding sample.finality_step_def second_delivered_core_def
    by (simp_all add: sample.invoke_protocol_def guard second_meter_core_fields(3) sample_context_def deliver
      lift_protocol_result_def record_observation_def Let_def del: terminal_intent_guard.simps(2))
qed

lemma second_delivered_fields:
  "core_published second_delivered_core = {(0,17)}"
  "core_records second_delivered_core (0,23) = Some second_record"
  by (simp_all add: second_delivered_core_def second_meter_core_fields)

definition second_published_authority :: eab_primary_authority where
  "second_published_authority = \<lparr>terminal_authority = second_delivered_core\<lparr>
     core_published := {(0,17),(0,23)}, core_epoch := Suc (core_epoch second_delivered_core)\<rparr>,
     publication_slots = (\<lambda>_. None)(50 \<mapsto> (0,17), 51 \<mapsto> (0,23))\<rparr>"

lemma second_native_publication:
  "sample.publish_at_sequence (0,23) 51 ((current_publication_authority before_second_meter)
       \<lparr>terminal_authority := second_delivered_core\<rparr>) =
     (second_published_authority, Primary_Published)"
proof -
  have effect: "terminal_effect_completed second_delivered_core second_record"
    by (simp add: terminal_effect_completed_def second_delivered_core_def second_request_fields
      record_observation_def commit_reservation_event_def record_credit_def)
  show ?thesis
    apply (simp add: sample.publish_at_sequence_def sample.finality_step_def sample.publish_primary_def
      second_published_authority_def second_meter_operational_fields(5) Let_def
      effect second_delivered_fields)
    apply (rule eab_primary_authority.equality)
    by (simp_all add: insert_commute)
qed

abbreviation pre_meter_operational :: metered_source_state where
  "pre_meter_operational \<equiv> current_operational before_second_meter"

definition second_metered_operational :: metered_source_state where
  "second_metered_operational = pre_meter_operational\<lparr>source_authority := second_published_authority,
      degree_state := (degree_state pre_meter_operational)\<lparr>
        binding_state := fst (evaluate_flow coupling_policy Atomic True (binding_state (degree_state pre_meter_operational))
           (transfer_commit (sample_binding 23))),
        billing_history := billing_history (degree_state pre_meter_operational) @ [second_usage]\<rparr>\<rparr>"

lemma second_meter_is_the_actual_native_credit_and_publication:
  "sample.meter_source_credit coupling_policy (promoted_metadata 12 4) (core_epoch (credit_core pre_meter_operational))
      0 51 Bypass_Route (sample_request 23) pre_meter_operational =
     (second_metered_operational, Credit_Metered second_usage)"
  unfolding second_metered_operational_def
  by (simp add: sample.meter_source_credit_def second_meter_operational_fields second_request_fields
    second_meter_core_fields(2) second_native_delivery(1)[unfolded sample.core_result.simps]
    second_native_delivery(2) second_native_publication
    can_commit_def coupling_policy_def promoted_metadata_def Let_def prod_encode_eq
    fixture_binding coupling_ticket_def billing_record_def)

lemma joined_authority_normal_form:
  "actual_authority = before_second_meter\<lparr>metered_ledger := (metered_ledger before_second_meter)\<lparr>
       operational_state := second_metered_operational,
       committed_cycles := committed_cycles (metered_ledger before_second_meter) @
         [successful_cycle issued_second_cycle second_usage]\<rparr>,
    next_publication_sequence := 52\<rparr>"
proof -
  let ?cycle = "issued_second_cycle"
  let ?ledger = "metered_ledger before_second_meter"
  let ?prior = "set (map billed_consensus (committed_cycles ?ledger))"
  let ?epoch = "core_epoch (credit_core pre_meter_operational)"
  have cycle:
    "\<lparr>consensus_session = (17,7,3), consensus_binding = binding_key (request_binding (sample_request 23)),
       consensus_publication_sequence = next_publication_sequence before_second_meter,
       consensus_commit_second = consensus_now before_second_meter,
       consensus_route_ticket = promoted_metadata 12 4\<rparr> = ?cycle"
    by (simp add: issued_second_cycle_def second_meter_operational_fields second_request_fields)
  have admission_check: "(?cycle \<notin> insert ?cycle ?prior
       \<or> \<not> unique_consensus_cycle (insert ?cycle ?prior) ?cycle
       \<or> consensus_binding ?cycle \<noteq> binding_key (request_binding (sample_request 23))
       \<or> fst (consensus_session ?cycle) \<noteq> binding_asset (request_binding (sample_request 23))) = False"
    by (simp add: unique_consensus_cycle_def second_meter_operational_fields(8) successful_cycle_def
      second_request_fields issued_second_cycle_def consensus_fixture_def)
  have credit: "sample.meter_source_credit coupling_policy (consensus_route_ticket ?cycle) ?epoch
       0 (consensus_publication_sequence ?cycle) Bypass_Route (sample_request 23) pre_meter_operational =
       (second_metered_operational, Credit_Metered second_usage)"
    by (simp only: issued_second_cycle_def consensus_cycle.select_convs second_meter_is_the_actual_native_credit_and_publication)
  have meter: "sample.meter_consensus_cycle coupling_policy (insert ?cycle ?prior) ?cycle ?epoch
       0 Bypass_Route (sample_request 23) ?ledger =
      (?ledger\<lparr>operational_state := second_metered_operational,
        committed_cycles := committed_cycles ?ledger @ [successful_cycle ?cycle second_usage]\<rparr>,
       Some (Credit_Metered second_usage))"
    by (simp only: sample.meter_consensus_cycle_def admission_check if_False Let_def
      credit fst_conv snd_conv metered_credit_reply.case)
  have active: "((17,7,3)::oracle_session_identity) \<noteq> (17,7,3) \<longleftrightarrow> False" by simp
  show ?thesis
    unfolding final_authority_runs_the_second_meter joined_dosp.execute_integrated_client.simps(4) Let_def
    unfolding active if_False
    unfolding cycle
    by (simp only: meter fst_conv snd_conv option.case metered_credit_reply.case second_meter_operational_fields(7); simp)
qed

theorem the_same_asset_was_metered_and_published_on_both_sides_of_promotion:
  "committed_cycles (metered_ledger actual_authority) =
    [successful_cycle (consensus_fixture 86399) fixture_billed_usage, successful_cycle issued_second_cycle second_usage]"
  "issued_receipt actual_authority 50 = Some fixture_receipt"
  "issued_receipt actual_authority 51 = Some issued_second_receipt"
  "core_published (credit_core (current_operational actual_authority)) = {(0,17),(0,23)}"
  "next_publication_sequence actual_authority = 52"
  unfolding joined_authority_normal_form
  by (simp_all add: issued_receipt_def published_transfer_receipt_def fixture_receipt_def issued_second_receipt_def
    second_meter_operational_fields(8)
    second_metered_operational_def second_published_authority_def second_delivered_core_def second_meter_core_fields second_request_fields
    certified_fixture_has_only_its_first_terminal_record fixture_binding Let_def)

lemma the_pre_promotion_ticket_cannot_meter_the_second_credit:
  "joined_dosp.execute_integrated_client
     (Meter_Credit (17,7,3) coupling_ticket 0 Bypass_Route (sample_request 23)) before_second_meter =
     (before_second_meter, Credit_Result (Some (Cutover_Refused Stale_Ticket)))"
  by (simp add: sample.meter_consensus_cycle_def sample.meter_source_credit_def unique_consensus_cycle_def
    second_request_fields second_meter_operational_fields consensus_fixture_def successful_cycle_def
    Let_def coupling_ticket_def promoted_metadata_def)

lemma a_different_session_for_the_same_asset_cannot_meter_the_second_credit:
  "joined_dosp.execute_integrated_client
      (Meter_Credit (17,9,3) (promoted_metadata 12 4) 0 Bypass_Route (sample_request 23)) before_second_meter =
    (before_second_meter, Credit_Result None)"
  by (rule joined_dosp.another_session_cannot_meter) simp

lemma the_two_bills_have_distinct_policy_and_settlement_epochs:
  defines "bills \<equiv> committed_cycles (metered_ledger actual_authority)"
  shows "map (billing_level \<circ> billed_usage) bills = [Coupled,Atomic]"
    and "map (billing_version \<circ> billed_usage) bills = [3,4]"
    and "map (billing_epoch \<circ> billed_usage) bills = [11,12]"
    and "map settlement_day bills = [0,1]"
  unfolding bills_def the_same_asset_was_metered_and_published_on_both_sides_of_promotion(1)
  by (simp_all add: billing_record_def successful_cycle_def issued_second_cycle_def billing_day_def
    consensus_fixture_def coupling_ticket_def promoted_metadata_def)

definition joined_recovery_grants :: "nat routing_grants" where
  "joined_recovery_grants = {(Join_Domain 6 9,2,86400), (Leave_Domain 2 6,3,86400)}"

definition published_recovery_state :: "nat recovery_state" where
  "published_recovery_state =
    (let receipt = the (issued_receipt actual_authority 51);
         payload = primary_transfer_value receipt
     in \<lparr>active_domains = {2,4}, route_epoch = 1,
         primary_record = payload, primary_sequence = published_sequence receipt,
         source_ready = (issued_receipt actual_authority 51 \<noteq> None),
           replica = (\<lambda>_. payload)(6 := Suc payload), work_owner = (\<lambda>_. None),
         completion_log = {}, irreversible_facts = image prod_encode (core_published (credit_core (current_operational actual_authority))),
         rollback_incomplete = False\<rparr>)"

abbreviation stale_replica_value :: nat where
  "stale_replica_value \<equiv> Suc (primary_record published_recovery_state)"

definition noticed_recovery :: "nat recovery_state" where
  "noticed_recovery = published_recovery_state\<lparr>
    replica := (replica published_recovery_state)(2 := stale_replica_value),
    work_owner := (work_owner published_recovery_state)(8 \<mapsto> 2)\<rparr>"

definition joined_recovery :: "nat recovery_state" where
  "joined_recovery = noticed_recovery\<lparr>active_domains := insert 6 (active_domains noticed_recovery), route_epoch := 2,
    work_owner := (work_owner noticed_recovery)(9 \<mapsto> 6)\<rparr>"

definition handed_off_recovery :: "nat recovery_state" where
  "handed_off_recovery = joined_recovery\<lparr>active_domains := active_domains joined_recovery - {2}, route_epoch := 3,
    work_owner := carry_owner 2 6 (work_owner joined_recovery)\<rparr>"

lemmas actual_publication_fields =
  the_same_asset_was_metered_and_published_on_both_sides_of_promotion(2-4)

lemma replay_of_the_metered_journal:
  "joined_dosp.journal.checked_current_replay actual_metering_journal
     (current_source_candidate actual_metering_journal) = Some actual_authority"
  by (simp add: actual_metering_journal_def joined_dosp.journal.generated_source_supplies_recovery_without_a_truth_flag)

lemma this_publication_produces_a_job_that_moves_to_the_new_domain:
  "recovery_step joined_recovery_grants {} published_recovery_state (Notice_Divergence 8 2 stale_replica_value)
     (transition_result.Accepted (Opened 8)) noticed_recovery"
  "recovery_step joined_recovery_grants {} noticed_recovery (Activate (Join_Domain 6 9) 2 86400 86400)
     (transition_result.Accepted (Joined 6 9)) joined_recovery"
  "recovery_step joined_recovery_grants {} joined_recovery (Activate (Leave_Domain 2 6) 3 86400 86400)
     (transition_result.Accepted (Left 2 6)) handed_off_recovery"
  unfolding noticed_recovery_def joined_recovery_def handed_off_recovery_def
  by (rule recovery_step.Detect_Divergence recovery_step.Join_Route recovery_step.Leave_Route;
      simp add: published_recovery_state_def actual_publication_fields joined_recovery_grants_def
      current_grant_def fresh_work_def Let_def)+

theorem the_metered_publication_is_replayed_into_the_same_job_after_handoff:
  "joined_dosp.install_from_current_integrated_replay
     joined_recovery_grants {} actual_metering_journal (current_source_candidate actual_metering_journal) 51
     handed_off_recovery (Apply_Repair 8 51) (transition_result.Accepted (Installed 8 6 51))
     (install_replica handed_off_recovery 8 6)"
proof -
  have slot: "publication_slots (current_publication_authority actual_authority) 51 = Some (0,23)"
    unfolding joined_authority_normal_form
    by (simp add: second_metered_operational_def second_published_authority_def)
  have published: "published_transfer_receipt (0,23) 51 (credit_core (current_operational actual_authority)) =
      Some issued_second_receipt"
    using actual_publication_fields(2) by (simp add: issued_receipt_def slot)
  have selected: "primary_receipt_matches (current_publication_authority actual_authority) issued_second_receipt handed_off_recovery"
    by (simp add: primary_receipt_matches_def published_recovery_state_def slot published
      issued_second_receipt_def handed_off_recovery_def joined_recovery_def noticed_recovery_def
      actual_publication_fields Let_def)
  have installed: "recovery_step joined_recovery_grants {} handed_off_recovery (Apply_Repair 8 51)
      (transition_result.Accepted (Installed 8 6 51)) (install_replica handed_off_recovery 8 6)"
    by (rule recovery_step.Ordinary_Repair)
      (simp_all add: handed_off_recovery_def joined_recovery_def noticed_recovery_def
        published_recovery_state_def actual_publication_fields issued_second_receipt_def carry_owner_def Let_def)
  show ?thesis
    using installed selected
    by (simp add: joined_dosp.install_from_current_integrated_replay_def receipt_repair_step_def
      replay_of_the_metered_journal actual_publication_fields(2))
qed

lemma the_earlier_publication_cannot_drive_this_repair:
  "joined_dosp.install_from_current_integrated_replay
     joined_recovery_grants {} actual_metering_journal (current_source_candidate actual_metering_journal) 50
     handed_off_recovery (Apply_Repair 8 50) (transition_result.Operational_Failure Evidence_Unavailable)
     handed_off_recovery"
  by (simp add: joined_dosp.install_from_current_integrated_replay_def replay_of_the_metered_journal
    actual_publication_fields(1,2) receipt_repair_step_def primary_receipt_matches_def fixture_receipt_def
    handed_off_recovery_def joined_recovery_def noticed_recovery_def published_recovery_state_def
    issued_second_receipt_def Let_def)

lemma the_joined_install_closes_only_its_own_job:
  defines "installed \<equiv> install_replica handed_off_recovery 8 6"
  shows "completion_log installed = {8}" "work_owner installed 8 = None"
    "work_owner installed 9 = Some 6" "replica installed 6 = primary_record handed_off_recovery"
    "irreversible_facts installed = irreversible_facts handed_off_recovery"
  unfolding installed_def by (simp_all add: install_replica_def handed_off_recovery_def joined_recovery_def
    noticed_recovery_def published_recovery_state_def carry_owner_def Let_def)

lemma the_handed_off_install_repairs_a_stale_value:
  "replica (install_replica handed_off_recovery 8 6) 6 \<noteq> replica handed_off_recovery 6"
  "replica (install_replica handed_off_recovery 8 6) 4 = replica handed_off_recovery 4"
  by (simp_all add: install_replica_def handed_off_recovery_def joined_recovery_def
    noticed_recovery_def published_recovery_state_def Let_def)

lemma the_joined_install_cannot_complete_the_job_twice:
  defines "installed \<equiv> install_replica handed_off_recovery 8 6"
  shows "\<not> joined_dosp.install_from_current_integrated_replay
     joined_recovery_grants {} actual_metering_journal (current_source_candidate actual_metering_journal) 51
     installed (Apply_Repair 8 51) (transition_result.Accepted (Installed 8 d 51)) t"
proof
  assume "joined_dosp.install_from_current_integrated_replay
     joined_recovery_grants {} actual_metering_journal (current_source_candidate actual_metering_journal) 51
     installed (Apply_Repair 8 51) (transition_result.Accepted (Installed 8 d 51)) t"
  then have step: "recovery_step joined_recovery_grants {} installed (Apply_Repair 8 51)
      (transition_result.Accepted (Installed 8 d 51)) t"
    by (auto simp: joined_dosp.install_from_current_integrated_replay_def replay_of_the_metered_journal
      actual_publication_fields(2) receipt_repair_step_def split: if_splits)
  from step have "work_owner installed 8 = Some d" by (cases rule: recovery_step.cases) auto
  then show False by (simp add: installed_def install_replica_def)
qed

lemma editing_the_journal_rejects_the_install_from_the_joined_trace:
  defines "candidate \<equiv> (current_source_candidate actual_metering_journal)
      \<lparr>candidate_entries := call_authority_log actual_metering_journal @
        [Authority_Input (Advance_Consensus_Time 86401) (Clock_Result True)]\<rparr>"
  shows "\<not> joined_dosp.install_from_current_integrated_replay
     joined_recovery_grants {} actual_metering_journal candidate 51 handed_off_recovery (Apply_Repair 8 51)
     (transition_result.Accepted (Installed 8 6 51)) t"
  by (rule joined_dosp.a_different_integrated_journal_cannot_install)
    (simp add: candidate_def)

end
