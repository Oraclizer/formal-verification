theory DOSP_Same_Sequence_Cases
  imports DOSP_Source_Defense
begin

abbreviation competing_publication where
  "competing_publication \<equiv> sample.publish_at_sequence (0,17) 51 primary_fixture"

abbreviation competing_receipt where
  "competing_receipt \<equiv> fixture_receipt\<lparr>published_sequence := 51\<rparr>"

lemma the_first_binding_can_be_issued_at_the_same_sequence_by_another_authority:
  "snd competing_publication = Primary_Published"
  "publication_slots (fst competing_publication) 51 = Some (0,17)"
  "published_transfer_receipt (0,17) 51 (terminal_authority (fst competing_publication)) = Some competing_receipt"
proof -
  have effects: "snd competing_publication = snd fixture_publication"
    "terminal_authority (fst competing_publication) = terminal_authority (fst fixture_publication)"
    by (simp_all add: sample.publish_at_sequence_def primary_fixture_def meter_fixture_def Let_def)
  show accepted: "snd competing_publication = Primary_Published"
    using effects(1) actual_credit_enables_primary_publication(1) by simp
  show "publication_slots (fst competing_publication) 51 = Some (0,17)"
    using accepted by (auto simp: sample.publish_at_sequence_def Let_def split: if_splits)
  show "published_transfer_receipt (0,17) 51 (terminal_authority (fst competing_publication)) = Some competing_receipt"
    using actual_credit_enables_primary_publication(3) unfolding effects(2)
    by (auto simp: published_transfer_receipt_def fixture_receipt_def Let_def split: option.splits if_splits)
qed

abbreviation competing_seed where
  "competing_seed \<equiv> joined_initial\<lparr>next_publication_sequence := 51\<rparr>"

definition competing_publisher_journal where
  "competing_publisher_journal =
    joined_dosp.journal.run_calls (integrated_call_program 99 0 [Inl first_meter])
      (initial_call_machine competing_seed)"

abbreviation competing_authority where
  "competing_authority \<equiv> call_authority_state competing_publisher_journal"

lemma competing_journal_receipt:
  "issued_receipt competing_authority 51 = Some competing_receipt"
proof -
  let ?meter = "sample.meter_source_credit coupling_policy coupling_ticket fixture_epoch 0 51
    Bypass_Route (sample_request 17) meter_fixture"
  have raw_credit: "snd (sample.invoke_protocol 2 5 0 (Deliver_Intent Bypass_Route (sample_request 17))
    (finality_sample_certified 17)) = Protocol_Response (Delivery_Response (New_Credit (sample_binding 17)))"
    using actual_fixture_delivery_is_new by (simp only: fixture_epoch_value)
  have metered: "source_authority (fst ?meter) = fst competing_publication"
    "snd ?meter = Credit_Metered fixture_billed_usage"
    using the_first_binding_can_be_issued_at_the_same_sequence_by_another_authority(1)
    by (simp_all add: sample.meter_source_credit_def meter_fixture_def primary_fixture_def
      fixture_binding raw_credit fixture_before_publication
      billing_record_def coupling_policy_def coupling_ticket_def can_commit_def Let_def)
  have ready: "source_call_ready 99 0 (initial_call_machine competing_seed)" by simp
  have executed: "competing_authority = fst (joined_dosp.execute_integrated_client first_meter competing_seed)"
    unfolding competing_publisher_journal_def
    using joined_dosp.integrated_event_program_uses_the_actual_journal_callbacks[OF ready, of "[Inl first_meter]"]
    by (simp only: joined_dosp.run_integrated_events.simps initial_call_machine_def durable_call_machine.select_convs)
  have authority: "current_publication_authority competing_authority = fst competing_publication"
    unfolding executed
    using metered
    by (simp add: sample.meter_consensus_cycle_def joined_initial_def cycle_fixture_def meter_fixture_def
      unique_consensus_cycle_def fixture_binding Let_def)
  show ?thesis
    by (simp add: issued_receipt_def authority the_first_binding_can_be_issued_at_the_same_sequence_by_another_authority(2,3))
qed

lemma competing_journal_replays_its_issued_record:
  "joined_dosp.journal.checked_current_replay competing_publisher_journal
    (current_source_candidate competing_publisher_journal) = Some competing_authority"
  unfolding competing_publisher_journal_def
  by (rule joined_dosp.journal.generated_source_supplies_recovery_without_a_truth_flag)

theorem an_actual_competing_issuer_at_the_same_sequence_cannot_replace_the_current_record:
  fixes sources :: available_journals
  defines "sources \<equiv> Map.empty(41 \<mapsto> competing_publisher_journal,52 \<mapsto> actual_metering_journal)"
  shows "issued_receipt competing_authority 51 = Some competing_receipt"
    "published_key competing_receipt \<noteq> published_key issued_second_receipt"
    "joined_dosp.select_current_publication sources current_repair_head
      [(41,current_source_candidate competing_publisher_journal),live_offer] 3 =
      Some (current_publication_authority actual_authority, issued_second_receipt)"
    "joined_dosp.select_current_publication sources current_repair_head
      [live_offer,(41,current_source_candidate competing_publisher_journal)] 3 =
      Some (current_publication_authority actual_authority, issued_second_receipt)"
    "joined_dosp.select_current_publication (Map.empty(52 \<mapsto> competing_publisher_journal)) current_repair_head
      [(52,current_source_candidate competing_publisher_journal)] 3 = None"
proof -
  show "issued_receipt competing_authority 51 = Some competing_receipt" by (rule competing_journal_receipt)
  show "published_key competing_receipt \<noteq> published_key issued_second_receipt"
    by (simp add: fixture_receipt_def issued_second_receipt_def)
  show "joined_dosp.select_current_publication sources current_repair_head
      [(41,current_source_candidate competing_publisher_journal),live_offer] 3 =
      Some (current_publication_authority actual_authority, issued_second_receipt)"
    "joined_dosp.select_current_publication sources current_repair_head
      [live_offer,(41,current_source_candidate competing_publisher_journal)] 3 =
      Some (current_publication_authority actual_authority, issued_second_receipt)"
    "joined_dosp.select_current_publication (Map.empty(52 \<mapsto> competing_publisher_journal)) current_repair_head
      [(52,current_source_candidate competing_publisher_journal)] 3 = None"
    by (simp_all add: sources_def joined_dosp.select_current_publication_def current_repair_head_def competing_journal_replays_its_issued_record
      competing_journal_receipt fixture_receipt_def issued_second_receipt_def replay_of_the_metered_journal
      actual_publication_fields(2) Let_def)
qed

end
