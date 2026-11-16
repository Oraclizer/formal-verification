theory EAB_Adapter_Cases
  imports DOSP_EAB_Coupling.EAB_Lifecycle_Cutover DOSP_EAB_Coupling.EAB_Recovery_Replay
    Evidence_Atomic_Binding.Finality_Scenarios
begin

definition coupling_policy :: "nat flow_policy" where
  "coupling_policy = \<lparr>hub = 1, domain_set = {0, 2}, allowed_sources = {0}\<rparr>"

definition coupling_ticket :: cutover_metadata where
  "coupling_ticket = \<lparr>required_level = Coupled, chosen_path = Atomic,
    meter_version = 3, cutover_epoch = 11\<rparr>"

definition meter_fixture :: metered_source_state where
  "meter_fixture = \<lparr>registered_asset = 17,
    degree_state = \<lparr>route_metadata = coupling_ticket,
      binding_state = \<lparr>committed = (\<lambda>_. 0), observation_cache = (\<lambda>_. 0)\<rparr>,
      billing_history = [], unreconciled_soft_write = False\<rparr>,
    source_authority = \<lparr>terminal_authority = finality_sample_certified 17, publication_slots = (\<lambda>_. None)\<rparr>\<rparr>"

abbreviation fixture_epoch :: nat where
  "fixture_epoch \<equiv> core_epoch (finality_sample_certified 17)"

abbreviation fixture_delivery :: "finality_core \<times> finality_reply" where
  "fixture_delivery \<equiv> sample.invoke_protocol 2 fixture_epoch 0
    (Deliver_Intent Bypass_Route (sample_request 17)) (finality_sample_certified 17)"

abbreviation fixture_native_delivery :: finality_core where
  "fixture_native_delivery \<equiv> sample.finality_step
    (Invoke_Protocol 2 fixture_epoch 0 (Deliver_Intent Bypass_Route (sample_request 17))) (finality_sample_certified 17)"

lemma fixture_binding:
  "request_binding (sample_request 17) = sample_binding 17"
  "binding_key (sample_binding 17) = (0, 17)"
  "binding_asset (sample_binding 17) = 17"
  "binding_destination (sample_binding 17) = 2"
  "binding_operation (sample_binding 17) = Destination_Credit"
  by (simp_all add: sample_request_def sample_binding_def example_binding_def)

lemma actual_fixture_delivery_is_new:
  "snd fixture_delivery = Protocol_Response (Delivery_Response (New_Credit (sample_binding 17)))"
  using normal_bypass_credit_uses_the_terminal_record
  by (simp add: sample.execute_finality_client_def)

lemma active_reservation_blocks_this_promotion:
  "promote_settled_asset coupling_policy {(12, 4)} 12 4 meter_fixture =
    (meter_fixture, transition_result.Rejected Ineligible_Promotion)"
proof (rule a_live_lock_blocks_promotion[where asset = 17 and key = "(0, 17)"])
  show "17 \<in> promotion_assets coupling_policy meter_fixture"
    by (simp add: promotion_assets_def meter_fixture_def)
  show "asset_owner (machine_state (core_parent (credit_core meter_fixture))) 17 = Some (0, 17)"
    using terminal_certificate_publishes_the_actual_parent_evidence[of 17] source_acquire_dispatch_effect_activates
    by (simp add: meter_fixture_def sample.publish_source_certificate_def commit_reservation_event_def Let_def)
qed

lemma stale_ticket_with_the_same_processing_path_still_fails:
  defines "promoted \<equiv> meter_fixture\<lparr>degree_state :=
      (degree_state meter_fixture)\<lparr>route_metadata := promoted_metadata 12 4\<rparr>\<rparr>"
  shows "chosen_path coupling_ticket = chosen_path (route_metadata (degree_state promoted)) \<and>
    sample.meter_source_credit coupling_policy coupling_ticket fixture_epoch 0 50 Bypass_Route
      (sample_request 17) promoted = (promoted, Cutover_Refused Stale_Ticket)"
  by (simp add: promoted_def sample.meter_source_credit_def meter_fixture_def
      fixture_binding coupling_ticket_def promoted_metadata_def Let_def)

definition primary_fixture :: eab_primary_authority where
  "primary_fixture = (source_authority meter_fixture)\<lparr>terminal_authority := fixture_native_delivery\<rparr>"

definition fixture_receipt :: eab_primary_receipt where
  "fixture_receipt = \<lparr>published_key = (0, 17), published_sequence = 50,
    published_binding = sample_binding 17, published_kind = Confirmed_Decision\<rparr>"

abbreviation fixture_publication :: "eab_primary_authority \<times> finality_reply" where
  "fixture_publication \<equiv> sample.publish_at_sequence (0, 17) 50 primary_fixture"

lemma fixture_before_publication:
  "core_records (finality_sample_certified 17) (0, 17) =
      Some \<lparr>terminal_binding = sample_binding 17, terminal_kind = Confirmed_Decision,
        terminal_evidence = [sample_certificate 17]\<rparr>"
  "core_published (finality_sample_certified 17) = {}"
proof -
  show "core_records (finality_sample_certified 17) (0, 17) =
      Some \<lparr>terminal_binding = sample_binding 17, terminal_kind = Confirmed_Decision,
        terminal_evidence = [sample_certificate 17]\<rparr>"
    using terminal_certificate_publishes_the_actual_parent_evidence[of 17]
      actual_source_supports_terminal_record_creation[of 17] by simp
  show "core_published (finality_sample_certified 17) = {}"
    by (simp add: finality_sample_certified_def sample.execute_finality_client_def sample.finality_step_def
        sample.invoke_protocol_def reject_protocol_intent_def finality_recording_is_not_primary_publication Let_def
        split: if_splits)
qed

lemma actual_credit_enables_primary_publication:
  "snd fixture_publication = Primary_Published"
  "publication_slots (fst fixture_publication) 50 = Some (0, 17)"
  "published_transfer_receipt (0, 17) 50 (terminal_authority (fst fixture_publication)) = Some fixture_receipt"
  "core_published (terminal_authority (fst fixture_publication)) = {(0, 17)}"
proof -
  from actual_fixture_delivery_is_new have credited:
    "sample_binding 17 \<in> set (credit_history (received_messages (machine_state (core_parent fixture_native_delivery))))"
    by (auto simp: sample.invoke_protocol_def lift_protocol_result_def sample.deliver_reserved_credit_def
        sample.finality_step_def record_observation_def commit_reservation_event_def record_credit_def Let_def
        split: if_splits message_reply.splits)
  have inputs: "core_records fixture_native_delivery (0, 17) =
      Some \<lparr>terminal_binding = sample_binding 17, terminal_kind = Confirmed_Decision,
        terminal_evidence = [sample_certificate 17]\<rparr>"
    "core_published fixture_native_delivery = {}"
    using fixture_before_publication
    by (simp_all add: sample.finality_step_def sample.invoke_protocol_def reject_protocol_intent_def Let_def
        split: if_splits)
  have effect: "sample.publish_primary (0, 17) fixture_native_delivery =
      (fixture_native_delivery\<lparr>core_published := {(0, 17)}\<rparr>, Primary_Published)"
    using inputs credited by (simp add: sample.publish_primary_def terminal_effect_completed_def fixture_binding Let_def)
  show "snd fixture_publication = Primary_Published"
    and "publication_slots (fst fixture_publication) 50 = Some (0, 17)"
    and "published_transfer_receipt (0, 17) 50 (terminal_authority (fst fixture_publication)) = Some fixture_receipt"
    and "core_published (terminal_authority (fst fixture_publication)) = {(0, 17)}"
    using inputs effect
    by (simp_all add: sample.publish_at_sequence_def sample.finality_step_def primary_fixture_def meter_fixture_def
        published_transfer_receipt_def fixture_receipt_def fixture_binding Let_def)
qed

definition metered_fixture_result :: "metered_source_state \<times> metered_credit_reply" where
  "metered_fixture_result = sample.meter_source_credit coupling_policy coupling_ticket fixture_epoch 0 50
      Bypass_Route (sample_request 17) meter_fixture"

lemma metered_fixture_has_one_current_charge:
  "source_authority (fst metered_fixture_result) = fst fixture_publication"
  "snd metered_fixture_result =
      Credit_Metered (billing_record (prod_encode (0, 17)) coupling_ticket (transfer_commit (sample_binding 17)))"
  "map billing_level (billing_history (degree_state (fst metered_fixture_result))) = [Coupled]"
  "map billing_version (billing_history (degree_state (fst metered_fixture_result))) = [3]"
  "map billing_epoch (billing_history (degree_state (fst metered_fixture_result))) = [11]"
  using actual_credit_enables_primary_publication(1)
  by (simp_all add: metered_fixture_result_def sample.meter_source_credit_def meter_fixture_def
      primary_fixture_def fixture_binding actual_fixture_delivery_is_new fixture_before_publication
      billing_record_def coupling_policy_def coupling_ticket_def can_commit_def Let_def)

lemma credited_binding_is_not_billed_twice:
  "sample.meter_source_credit coupling_policy coupling_ticket fixture_epoch 0 51 Bypass_Route
      (sample_request 17) (fst metered_fixture_result) =
    (fst metered_fixture_result, Cutover_Refused Disallowed_Route)"
  using actual_credit_enables_primary_publication(1)
  by (simp add: metered_fixture_result_def sample.meter_source_credit_def meter_fixture_def
      primary_fixture_def fixture_binding actual_fixture_delivery_is_new fixture_before_publication
      billing_record_def coupling_policy_def coupling_ticket_def can_commit_def Let_def)

lemma occupied_sequence_blocks_delivery_and_metering:
  defines "occupied \<equiv> meter_fixture\<lparr>source_authority :=
      (source_authority meter_fixture)\<lparr>publication_slots := (\<lambda>_. Some (0, 22))\<rparr>\<rparr>"
  shows "sample.meter_source_credit coupling_policy coupling_ticket fixture_epoch 0 50 Bypass_Route
      (sample_request 17) occupied = (occupied, Unavailable_Publication_Sequence)"
  by (simp add: occupied_def sample.meter_source_credit_def meter_fixture_def fixture_binding
      coupling_policy_def coupling_ticket_def can_commit_def Let_def)

definition repair_fixture :: "nat recovery_state" where
  "repair_fixture = \<lparr>active_domains = {2, 4}, route_epoch = 1, primary_record = primary_transfer_value fixture_receipt,
    primary_sequence = 50, source_ready = True, replica = (\<lambda>d. if d = 2 then 0 else primary_transfer_value fixture_receipt),
    work_owner = (\<lambda>job. if job = 8 then Some 2 else None), completion_log = {},
    irreversible_facts = {prod_encode (0, 17)}, rollback_incomplete = False\<rparr>"

lemma repair_fixture_tracks_every_active_divergence:
  "repair_fixture \<in> recovery_carrier"
  by (auto simp: repair_fixture_def pending_ids_def dom_def recovery_carrier_def replica_covered_def split: if_splits)

lemma the_metered_published_transfer_reaches_replica_install:
  "receipt_repair_step {} {} (source_authority (fst metered_fixture_result)) fixture_receipt repair_fixture (Apply_Repair 8 50)
    (transition_result.Accepted (Installed 8 2 50)) (install_replica repair_fixture 8 2)"
  using metered_fixture_has_one_current_charge(1) actual_credit_enables_primary_publication
  by (auto simp: receipt_repair_step_def primary_receipt_matches_def repair_fixture_def fixture_receipt_def
      intro: recovery_step.Ordinary_Repair)

lemma the_same_call_cannot_install_a_different_publication_sequence:
  "receipt_repair_step {} {} (fst fixture_publication) (fixture_receipt\<lparr>published_sequence := 51\<rparr>)
    repair_fixture (Apply_Repair 8 50) (transition_result.Operational_Failure Evidence_Unavailable) repair_fixture"
  by (simp add: receipt_repair_step_def primary_receipt_matches_def repair_fixture_def)

lemma a_missing_publication_slot_blocks_the_same_install:
  "receipt_repair_step {} {} ((fst fixture_publication)\<lparr>publication_slots := (\<lambda>_. None)\<rparr>)
    fixture_receipt repair_fixture (Apply_Repair 8 50) (transition_result.Operational_Failure Evidence_Unavailable) repair_fixture"
  by (simp add: receipt_repair_step_def primary_receipt_matches_def)

end
