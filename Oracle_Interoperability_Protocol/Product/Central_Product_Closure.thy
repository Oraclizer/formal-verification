theory Central_Product_Closure
  imports "Checks/Promotion_Evidence"
begin

context source_attestation
begin

theorem actual_product_authority_is_the_replay_of_its_recorded_public_execution:
  fixes execute :: "authority_connection \<Rightarrow> 'token retained_service_action \<Rightarrow> retained_product \<Rightarrow> retained_product \<times> scheduled_service_reply"
    and directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    and balances regulatory contexts durable target provider actions
    and initial current :: retained_product
    and records :: retained_call_source
    and genesis :: finality_core
  defines "execute \<equiv> schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack"
    and "initial \<equiv> initial_promotable_product balances regulatory contexts durable target provider"
    and "current \<equiv> run_product_action_word execute actions initial"
    and "records \<equiv> retained_source current"
    and "genesis \<equiv> initial_finality_core balances regulatory contexts"
  shows "retained_genesis records = genesis"
    "finality_calls.authentic_call_history (retained_log records) genesis"
    "retained_core records = run_finality (call_operations (retained_log records) genesis) genesis"
    "reservation_contract balances (core_parent (retained_core records))"
    "distinct (authority_execution_ids (retained_log records))"
    "capture_retained_product (reopen_retained_product connection current) = current"
proof -
  have init: "retained_source_replay_valid initial"
    unfolding initial_def by (rule canonical_product_initialization_supplies_the_actual_public_genesis(1))
  have trace: "retained_source_replay_valid current \<and>
      retained_genesis records = retained_genesis (retained_source initial)"
    unfolding current_def records_def execute_def
    by (rule every_product_word_keeps_its_actual_genesis_and_authority_replay[OF init])
  show gen: "retained_genesis records = genesis"
    using trace unfolding initial_def genesis_def
    by (simp add: canonical_product_initialization_supplies_the_actual_public_genesis(2))
  have from_recorded_genesis: "retained_core records =
      finality_calls.replay_call_authority (retained_log records) (retained_genesis records) \<and>
    finality_calls.authentic_call_history (retained_log records) (retained_genesis records)"
    using trace[THEN conjunct1]
    by (simp add: retained_source_replay_valid_def reopen_retained_source_def finality_calls.authority_replay_contract_def records_def)
  note replay = from_recorded_genesis[unfolded gen]
  show "finality_calls.authentic_call_history (retained_log records) genesis" by (rule replay[THEN conjunct2])
  have core: "retained_core records = run_finality (call_operations (retained_log records) genesis) genesis"
    using replay[THEN conjunct1] unfolding call_replay_is_actual_finality_run .
  then show "retained_core records = run_finality (call_operations (retained_log records) genesis) genesis" .
  show "reservation_contract balances (core_parent (retained_core records))"
    unfolding core genesis_def by (rule finality_supplies_actual_reservation_contract)
  have ids: "retained_call_ids_exact initial"
    unfolding initial_def by (rule initialized_product_has_exact_retained_call_ids)
  show "distinct (authority_execution_ids (retained_log records))"
    unfolding records_def current_def execute_def
    by (rule every_actual_product_trace_executes_each_authoritative_call_id_at_most_once[OF ids])
  show "capture_retained_product (reopen_retained_product connection current) = current"
    by (rule product_round_trip_preserves_the_durable_projection)
qed

lemma scheduled_reopen_has_the_same_reply_and_retained_effect:
  fixes current :: retained_product
  shows "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection action (capture_retained_product (reopen_retained_product previous current)) =
   schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection action current"
  using product_round_trip_preserves_the_durable_projection[of previous current] by simp

lemma wire_success_has_one_canonical_origin_and_the_selected_scheduled_action:
  fixes selected :: "wire_core \<Rightarrow> 'token retained_service_action option"
    and directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack connection
  defines "execute \<equiv> schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack connection"
  assumes accepted: "consume_wire_in_current_product verify_signature source_verified body_allowed scope selected execute bytes dedup before =
    (after_dedup, after, Some reply)"
  obtains packet action where "decode_wire_packet bytes = Some packet"
    "encode_wire_packet packet = bytes"
    "current_wire_scope scope (packet_core packet)"
    "selected (packet_core packet) = Some action"
    "execute action before = (after, reply)"
proof -
  obtain packet action where gate: "wire_gate verify_signature source_verified body_allowed scope bytes = Gate_Admitted packet"
    and selected: "selected (packet_core packet) = Some action" and result: "execute action before = (after, reply)"
    using the_actual_product_receiver_gets_only_the_action_decoded_from_the_verified_core[OF accepted] by blast
  have decoded: "decode_wire_packet bytes = Some packet" and scoped: "current_wire_scope scope (packet_core packet)"
    using a_wire_admission_uses_the_exact_current_domain_key_epoch_and_signature[OF gate] by blast+
  have encoded: "encode_wire_packet packet = bytes"
    by (rule every_accepted_wire_message_has_exactly_the_received_bytes[OF decoded, THEN conjunct1])
  show thesis by (rule that[OF decoded encoded scoped selected result])
qed

definition clock_observation_operation where
  "clock_observation_operation available expected actual session_bound clock_granted time_verified revision_room endpoint now core =
    (let old = reservation_clock (machine_state (core_parent core)) in
      if available \<and> expected = actual \<and> session_bound \<and> clock_granted \<and>
        time_verified \<and> revision_room \<and> old \<le> now
      then Some (Invoke_Protocol endpoint (core_epoch core) 0 (Time_Intent (now - old)))
      else None)"

lemma an_admitted_clock_observation_is_the_exact_public_time_operation:
  assumes selected: "clock_observation_operation available expected actual session_bound clock_granted
    time_verified revision_room endpoint now core = Some operation"
  shows "reservation_clock (machine_state (core_parent (finality_step operation core))) = now"
    "unresolved_source_obligations (machine_state (core_parent (finality_step operation core))) =
       unresolved_source_obligations (machine_state (core_parent core))"
    "source_units (machine_state (core_parent (finality_step operation core))) =
       source_units (machine_state (core_parent core))"
    "destination_units (machine_state (core_parent (finality_step operation core))) =
       destination_units (machine_state (core_parent core))"
    "core_records (finality_step operation core) = core_records core"
proof -
  let ?old = "reservation_clock (machine_state (core_parent core))"
  let ?elapsed = "now - ?old"
  have op: "operation = Invoke_Protocol endpoint (core_epoch core) 0 (Time_Intent ?elapsed)"
    and le: "?old \<le> now"
    using selected by (auto simp: clock_observation_operation_def Let_def split: if_splits)
  have effect: "core_parent (finality_step operation core) = advance_reservation_time ?elapsed (core_parent core)"
    by (simp add: op finality_step_def invoke_protocol_def Let_def)
  show "reservation_clock (machine_state (core_parent (finality_step operation core))) = now"
    unfolding effect using le by (simp add: advance_reservation_time_def commit_reservation_event_def)
  note frame = actual_finality_timeout_preserves_pending_and_balances[of endpoint core 0 ?elapsed,
    unfolded Let_def op[symmetric]]
  show "unresolved_source_obligations (machine_state (core_parent (finality_step operation core))) =
       unresolved_source_obligations (machine_state (core_parent core))"
    using frame by blast
  show "source_units (machine_state (core_parent (finality_step operation core))) =
       source_units (machine_state (core_parent core))"
    using frame by blast
  show "destination_units (machine_state (core_parent (finality_step operation core))) =
       destination_units (machine_state (core_parent core))"
    using frame by blast
  show "core_records (finality_step operation core) = core_records core"
    using frame by blast
qed

lemma clock_observation_rejects_a_stale_cut_or_unverified_time:
  assumes "expected \<noteq> actual \<or> \<not> time_verified"
  shows "clock_observation_operation available expected actual session_bound clock_granted time_verified
    revision_room endpoint now core = None"
  using assms by (auto simp: clock_observation_operation_def)

thm_oracles actual_product_authority_is_the_replay_of_its_recorded_public_execution
  scheduled_reopen_has_the_same_reply_and_retained_effect
  wire_success_has_one_canonical_origin_and_the_selected_scheduled_action
  an_admitted_clock_observation_is_the_exact_public_time_operation

ML \<open>
  val _ =
    if null (Thm_Deps.all_oracles @{thms
      actual_product_authority_is_the_replay_of_its_recorded_public_execution
      scheduled_reopen_has_the_same_reply_and_retained_effect
      wire_success_has_one_canonical_origin_and_the_selected_scheduled_action
      an_admitted_clock_observation_is_the_exact_public_time_operation})
    then ()
    else error "Central product closure depends on an oracle"
\<close>

end

end
