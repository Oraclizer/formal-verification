theory Reference_Write_Capacity
  imports "OIP_Reference_Write_Core_Seed.Reference_Write_Core_Seed"
begin

definition write_u64_max :: nat where
  "write_u64_max = 18446744073709551615"

lemma write_u64_max_succ: "Suc write_u64_max = 2 ^ 64"
  by code_simp

definition write_capacity_command :: client_command where
  "write_capacity_command = Client_Protocol 0 0 (Write_Intent (sample_request 17) 0 [(17,write_u64_max)] 9)"

definition write_capacity_payload :: product_call_payload where
  "write_capacity_payload = write_fixture_payload\<lparr>payload_envelope := lock_example_envelope write_capacity_command\<rparr>"

definition write_capacity_core :: wire_core where
  "write_capacity_core =
    (let body = wire_operation_body write_fixture_core
     in write_fixture_core\<lparr>wire_operation_body := body\<lparr>wire_words := (wire_words body)[20 := write_u64_max]\<rparr>\<rparr>)"

definition write_capacity_other_uuid :: wire_core where
  "write_capacity_other_uuid = write_capacity_core\<lparr>wire_uuid := (wire_uuid write_capacity_core)[0 := 13]\<rparr>"

lemma capacity_core_selects_the_max_version:
  "select_reference_write (\<lambda>_. Some (sample_request 17)) write_capacity_core =
    Some ((7,1),write_capacity_payload)"
  "select_reference_write (\<lambda>_. Some (sample_request 17)) write_capacity_other_uuid =
    Some ((7,1),write_capacity_payload)"
  by code_simp+

lemma capacity_cores_are_wellformed:
  "wire_core_wellformed write_capacity_core"
  "wire_core_wellformed write_capacity_other_uuid"
proof -
  have body: "wire_body_wellformed (wire_operation_body write_capacity_core)"
    by (simp add: wire_body_wellformed_def body_fields_def write_capacity_core_def write_fixture_core_def
        write_u64_max_def wire_octets_def Let_def)
  have octets: "wire_octets (encode_wire_body (wire_operation_body write_capacity_core))"
    unfolding encode_wire_body_def
    by (rule encoded_wire_fields_are_octets) (use body in \<open>simp add: wire_body_wellformed_def\<close>)
  show "wire_core_wellformed write_capacity_core" "wire_core_wellformed write_capacity_other_uuid"
    using body octets
    by (simp_all add: wire_core_wellformed_def core_fields_def secondary_field_def wire_octets_def
        write_capacity_other_uuid_def write_capacity_core_def write_fixture_core_def Let_def)
qed

lemma capacity_cores_are_canonical:
  "decode_wire_core (encode_wire_core write_capacity_core) = Some write_capacity_core"
  "decode_wire_core (encode_wire_core write_capacity_other_uuid) = Some write_capacity_other_uuid"
  "code_check_operation reference_accepts_write write_capacity_core = None"
proof -
  show "decode_wire_core (encode_wire_core write_capacity_core) = Some write_capacity_core"
    by (rule wellformed_canonical_core_has_a_two_way_encoding[OF capacity_cores_are_wellformed(1)])
  show "decode_wire_core (encode_wire_core write_capacity_other_uuid) = Some write_capacity_other_uuid"
    by (rule wellformed_canonical_core_has_a_two_way_encoding[OF capacity_cores_are_wellformed(2)])
  show "code_check_operation reference_accepts_write write_capacity_core = None"
    by (rule the_new_profile_accepts_the_existing_write_layout(2))
      (simp_all add: write_capacity_core_def write_fixture_core_def Let_def)
qed

lemma capacity_core_uuid_change_uses_a_different_transport_key:
  "authenticated_wire_message_id write_capacity_other_uuid \<noteq> authenticated_wire_message_id write_capacity_core"
  by (simp add: authenticated_wire_message_id_def write_capacity_other_uuid_def
      write_capacity_core_def write_fixture_core_def Let_def)

lemma capacity_blocks_write_readiness:
  assumes command: "envelope_command (payload_envelope payload) =
    Client_Protocol endpoint index (Write_Intent request generation versions value)"
    and full: "asset_version (authoritative_reservation_state source) (binding_asset (request_binding request)) = write_u64_max
       \<or> cut_revision (write_ledger_cut before) = write_u64_max"
  shows "\<not> reference_write_ready registered actor call_id payload source before"
  using full by (elim disjE; simp add: reference_write_ready_def command write_u64_max_def Let_def)

context source_attestation
begin

lemma a_fresh_write_at_capacity_records_a_refusal:
  assumes connected: "call_connection (product_calls (write_source connection before)) = Authority_Connected"
    and current: "envelope_cut (payload_envelope payload) = write_ledger_cut before"
    and command: "envelope_command (payload_envelope payload) =
      Client_Protocol endpoint index (Write_Intent request generation versions value)"
    and full: "asset_version (authoritative_reservation_state (write_source connection before))
        (binding_asset (request_binding request)) = write_u64_max
      \<or> cut_revision (write_ledger_cut before) = write_u64_max"
  shows "reference_write_fresh registered connection actor call_id payload before =
    record_reference_write call_id payload Authority_Rejected (None :: product_world option) before"
  using capacity_blocks_write_readiness[OF command full] connected current
  by (simp add: reference_write_fresh_def Let_def)

lemma a_reopened_rejected_write_collects_the_retained_refusal:
  assumes recorded: "retained_outcomes (reference_product (write_authority before)) call_id =
      Some \<lparr>result_payload = payload, result_outcome = Authority_Rejected\<rparr>"
    and position: "write_effect_positions before call_id = None"
    and bound: "result_access_bound verified actor call_id payload
      (current_product_outcomes (reopen_retained_product connection (reference_product (write_authority before))))"
    and command: "envelope_command (payload_envelope payload) =
      Client_Protocol endpoint index (Write_Intent request generation versions value)"
  shows "collect_reference_write verified connection actor call_id payload before = Some (Authority_Rejected,None)"
  using recorded position bound command
  by (simp add: collect_reference_write_def observe_collection_def result_completion_ready_def Let_def
      reopening_the_write_authority_restores_the_exact_result_table reopened_write_outcomes_are_available_to_the_endpoint)

end

definition write_capacity_machine where
  "write_capacity_machine = (let state = machine_state lock_example_held in
    lock_example_held\<lparr>machine_state := state\<lparr>asset_version := (asset_version state)(17 := write_u64_max)\<rparr>\<rparr>)"

definition write_capacity_world where
  "write_capacity_world = lock_example_world write_capacity_machine"

definition write_capacity_store :: "unit reference_write_store" where
  "write_capacity_store =
    (let base = write_fixture_store (sample_source_context ACTIVE);
         authority = write_authority base; records = reference_product authority;
         next = authority\<lparr>reference_product := records\<lparr>retained_source := capture_retained_source write_capacity_world\<rparr>\<rparr>
     in base\<lparr>write_product_image := (write_product_image base)\<lparr>image_authority := next,
       image_read_history := initialize_reference_history 9 (capture_reference_view next)\<rparr>\<rparr>)"

lemma write_capacity_fixture_source:
  "write_source Authority_Connected write_capacity_store = write_capacity_world"
  by (simp add: write_capacity_store_def write_fixture_projection(1) write_capacity_world_def lock_example_world_def
      reference_lock_source_def recovery_projection_supplies_the_exact_source
      capture_retained_source_def reopen_retained_source_def initial_call_machine_def Let_def)

lemma write_capacity_fixture_lock_admitted:
  "lock_envelope_admitted 7 (payload_envelope write_capacity_payload) (payload_credential write_capacity_payload) write_capacity_world"
  by (simp add: write_capacity_payload_def write_fixture_payload_def write_capacity_command_def write_capacity_world_def
      write_capacity_machine_def lock_example_world_def lock_example_core_def lock_example_envelope_def
      lock_example_token_def initial_call_machine_def lock_envelope_admitted_def envelope_matches_request_def
      envelope_matches_binding_def lock_credential_matches_def authoritative_lock_view_def authoritative_lock_token_def
      authoritative_reservation_state_def product_lock_admitted_def current_lock_token_def current_product_cut_def
      lock_example_public_defs)

abbreviation write_capacity_unbounded_effect where
  "write_capacity_unbounded_effect \<equiv> write_asset_data (sample_source_context ACTIVE) (sample_request 17) 0
    (vector_lookup [(17,write_u64_max)]) 9 write_capacity_machine"

lemma without_the_capacity_check_the_fixture_reaches_the_unbounded_write:
  "snd write_capacity_unbounded_effect = Data_Updated"
  by (simp add: successful_write_guard write_capacity_machine_def vector_lookup_def lock_example_public_defs)

lemma the_unbounded_write_exceeds_the_asset_counter_range:
  "asset_value (machine_state (fst write_capacity_unbounded_effect)) 17 = 9"
  "asset_version (machine_state (fst write_capacity_unbounded_effect)) 17 = 2 ^ 64"
  using successful_write_value_and_version[OF without_the_capacity_check_the_fixture_reaches_the_unbounded_write]
  by (simp_all add: write_canary_primary_asset write_capacity_machine_def write_u64_max_succ Let_def)

abbreviation run_write_capacity_fixture where
  "run_write_capacity_fixture \<equiv> sample.reference_write_fresh {0,2} Authority_Connected 7 (7,1)
    write_capacity_payload write_capacity_store"

lemma the_capacity_fixture_records_the_exact_refusal:
  "run_write_capacity_fixture =
    record_reference_write (7,1) write_capacity_payload Authority_Rejected (None :: product_world option) write_capacity_store"
proof (rule sample.a_fresh_write_at_capacity_records_a_refusal)
  show "call_connection (product_calls (write_source Authority_Connected write_capacity_store)) = Authority_Connected"
    by (simp add: write_capacity_fixture_source write_capacity_world_def lock_example_world_def initial_call_machine_def)
  show "envelope_cut (payload_envelope write_capacity_payload) = write_ledger_cut write_capacity_store"
    by (simp add: write_capacity_payload_def lock_example_envelope_def write_capacity_store_def
        initialize_reference_history_def reference_observed_cut_def Let_def)
  show "envelope_command (payload_envelope write_capacity_payload) =
    Client_Protocol 0 0 (Write_Intent (sample_request 17) 0 [(17,write_u64_max)] 9)"
    by (simp add: write_capacity_payload_def lock_example_envelope_def write_capacity_command_def)
  show "asset_version (authoritative_reservation_state (write_source Authority_Connected write_capacity_store))
        (binding_asset (request_binding (sample_request 17))) = write_u64_max
      \<or> cut_revision (write_ledger_cut write_capacity_store) = write_u64_max"
    by (simp add: write_capacity_fixture_source write_canary_primary_asset write_capacity_world_def
        lock_example_world_def lock_example_core_def initial_call_machine_def authoritative_reservation_state_def
        write_capacity_machine_def Let_def)
qed

lemma the_capacity_fixture_observes_the_initial_view:
  "observe_write_fixture run_write_capacity_fixture = (Some (1,None),0,write_u64_max,0)"
  unfolding the_capacity_fixture_records_the_exact_refusal observe_write_fixture_def Let_def
  unfolding recording_a_write_without_effect_keeps_the_exact_authority_view(1,3)
  by (simp add: write_capacity_store_def initialize_reference_history_def reference_observed_cut_def
      capture_reference_view_def capture_snapshot_def capture_retained_source_def write_capacity_world_def
      lock_example_world_def lock_example_core_def initial_call_machine_def write_capacity_machine_def lock_example_public_defs)

section \<open>Selected history and reachable asset versions\<close>

lemma a_selected_cut_has_a_representable_successor:
  fixes prefix_count revision word_max :: nat
  assumes "prefix_count = Suc revision" "prefix_count \<le> word_max"
  shows "revision < word_max"
  using assms by arith

lemma advancing_a_physically_bounded_history_does_not_wrap_its_length:
  fixes prefix_count revision word_max :: nat
  assumes "prefix_count = Suc revision" "prefix_count < word_max"
  shows "Suc (Suc revision) \<le> word_max"
  using assms by arith

inductive write_counter_history :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  genesis: "write_counter_history 0 0"
| other_step: "write_counter_history version revision \<Longrightarrow> write_counter_history version (revision + steps)"
| asset_step: "write_counter_history version revision \<Longrightarrow> write_counter_history (Suc version) (Suc revision)"

lemma a_reachable_asset_version_is_bounded_by_its_revision:
  "write_counter_history version revision \<Longrightarrow> version \<le> revision"
  by (induction rule: write_counter_history.induct) (auto intro: trans_le_add1)

lemma a_reachable_selected_version_is_below_u64_max:
  assumes "write_counter_history version revision"
    "prefix_count = Suc revision" "prefix_count \<le> word_max" "word_max \<le> write_u64_max"
  shows "version < write_u64_max"
  using a_reachable_asset_version_is_bounded_by_its_revision[OF assms(1)]
    a_selected_cut_has_a_representable_successor[OF assms(2,3)] assms(4) by arith

definition write_capacity_integer_cores :: "integer list list" where
  "write_capacity_integer_cores =
    map (map integer_of_nat \<circ> encode_wire_core) [write_capacity_core,write_capacity_other_uuid]"

definition write_capacity_observation :: "integer list" where
  "write_capacity_observation = (let (result, value, version, revision) = observe_write_fixture run_write_capacity_fixture in
    case result of Some (code,None) \<Rightarrow> map integer_of_nat [1,code,0,0,value,version,revision] | _ \<Rightarrow> [])"

declare [[code drop: write_capacity_observation]]

lemma write_capacity_observation_exact [code]:
  "write_capacity_observation = [1,1,0,0,0,18446744073709551615,0]"
  unfolding write_capacity_observation_def the_capacity_fixture_observes_the_initial_view
  by (simp add: write_u64_max_def integer_of_nat_eq_of_nat)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms capacity_core_selects_the_max_version capacity_cores_are_canonical
      capacity_core_uuid_change_uses_a_different_transport_key
      source_attestation.a_fresh_write_at_capacity_records_a_refusal
      source_attestation.a_reopened_rejected_write_collects_the_retained_refusal
      write_capacity_fixture_lock_admitted the_unbounded_write_exceeds_the_asset_counter_range
      the_capacity_fixture_observes_the_initial_view advancing_a_physically_bounded_history_does_not_wrap_its_length
      a_reachable_selected_version_is_below_u64_max write_capacity_observation_exact})
  then () else error "Unexpected oracle in the reference Write capacity proofs"
\<close>

export_code write_capacity_integer_cores write_capacity_observation
  in SML module_name Reference_Write_Capacity file_prefix "reference_write_capacity"

end
