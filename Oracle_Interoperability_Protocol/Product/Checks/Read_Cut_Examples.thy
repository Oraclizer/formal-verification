theory Read_Cut_Examples
  imports "../Read_Program" "OIP_Product_Base.Lock_Endpoint_Examples"
begin

definition read_example_query where "read_example_query = Application_Value 17"

definition read_example_before where
  "read_example_before = initial_product_reads 100 (initial_settlement_world 99
     (initial_origin_world (lock_example_world sample_initial)))"

definition read_example_reserve where
  "read_example_reserve = Client_Protocol 0 0 (Reserve_Intent (sample_request 17) [] 10)"

definition read_example_write where
  "read_example_write = Client_Protocol 0 0 (Write_Intent (sample_request 17) 0 [] 9)"

definition read_example_release where
  "read_example_release = Client_Protocol 0 0 (Cancel_Intent (sample_request 17) 0 [(17,1)])"

definition read_example_write_calls where
  "read_example_write_calls = sample.finality_calls.run_calls
    [Begin_Call (7,1) read_example_reserve, Dispatch_Call (7,1) read_example_reserve,
     Begin_Call (7,2) read_example_write, Dispatch_Call (7,2) read_example_write,
     Begin_Call (7,3) read_example_release, Dispatch_Call (7,3) read_example_release]
    (initial_call_machine (lock_example_core sample_initial))"

definition read_example_released_core where
  "read_example_released_core = fst (sample.execute_finality_client read_example_release
     (fst (sample.execute_finality_client read_example_write
       (fst (sample.execute_finality_client read_example_reserve (lock_example_core sample_initial))))))"

definition read_example_cached where
  "read_example_cached = sample.capture_product_cache (\<lambda>_ _ _. True) 7 1 read_example_query read_example_before"

definition read_example_after where
  "read_example_after = read_example_cached\<lparr>read_authority :=
    (let s = read_authority read_example_before; old = origin_outcomes (settlement_primary s)
     in update_settlement_outcomes (old\<lparr>outcome_source := (outcome_source old)\<lparr>product_calls := read_example_write_calls\<rparr>\<rparr>) s)\<rparr>"

abbreviation old_read_cut :: product_cut where
  "old_read_cut \<equiv> \<lparr>cut_authority_epoch = 9, cut_revision = 0\<rparr>"

abbreviation new_read_cut :: product_cut where
  "new_read_cut \<equiv> \<lparr>cut_authority_epoch = 9, cut_revision = 3\<rparr>"

lemmas read_example_state_defs = read_example_before_def initial_product_reads_def initial_settlement_world_def
  initial_origin_world_def initial_outcome_world_def lock_example_world_def
  observed_product_source_def observed_product_cut_def authoritative_read_core_def exact_calls_def outcome_calls_def
  current_product_cut_def initial_call_machine_def read_asset_registered_def

lemma old_read_example_has_value_zero:
  "stored_query read_example_query (capture_snapshot (lock_example_core sample_initial)) = Units_Value 0"
  by (simp add: read_example_query_def capture_snapshot_def lock_example_core_def lock_example_public_defs)

lemma cached_value_is_bound_to_revision_zero:
  "query_cache read_example_cached read_example_query = Some
    \<lparr>cached_query = read_example_query, cached_provider = 100, cached_cut = old_read_cut, cached_value = Units_Value 0\<rparr>"
  by (simp add: read_example_cached_def sample.capture_product_cache_def read_example_state_defs
    read_access_bound_def read_authority_available_def sample.authority_prefix_snapshot_def sample.authority_prefix_core_def
    old_read_example_has_value_zero snapshot_query_ready_def read_example_query_def capture_snapshot_def
    lock_example_core_def initial_finality_core_def lock_example_public_defs Let_def)

lemma held_application_value_is_not_visible_at_its_cut:
  "read_current_product (\<lambda>_ _ _. True) 7 1 read_example_query old_read_cut
    (initial_product_reads 100 (initial_settlement_world 99 (initial_origin_world (lock_example_world lock_example_held)))) =
    Product_Read_Busy"
  by (simp add: read_current_product_def read_example_state_defs read_access_bound_def read_authority_available_def
    snapshot_query_ready_def read_example_query_def capture_snapshot_def lock_example_core_def
    initial_finality_core_def lock_example_public_defs Let_def)

lemma read_example_write_call_fields:
  "call_authority_state read_example_write_calls = read_example_released_core"
  "length (call_authority_log read_example_write_calls) = 3"
  "call_local_status read_example_write_calls = Endpoint_Up"
  "call_connection read_example_write_calls = Authority_Connected"
  "call_genesis read_example_write_calls = lock_example_core sample_initial"
  by (simp_all add: read_example_write_calls_def read_example_released_core_def initial_call_machine_def
      sample.finality_calls.call_definitions Let_def)

lemma actual_authority_write_replaces_value_zero_with_nine:
  "stored_query read_example_query (capture_snapshot (call_authority_state read_example_write_calls)) = Units_Value 9"
  "snapshot_query_ready read_example_query (capture_snapshot (call_authority_state read_example_write_calls))"
  unfolding read_example_write_call_fields(1)
  by (simp_all add: read_example_released_core_def read_example_reserve_def read_example_write_def read_example_release_def
      sample.execute_finality_client_def sample.finality_step_def sample.invoke_protocol_def lift_protocol_result_def
      capture_snapshot_def current_lock_view_def lock_example_core_def initial_finality_core_def lock_example_contexts_def
      lock_example_public_defs write_asset_data_def cancel_before_dispatch_def vector_lookup_def read_example_query_def snapshot_query_ready_def)

lemma current_read_example_projects_actual_authority:
  "observed_product_cut (read_authority read_example_after) = new_read_cut"
  "authoritative_read_core (read_authority read_example_after) = call_authority_state read_example_write_calls"
  "read_access_bound (\<lambda>_ _ _. True) kind 7 1 read_example_query read_example_after"
  "read_authority_available read_example_after"
  "read_asset_registered read_example_query read_example_after"
  by (simp_all add: read_example_after_def update_settlement_outcomes_def read_example_state_defs
      read_access_bound_def read_authority_available_def read_example_query_def
      read_example_write_call_fields(2,3,4) Let_def)

lemma after_write_the_cache_is_still_at_revision_zero:
  "query_cache read_example_after read_example_query = Some
    \<lparr>cached_query = read_example_query, cached_provider = 100, cached_cut = old_read_cut, cached_value = Units_Value 0\<rparr>"
  by (simp add: read_example_after_def cached_value_is_bound_to_revision_zero)

lemma after_write_the_provider_is_still_the_same:
  "read_provider read_example_after = 100"
  by (simp add: read_example_after_def read_example_cached_def sample.capture_product_cache_def
    read_example_before_def initial_product_reads_def Let_def split: option.splits if_splits)

lemma stale_cache_returns_busy_and_direct_current_read_returns_nine:
  "read_current_product (\<lambda>_ _ _. True) 7 1 read_example_query new_read_cut read_example_after = Product_Read_Busy"
  "read_current_product (\<lambda>_ _ _. True) 7 1 read_example_query new_read_cut
    (read_example_after\<lparr>query_cache := (\<lambda>_. None)\<rparr>) = Current_Cut_Value new_read_cut (Units_Value 9)"
proof -
  let ?entry = "\<lparr>cached_query = read_example_query, cached_provider = 100, cached_cut = old_read_cut, cached_value = Units_Value 0\<rparr>"
  have stale: "\<not> cache_is_current_for ?entry read_example_query read_example_after"
    by (simp add: cache_is_current_for_def current_read_example_projects_actual_authority(1))
  show "read_current_product (\<lambda>_ _ _. True) 7 1 read_example_query new_read_cut read_example_after = Product_Read_Busy"
    by (simp only: read_current_product_def Let_def current_read_example_projects_actual_authority
      after_write_the_cache_is_still_at_revision_zero actual_authority_write_replaces_value_zero_with_nine(2)
      stale option.simps simp_thms if_True if_False)
  let ?clear = "read_example_after\<lparr>query_cache := (\<lambda>_. None)\<rparr>"
  have auth: "read_authority ?clear = read_authority read_example_after" by simp
  have empty: "query_cache ?clear read_example_query = None" by simp
  show "read_current_product (\<lambda>_ _ _. True) 7 1 read_example_query new_read_cut
    (read_example_after\<lparr>query_cache := (\<lambda>_. None)\<rparr>) = Current_Cut_Value new_read_cut (Units_Value 9)"
    by (simp only: read_current_product_def Let_def auth empty query_cache_update_keeps_read_access
      query_cache_update_keeps_read_availability query_cache_update_keeps_asset_registration current_read_example_projects_actual_authority
      actual_authority_write_replaces_value_zero_with_nine option.simps simp_thms if_True if_False)
qed

lemma historical_revision_zero_is_still_the_old_value:
  "sample.read_historical_product (\<lambda>_ _ _. True) 7 1 read_example_query 0 read_example_after =
    Historical_Prefix_Value 0 (Units_Value 0)"
proof -
  let ?snapshot = "capture_snapshot (lock_example_core sample_initial)"
  have history: "sample.authority_prefix_snapshot 0 (read_authority read_example_after) = Some ?snapshot"
    by (simp add: sample.authority_prefix_snapshot_def sample.authority_prefix_core_def read_example_after_def
      update_settlement_outcomes_def read_example_state_defs read_example_write_call_fields(5) Let_def)
  have ready: "snapshot_query_ready read_example_query ?snapshot"
    by (simp add: snapshot_query_ready_def read_example_query_def capture_snapshot_def
      lock_example_core_def initial_finality_core_def lock_example_public_defs)
  show ?thesis by (simp only: sample.read_historical_product_def current_read_example_projects_actual_authority
    history ready old_read_example_has_value_zero option.simps simp_thms if_True if_False)
qed

definition cache_example_with_revision_check_removed where
  "cache_example_with_revision_check_removed = read_example_after\<lparr>query_cache :=
    (query_cache read_example_after)(read_example_query := map_option (\<lambda>entry. entry\<lparr>cached_cut :=
      (cached_cut entry)\<lparr>cut_revision := cut_revision (observed_product_cut (read_authority read_example_after))\<rparr>\<rparr>)
        (query_cache read_example_after read_example_query))\<rparr>"

lemma removing_only_the_revision_comparison_returns_a_stale_current_value:
  "read_current_product (\<lambda>_ _ _. True) 7 1 read_example_query new_read_cut cache_example_with_revision_check_removed =
    Current_Cut_Value new_read_cut (Units_Value 0)"
proof -
  let ?mutant = "cache_example_with_revision_check_removed"
  let ?entry = "\<lparr>cached_query = read_example_query, cached_provider = 100, cached_cut = new_read_cut, cached_value = Units_Value 0\<rparr>"
  have auth: "read_authority ?mutant = read_authority read_example_after"
    by (simp add: cache_example_with_revision_check_removed_def)
  have access: "read_access_bound (\<lambda>_ _ _. True) Read_Current 7 1 read_example_query ?mutant"
    by (simp only: cache_example_with_revision_check_removed_def query_cache_update_keeps_read_access
      current_read_example_projects_actual_authority(3))
  have available: "read_authority_available ?mutant"
    by (simp only: cache_example_with_revision_check_removed_def query_cache_update_keeps_read_availability
      current_read_example_projects_actual_authority(4))
  have registered: "read_asset_registered read_example_query ?mutant"
    by (simp only: cache_example_with_revision_check_removed_def query_cache_update_keeps_asset_registration
      current_read_example_projects_actual_authority(5))
  have cached: "query_cache ?mutant read_example_query = Some ?entry"
    by (simp add: cache_example_with_revision_check_removed_def after_write_the_cache_is_still_at_revision_zero
      current_read_example_projects_actual_authority(1))
  have usable: "cache_is_current_for ?entry read_example_query ?mutant"
    by (simp add: cache_is_current_for_def cache_example_with_revision_check_removed_def
      current_read_example_projects_actual_authority(1) after_write_the_provider_is_still_the_same)
  show ?thesis by (simp only: read_current_product_def Let_def auth access available registered
    current_read_example_projects_actual_authority actual_authority_write_replaces_value_zero_with_nine(2)
    cached usable option.simps product_cache_entry.select_convs simp_thms if_True if_False)
qed

lemma stale_observation_cannot_authorize_a_write_after_the_cut_moves:
  "fst (sample.execute_at_checked_cut permitted verified maintainers registered verified_ack
    entry 7 old_read_cut (7,2) payload read_example_after) = read_example_after"
  by (rule sample.stale_cut_cannot_authorize_a_product_effect)
    (simp add: current_read_example_projects_actual_authority)

lemma active_lock_can_be_written_at_its_checked_cut:
  "let s = initial_product_reads 100 (initial_settlement_world 99 (initial_origin_world (lock_example_world lock_example_held)));
       payload = \<lparr>payload_envelope = lock_example_envelope read_example_write,
         payload_credential = Some lock_example_token, payload_origin_epoch = 9\<rparr>
   in snd (sample.execute_at_checked_cut (\<lambda>_ _ _. True) (\<lambda>_ _ _. True) {} {0,2} (\<lambda>_. True)
         Normal_Lock_Entry 7 old_read_cut (7,1) payload s) = Forwarded_At_Checked_Cut"
  by (simp add: sample.execute_at_checked_cut_def result_access_bound_def product_identity_bound_def
      read_example_state_defs lock_example_envelope_def read_example_write_def sample_request_def read_authority_available_def Let_def)

end
