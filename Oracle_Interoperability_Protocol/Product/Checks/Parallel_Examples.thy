theory Parallel_Examples
  imports "../Parallel_Trace" "OIP_Product_Base.Propagation_Examples" Identity_Examples Read_Cut_Examples
begin

abbreviation parallel_example_key where "parallel_example_key \<equiv> ((0,17),0)"

definition parallel_example_settlement where
  "parallel_example_settlement = enqueue_secondary (0,17) (queue_example_world call_example_ready)"

definition parallel_example_world where
  "parallel_example_world = initial_regulated_product (initial_product_reads 1 parallel_example_settlement)"

lemma exact_parallel_job_dispatch_is_nonvacuous:
  "let result = execute_settlement_action verified (Exact_Dispatch_Secondary parallel_example_key) parallel_example_settlement;
       next_job = queue_example_job\<lparr>secondary_attempts := 1, secondary_state := Secondary_In_Flight\<rparr>
   in settlement_jobs (fst result) parallel_example_key = Some next_job \<and>
      snd result = Settlement_Dispatched (Some next_job) \<and> settlement_primary (fst result) = settlement_primary parallel_example_settlement"
  by (simp add: parallel_example_settlement_def checked_primary_commitment_opens_one_secondary_job
      execute_settlement_action_def step_settlement_slot_def queue_example_job_def Let_def)

lemma same_slot_dispatch_and_enqueue_change_the_reply_when_reordered:
  "let s = queue_example_world call_example_ready;
       left = execute_settlement_action verified (Exact_Enqueue (0,17)) s;
       right_first = execute_settlement_action verified (Exact_Dispatch_Secondary parallel_example_key) s;
       right_after_left = execute_settlement_action verified (Exact_Dispatch_Secondary parallel_example_key) (fst left)
   in snd right_first = Settlement_Dispatched None \<and>
      snd right_after_left = Settlement_Dispatched (Some
       (queue_example_job\<lparr>secondary_attempts := 1, secondary_state := Secondary_In_Flight\<rparr>))"
proof -
  let ?before = "queue_example_world call_example_ready"
  have absent: "settlement_jobs ?before parallel_example_key = None"
    by (simp add: queue_example_world_def initial_settlement_world_def)
  have first: "fst (execute_settlement_action verified (Exact_Enqueue (0,17)) ?before) = parallel_example_settlement"
    by (simp add: exact_queue_effect_is_the_existing_endpoint_effect(1) parallel_example_settlement_def)
  have empty: "snd (execute_settlement_action verified (Exact_Dispatch_Secondary parallel_example_key) ?before) =
    Settlement_Dispatched None"
    by (simp add: execute_settlement_action_def step_settlement_slot_def Let_def absent)
  show ?thesis using exact_parallel_job_dispatch_is_nonvacuous[of verified]
    by (simp add: Let_def first empty)
qed

lemma two_dispatches_of_one_job_return_different_attempts_to_the_occurrences:
  "let first = execute_settlement_action verified (Exact_Dispatch_Secondary parallel_example_key) parallel_example_settlement;
       second = execute_settlement_action verified (Exact_Dispatch_Secondary parallel_example_key) (fst first)
   in snd first \<noteq> snd second"
proof -
  let ?step = "execute_settlement_action verified (Exact_Dispatch_Secondary parallel_example_key)"
  let ?first = "?step parallel_example_settlement"
  have first_slot: "settlement_jobs (fst ?first) parallel_example_key =
      Some (queue_example_job\<lparr>secondary_attempts := 1, secondary_state := Secondary_In_Flight\<rparr>)"
    using exact_parallel_job_dispatch_is_nonvacuous[of verified] by (simp add: Let_def)
  have first_reply: "snd ?first =
      Settlement_Dispatched (Some (queue_example_job\<lparr>secondary_attempts := 1, secondary_state := Secondary_In_Flight\<rparr>))"
    using exact_parallel_job_dispatch_is_nonvacuous[of verified] by (simp add: Let_def)
  have second_reply: "snd (?step (fst ?first)) =
      Settlement_Dispatched (Some (queue_example_job\<lparr>secondary_attempts := 2, secondary_state := Secondary_In_Flight\<rparr>))"
    by (subst execute_settlement_action_def) (simp add: step_settlement_slot_def Let_def first_slot)
  show ?thesis unfolding Let_def first_reply second_reply
    by (simp add: queue_example_job_def)
qed

lemma exhausted_attempt_counter_does_not_dispatch:
  assumes "secondary_attempts job = 2^64 - 1"
  shows "step_one_slot verified (Slot_Dispatch key) (Some job) = (Some job, Settlement_Dispatched None)"
  using assms by simp

lemma same_slot_actions_cannot_exchange_even_with_unchanged_authority:
  "\<not> compatible_service_actions (Service_Maintenance (Exact_Dispatch_Secondary parallel_example_key))
    (Service_Maintenance (Exact_Secondary_Failed parallel_example_key)) parallel_example_settlement"
  by (simp add: compatible_service_actions_def service_access_footprint_def Let_def)

lemma an_actual_queue_write_can_exchange_with_an_authorized_observation:
  "compatible_service_actions (Service_Maintenance (Exact_Dispatch_Secondary parallel_example_key))
    (Service_Read token proof target (Raw_Data (Source_Balance (0,17))) None) parallel_example_settlement"
  by (simp add: compatible_service_actions_def service_access_footprint_def Let_def)

lemma different_exact_jobs_can_exchange_under_the_same_authority:
  "compatible_service_actions (Service_Maintenance (Exact_Dispatch_Secondary ((0,17),0)))
    (Service_Maintenance (Exact_Dispatch_Secondary ((0,22),1))) parallel_example_settlement"
  by (simp add: compatible_service_actions_def service_access_footprint_def Let_def)

lemma epoch_and_provider_dependence_remain_even_for_a_different_asset:
  "\<not> compatible_service_actions
    (Service_Maintenance (Exact_Install maintainer epoch changes sessions))
    (Service_Read token proof target (Historical_Data (Application_Value 22) 0) None) parallel_example_settlement"
  by (simp add: compatible_service_actions_def service_access_footprint_def Let_def)

lemma actual_primary_write_changes_the_reply_to_the_same_signed_cut:
  "read_current_product (\<lambda>_ _ _. True) 7 1 read_example_query old_read_cut read_example_before =
    Current_Cut_Value old_read_cut (Units_Value 0)"
  "read_current_product (\<lambda>_ _ _. True) 7 1 read_example_query old_read_cut read_example_after =
    Product_Read_Busy"
proof -
  show "read_current_product (\<lambda>_ _ _. True) 7 1 read_example_query old_read_cut read_example_before =
    Current_Cut_Value old_read_cut (Units_Value 0)"
    by (simp add: read_current_product_def read_access_bound_def read_authority_available_def
        snapshot_query_ready_def read_example_state_defs read_example_query_def
        capture_snapshot_def lock_example_core_def initial_finality_core_def lock_example_public_defs Let_def)
  show "read_current_product (\<lambda>_ _ _. True) 7 1 read_example_query old_read_cut read_example_after =
    Product_Read_Busy"
    using current_read_example_projects_actual_authority(3)[of Read_Current]
    by (simp add: read_current_product_def Let_def current_read_example_projects_actual_authority(1,4))
qed

context source_attestation
begin

lemma authorized_raw_observation_of_the_published_credit_is_five:
  "read_with_revalidated_cache identity_case_directory (\<lambda>_ _ _ _. True) identity_case_directory
    (\<lambda>_ _ _ _. True) 7 (identity_case_proof 1 9) 2 (Raw_Data (Destination_Balance (2,17,3))) None parallel_example_world =
      Authorized_Raw (Units_Value 5)"
proof -
  let ?world = "discard_process_cache parallel_example_world"
  let ?query = "Destination_Balance (2,17,3)"
  have source: "identity_source ?world = terminal_example_world call_example_ready"
    by (simp add: identity_source_def observed_product_source_def discard_process_cache_def parallel_example_world_def
        initial_product_reads_def initial_regulated_product_def initial_governed_world_def initial_legal_world_def
        regulated_read_world_def replace_regulated_reads_def parallel_example_settlement_def secondary_steps_preserve_primary
        queue_example_world_def initial_settlement_world_def queue_example_primary_def initial_origin_world_def initial_outcome_world_def)
  have auth: "identity_case_directory 7 = Some (identity_case_user 7)"
    by (simp add: identity_case_directory_def)
  have allowed: "identity_read_allowed identity_case_directory (\<lambda>_ _ _ _. True) identity_case_directory
    (\<lambda>_ _ _ _. True) 7 (identity_case_proof 1 9) 2 (Raw_Data ?query) (identity_source ?world)"
    unfolding source
    by (simp add: identity_read_allowed_def active_identity_def current_product_cut_def handover_case_defs)
  have calls: "exact_calls (read_authority (regulated_read_world ?world)) = product_calls (terminal_example_world call_example_ready)"
    using source by (simp add: identity_source_def observed_product_source_def exact_calls_def outcome_calls_def)
  have available: "read_authority_available (regulated_read_world ?world)"
    unfolding read_authority_available_def calls
    by (simp add: terminal_example_world_def initial_call_machine_def)
  have registered: "read_asset_registered ?query (regulated_read_world ?world)"
    by (simp add: read_asset_registered_def identity_source_def[symmetric] source
        terminal_example_world_def lock_example_world_def)
  have value_at_cut: "stored_query ?query
    (capture_snapshot (authoritative_read_core (read_authority (regulated_read_world ?world)))) = Units_Value 5"
    using full_credit_consumer_activates
    by (simp add: capture_snapshot_def authoritative_read_core_def calls terminal_example_world_def initial_call_machine_def
        call_example_ready_parent)
  show ?thesis
    using a_live_authorized_raw_read_observes_the_actual_current_source[OF auth allowed available registered] value_at_cut
    by (simp add: read_with_revalidated_cache_def Let_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
     different_actual_settlement_slots_exchange
     source_attestation.compatible_actual_product_actions_exchange
     source_attestation.the_actual_product_finite_exchange_closure
     same_slot_dispatch_and_enqueue_change_the_reply_when_reordered})
  then () else error "Unexpected oracle in actual service composition"
\<close>

end
