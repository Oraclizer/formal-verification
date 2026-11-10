theory Current_Read_G0
  imports "OIP_Current_Read_G0_Source.Current_Read_G0_Source"
begin

lemma current_read_g0_registration_preserved:
  "read_asset_registered query (current_read_g0_live_reads reads) = read_asset_registered query reads"
proof (cases "registration_sensitive_asset query")
  case None
  show ?thesis by (simp only: read_asset_registered_def None option.case)
next
  case (Some asset)
  show ?thesis
    unfolding read_asset_registered_def Some option.case
    by (rule arg_cong[OF current_read_g0_owner_lookup, where f="\<lambda>owner. owner \<noteq> None"])
qed

lemma current_read_g0_live_projections:
  "observed_product_cut (read_authority (current_read_g0_live_reads reads)) =
    observed_product_cut (read_authority reads)"
  "authoritative_read_core (read_authority (current_read_g0_live_reads reads)) =
    authoritative_read_core (read_authority reads)"
  "read_access_bound permitted kind who session query (current_read_g0_live_reads reads) =
    read_access_bound permitted kind who session query reads"
  "read_asset_registered query (current_read_g0_live_reads reads) = read_asset_registered query reads"
  "read_authority_available (current_read_g0_live_reads reads)"
  "query_cache (current_read_g0_live_reads reads) query = None"
  "observed_product_cut (read_authority (regulated_read_world (current_read_g0_reopen reads))) =
    observed_product_cut (read_authority reads)"
  apply (simp_all only: current_read_g0_registration_preserved)
  by (simp_all add: current_read_g0_reopen_defs observed_product_cut_def current_product_cut_def
    authoritative_read_core_def read_access_bound_def read_authority_available_def)

lemma current_read_g0_initial_reads:
  "observed_product_cut (read_authority read_example_before) = old_read_cut"
  "authoritative_read_core (read_authority read_example_before) = lock_example_core sample_initial"
  "read_access_bound (\<lambda>_ _ _. True) Read_Current 7 1 read_example_query read_example_before"
  "read_asset_registered read_example_query read_example_before"
  "snapshot_query_ready read_example_query (capture_snapshot (lock_example_core sample_initial))"
  by (simp_all add: read_example_state_defs read_access_bound_def read_example_query_def
    snapshot_query_ready_def capture_snapshot_def lock_example_core_def initial_finality_core_def lock_example_public_defs)

lemma current_read_g0_core_results:
  "read_current_product (\<lambda>_ _ _. True) 7 1 read_example_query old_read_cut
    (current_read_g0_live_reads read_example_before) = Current_Cut_Value old_read_cut (Units_Value 0)"
  "read_current_product (\<lambda>_ _ _. True) 7 1 read_example_query old_read_cut
    (current_read_g0_live_reads read_example_after) = Product_Read_Busy"
proof -
  let ?before = "current_read_g0_live_reads read_example_before"
  let ?after = "current_read_g0_live_reads read_example_after"
  have initial_core: "authoritative_read_core (read_authority ?before) = lock_example_core sample_initial"
    by (simp only: current_read_g0_live_projections(2) current_read_g0_initial_reads(2))
  have initial_access: "read_access_bound (\<lambda>_ _ _. True) Read_Current 7 1 read_example_query ?before"
    unfolding current_read_g0_live_projections(3)
    by (rule current_read_g0_initial_reads(3))
  have after_access: "read_access_bound (\<lambda>_ _ _. True) Read_Current 7 1 read_example_query ?after"
    unfolding current_read_g0_live_projections(3)
    by (rule current_read_example_projects_actual_authority(3))
  have stale: "old_read_cut \<noteq> observed_product_cut (read_authority ?after)"
    unfolding current_read_g0_live_projections(1) current_read_example_projects_actual_authority(1)
    by simp
  show "read_current_product (\<lambda>_ _ _. True) 7 1 read_example_query old_read_cut ?before =
    Current_Cut_Value old_read_cut (Units_Value 0)"
    by (simp only: read_current_product_def Let_def initial_core initial_access
      current_read_g0_live_projections(1,4,5,6) current_read_g0_initial_reads(1,4,5)
      old_read_example_has_value_zero option.case simp_thms if_True if_False)
  show "read_current_product (\<lambda>_ _ _. True) 7 1 read_example_query old_read_cut ?after =
    Product_Read_Busy"
    by (rule sample.stale_current_request_is_closed
      [OF after_access current_read_g0_live_projections(5) stale])
qed

lemma current_read_g0_gate:
  "identity_read_allowed identity_case_directory (current_read_g0_policy granted)
    identity_case_directory current_read_g0_verify 7 (identity_case_proof 1 9) 2 current_read_g0_request
    (identity_source (discard_process_cache (current_read_g0_reopen reads))) =
    (granted \<and> read_access_bound (\<lambda>_ _ _. True) Read_Current 7 1 read_example_query
       (current_read_g0_live_reads reads) \<and>
     cut_authority_epoch (observed_product_cut (read_authority reads)) = 9)"
  by (auto simp: identity_read_allowed_def current_read_g0_policy_def current_read_g0_verify_def
    identity_case_directory_def identity_case_user_def identity_case_proof_def active_identity_def
    identity_source_def read_access_bound_def observed_product_cut_def current_product_cut_def
    current_read_g0_reopen_defs)

lemma current_read_g0_snapshot_fields:
  "reference_grants_fit {2} (reference_product (current_read_g0_snapshot reads))
    (reference_inputs (current_read_g0_snapshot reads))"
  "\<lparr>reference_product = reference_product (current_read_g0_snapshot reads),
     reference_inputs = reference_inputs (current_read_g0_snapshot reads)\<rparr> =
    current_read_g0_snapshot reads"
  by (simp_all add: current_read_g0_snapshot_def reference_grants_fit_def Let_def)

lemma current_read_g0_selected_wire_service:
  "current_read_g0_consume granted before =
    current_read_g0_execute granted
      \<lparr>reference_connection = Authority_Connected,
       reference_service_action = Service_Read 7 (identity_case_proof 1 9) 2 current_read_g0_request None,
       reference_supplied_grants = None\<rparr> before"
proof -
  interpret selected: reference_trace_consumer
    example_roster example_faulty example_bound example_threshold
    sample_verifies sample_signed sample_truth sample_source
    "current_read_g0_execute granted"
    identity_case_directory "\<lambda>_ _ _ _ _. False"
    "current_read_g0_policy granted" identity_case_directory "\<lambda>_ _ _ _ _ _. False"
    current_read_g0_verify "\<lambda>_ _ _ _ _ _. False" "\<lambda>_ _. False"
    "\<lambda>_ _ _ _ _ _ _. False" "\<lambda>_ _ _ _. False" "\<lambda>_ _ _ _ _. False"
    "\<lambda>_ _ _. False" "\<lambda>_ _ _. False" "\<lambda>_ _ _. False"
    "{}" "{2}" "\<lambda>_. False" "\<lambda>_ _. False"
    apply (rule reference_trace_consumer.intro[OF sample.source_attestation_axioms])
    apply (rule reference_trace_consumer_axioms.intro)
    by (intro ext) (simp only: current_read_g0_execute_def)
  show ?thesis
    by (simp only: current_read_g0_consume_def selected.code_execute_fixed_source_read_def
      current_read_g0_selects_original option.case)
qed

lemma current_read_g0_uses_retained_service:
  "current_read_g0_consume granted (current_read_g0_snapshot reads) =
    (current_read_g0_snapshot reads,
      Some (Scheduled_Endpoint (Service_Read_Result
        (sample.read_at_identity_endpoint identity_case_directory (current_read_g0_policy granted)
          identity_case_directory current_read_g0_verify 7 (identity_case_proof 1 9) 2
          current_read_g0_request (discard_process_cache (current_read_g0_reopen reads))))))"
  unfolding current_read_g0_selected_wire_service current_read_g0_execute_def reference_service_input.select_convs
  by (simp add: sample.service_at_reference_snapshot_def sample.schedule_at_retained_state_def
    sample.schedule_service_step_def product_round_trip_preserves_the_durable_projection
    select_reference_grants_def sample.read_with_revalidated_cache_def
    current_read_g0_snapshot_fields Let_def split: identity_read_reply.splits product_read_reply.splits)

lemma current_read_g0_fixture_identity:
  "identity_case_directory 7 = Some (identity_case_user 7)"
  "identity_principal (identity_case_user 7) = 7"
  "proof_session (identity_case_proof 1 9) = 1"
  by (simp_all add: identity_case_directory_def identity_case_user_def identity_case_proof_def)

lemma current_read_g0_fixture_gates:
  "identity_read_allowed identity_case_directory (current_read_g0_policy granted)
    identity_case_directory current_read_g0_verify 7 (identity_case_proof 1 9) 2 current_read_g0_request
    (identity_source (discard_process_cache (current_read_g0_reopen read_example_before))) = granted"
  "identity_read_allowed identity_case_directory (current_read_g0_policy granted)
    identity_case_directory current_read_g0_verify 7 (identity_case_proof 1 9) 2 current_read_g0_request
    (identity_source (discard_process_cache (current_read_g0_reopen read_example_after))) = granted"
  by (simp_all only: current_read_g0_gate current_read_g0_live_projections(3)
    current_read_g0_initial_reads(1,3) current_read_example_projects_actual_authority(1,3)
    product_cut.select_convs simp_thms)

lemma current_read_g0_fixed_results:
  "current_read_g0_consume True (current_read_g0_snapshot read_example_before) =
    (current_read_g0_snapshot read_example_before,
      Some (Scheduled_Endpoint (Service_Read_Result
        (Authorized_Data (Current_Cut_Value old_read_cut (Units_Value 0))))))"
  "current_read_g0_consume True (current_read_g0_snapshot read_example_after) =
    (current_read_g0_snapshot read_example_after,
      Some (Scheduled_Endpoint (Service_Read_Result (Authorized_Data Product_Read_Busy))))"
  "current_read_g0_consume False (current_read_g0_snapshot read_example_before) =
    (current_read_g0_snapshot read_example_before,
      Some (Scheduled_Endpoint (Service_Read_Result Identity_Read_Rejected)))"
  by (simp_all only: current_read_g0_uses_retained_service sample.read_at_identity_endpoint_def
    current_read_g0_fixture_gates current_read_g0_live_projections(5) current_read_g0_fixture_identity
    sample.authorized_read_value.simps(1) current_read_g0_core_results
    Let_def option.case simp_thms if_True if_False)

text \<open>
  The first-arrival replay check prepares an immutable candidate. The canary
  releases the read and selects that candidate only if its synthetic head
  comparison still succeeds. The retained service refuses before selection.
\<close>

fun current_read_g0_selectable :: "scheduled_service_reply option \<Rightarrow> bool" where
  "current_read_g0_selectable (Some (Scheduled_Endpoint (Service_Read_Result
    (Authorized_Data (Current_Cut_Value _ _))))) = True"
| "current_read_g0_selectable (Some (Scheduled_Endpoint (Service_Read_Result
    (Authorized_Data Product_Read_Busy)))) = True"
| "current_read_g0_selectable _ = False"

definition current_read_g0_seed where
  "current_read_g0_seed reads =
    \<lparr>rust_replay_bindings = (\<lambda>_. None), rust_replay_selected_head = Some (0::nat),
      rust_replay_order = 0, rust_replay_product = current_read_g0_snapshot reads\<rparr>"

definition current_read_g0_first where
  "current_read_g0_first granted live_head before =
    (case rust_replay_check True (admit_replay replay_first_bytes) (1::nat) before of
       (prepared, Wire_First _) \<Rightarrow>
         (let (after, reply) = current_read_g0_consume granted (rust_replay_product before)
          in if current_read_g0_selectable reply then
               if live_head = rust_replay_selected_head before
               then (prepared\<lparr>rust_replay_product := after\<rparr>, reply) else (before, None)
             else (before, reply))
     | _ \<Rightarrow> (before, None))"

definition current_read_g0_observe where
  "current_read_g0_observe granted live_head reads =
    (let (selected_read_image, reply) = current_read_g0_first granted live_head (current_read_g0_seed reads);
         observed_read_cut = observed_product_cut (read_authority
           (regulated_read_world (reopen_retained_product Authority_Connected
             (reference_product (rust_replay_product selected_read_image)))))
     in (reply, observed_read_cut, rust_replay_selected_head selected_read_image, rust_replay_order selected_read_image,
         rust_replay_bindings selected_read_image (authenticated_wire_message_id replay_first_core)))"

lemma current_read_g0_product_preserved:
  "rust_replay_product (fst (current_read_g0_first granted live_head (current_read_g0_seed reads))) =
    current_read_g0_snapshot reads"
  by (simp add: current_read_g0_first_def current_read_g0_seed_def rust_replay_check_def
    both_exact_signed_queries_are_individually_admissible_at_the_delivery_boundary
    current_read_g0_uses_retained_service Let_def split: if_splits)

lemma current_read_g0_observations:
  "current_read_g0_observe True (Some 0) read_example_before =
    (Some (Scheduled_Endpoint (Service_Read_Result
       (Authorized_Data (Current_Cut_Value old_read_cut (Units_Value 0))))),
     old_read_cut, Some 1, 1, Some replay_first_core_bytes)"
  "current_read_g0_observe True (Some 0) read_example_after =
    (Some (Scheduled_Endpoint (Service_Read_Result (Authorized_Data Product_Read_Busy))),
     new_read_cut, Some 1, 1, Some replay_first_core_bytes)"
  "current_read_g0_observe False (Some 0) read_example_before =
    (Some (Scheduled_Endpoint (Service_Read_Result Identity_Read_Rejected)),
     old_read_cut, Some 0, 0, None)"
  "current_read_g0_observe True (Some 2) read_example_before =
    (None, old_read_cut, Some 0, 0, None)"
  by (simp_all add: current_read_g0_observe_def current_read_g0_first_def current_read_g0_seed_def
    rust_replay_check_def both_exact_signed_queries_are_individually_admissible_at_the_delivery_boundary
    replay_first_encodes_the_exact_core current_read_g0_fixed_results current_read_g0_live_projections
    current_read_g0_initial_reads current_read_example_projects_actual_authority(1) Let_def)

thm_oracles current_read_g0_selects_original current_read_g0_fixed_results
  current_read_g0_product_preserved current_read_g0_observations

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms current_read_g0_selects_original
      current_read_g0_fixed_results current_read_g0_product_preserved current_read_g0_observations})
  then () else error "Unexpected oracle in CurrentRead G-0"
\<close>

end
