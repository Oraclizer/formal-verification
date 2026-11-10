theory Current_Read_G0_Source
  imports
    "OIP_Message_Code.Wire_Code_Fixed_Read_Execution"
    "OIP_Reference_Execution.Reference_Signed_Replay_Code"
    "OIP_Product.Read_Cut_Examples"
    "OIP_Product.Identity_Examples"
begin

abbreviation current_read_g0_request where
  "current_read_g0_request \<equiv> Current_Data read_example_query old_read_cut"

definition current_read_g0_policy where
  "current_read_g0_policy granted identity target request epoch \<longleftrightarrow>
    granted \<and> identity_principal identity = 7 \<and> target = 2 \<and>
    request = current_read_g0_request \<and> epoch = 9"

definition current_read_g0_verify where
  "current_read_g0_verify identity proof target request \<longleftrightarrow>
    identity = identity_case_user 7 \<and> proof = identity_case_proof 1 9 \<and>
    target = 2 \<and> request = current_read_g0_request"

definition current_read_g0_snapshot where
  "current_read_g0_snapshot reads =
    (let records = capture_retained_product (initial_regulated_product reads)
     in \<lparr>reference_product = records,
          reference_inputs = \<lparr>reference_epoch = reference_records_epoch records,
            reference_grants = (\<lambda>_. {})\<rparr>\<rparr>)"

definition current_read_g0_execute where
  "current_read_g0_execute granted (entry :: nat reference_service_input) =
    sample.service_at_reference_snapshot identity_case_directory (\<lambda>_ _ _ _ _. False)
      (current_read_g0_policy granted) identity_case_directory (\<lambda>_ _ _ _ _ _. False)
      current_read_g0_verify (\<lambda>_ _ _ _ _ _. False) (\<lambda>_ _. False)
      (\<lambda>_ _ _ _ _ _ _. False) (\<lambda>_ _ _ _. False) (\<lambda>_ _ _ _ _. False)
      (\<lambda>_ _ _. False) (\<lambda>_ _ _. False) (\<lambda>_ _ _. False)
      {} {2} (\<lambda>_. False) (\<lambda>_ _. False)
      (reference_connection entry) (reference_service_action entry) (reference_supplied_grants entry)"

definition current_read_g0_consume where
  "current_read_g0_consume granted before =
    reference_trace_consumer.code_execute_fixed_source_read (current_read_g0_execute granted)
      replay_fixture_verifier (\<lambda>_. True) replay_scope 7 replay_first_bytes Authority_Connected before"

lemma current_read_g0_original_passes_precheck:
  "code_check_declared_version replay_first_bytes (boundary_max_frame replay_scope) = None"
proof -
  have canonical: "encode_wire_packet replay_first_packet = replay_first_bytes"
    "wire_packet_wellformed replay_first_packet"
    using every_accepted_wire_message_has_exactly_the_received_bytes
      [OF replay_first_decodes_the_exact_signed_packet] by blast+
  have version: "wire_version (packet_core replay_first_packet) = 6"
    by (simp add: replay_first_core_def)
  have bound: "length (encode_wire_packet replay_first_packet) \<le> boundary_max_frame replay_scope"
    by (simp add: canonical(1) replay_first_bytes_def replay_scope_def)
  from a_canonical_current_packet_passes_the_declared_version_precheck
    [OF canonical(2) version bound]
  show ?thesis by (simp only: canonical(1))
qed

lemma current_read_g0_selects_original:
  "code_select_nonreceipt_read_service replay_fixture_verifier (\<lambda>_. True) replay_scope
    (7::nat) replay_first_bytes =
    Some (Service_Read 7 (identity_case_proof 1 9) 2 current_read_g0_request None)"
proof -
  have read: "code_source_nonreceipt_read_service (7::nat) replay_first_core =
    Some (Service_Read 7 (identity_case_proof 1 9) 2 current_read_g0_request None)"
    using a_current_source_application_query_keeps_the_session_epoch_cut_and_asset
      [of replay_first_core 1 0 17 "7::nat"]
    by (simp add: replay_first_core_def read_example_query_def identity_case_proof_def)
  have precheck: "code_check_declared_version replay_first_bytes (boundary_max_frame replay_scope) = None"
    by (rule current_read_g0_original_passes_precheck)
  have gate: "code_library_gate replay_fixture_verifier (\<lambda>_. True) code_nonreceipt_read_allowed
      replay_scope replay_first_bytes = Gate_Admitted replay_first_packet"
  proof -
    have "code_library_gate replay_fixture_verifier (\<lambda>_. True) code_nonreceipt_read_allowed
        replay_scope replay_first_bytes =
      wire_gate replay_fixture_verifier (\<lambda>_. True) code_nonreceipt_read_allowed replay_scope replay_first_bytes"
      apply (rule prechecked_current_input_reuses_the_model_admission)
        apply (simp add: replay_scope_def)
       apply (rule precheck)
      by (simp add: replay_scope_def)
    also have "\<dots> = admit_replay replay_first_bytes"
      by (simp add: admit_replay_def wire_gate_def replay_first_decodes_the_exact_signed_packet
        code_nonreceipt_read_allowed_def code_decode_query_nonreceipt_def replay_first_core_def Let_def)
    finally show ?thesis by (simp add: both_exact_signed_queries_are_individually_admissible_at_the_delivery_boundary)
  qed
  show ?thesis by (simp add: code_select_nonreceipt_read_service_def gate read)
qed

abbreviation current_read_g0_reopen where
  "current_read_g0_reopen reads \<equiv>
    reopen_retained_product Authority_Connected (reference_product (current_read_g0_snapshot reads))"

abbreviation current_read_g0_live_reads where
  "current_read_g0_live_reads reads \<equiv>
    regulated_read_world (discard_process_cache (current_read_g0_reopen reads))"

lemmas current_read_g0_reopen_defs = current_read_g0_snapshot_def capture_retained_product_def
  capture_retained_source_def reopen_retained_product_def reopen_retained_source_def
  initial_regulated_product_def initial_governed_world_def initial_legal_world_def
  initial_product_reads_def discard_process_cache_def replace_regulated_reads_def
  regulated_read_world_def observed_product_source_def exact_calls_def outcome_calls_def Let_def

lemma current_read_g0_owner_lookup:
  "product_owners (product_durable (observed_product_source
      (read_authority (current_read_g0_live_reads reads)))) asset =
    product_owners (product_durable (observed_product_source (read_authority reads))) asset"
proof -
  have cache: "read_authority (current_read_g0_live_reads reads) =
      read_authority (regulated_read_world (current_read_g0_reopen reads))"
    by (simp add: discard_process_cache_def replace_regulated_reads_def regulated_read_world_def)
  have captured: "retained_source (reference_product (current_read_g0_snapshot reads)) =
      capture_retained_source (observed_product_source (read_authority reads))"
    by (simp add: current_read_g0_snapshot_def capture_retained_product_def
      initial_regulated_product_def initial_governed_world_def initial_legal_world_def
      observed_product_source_def Let_def)
  show ?thesis
    unfolding cache identity_source_def[symmetric]
    by (simp add: recovery_projection_supplies_the_exact_source captured
      reopen_retained_source_def capture_retained_source_def Let_def)
qed

end
