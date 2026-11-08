theory Identity_Examples
  imports "../Owner_Recovery" "OIP_Product_Base.Lock_Terminal_Entries"
begin

definition identity_case_user where
  "identity_case_user who = \<lparr>identity_principal = who, identity_domain = 0, identity_ocid = who + 100, identity_rai = who + 200\<rparr>"

definition identity_case_directory where
  "identity_case_directory who = (if who \<in> {7,8} then Some (identity_case_user who) else None)"

definition identity_case_proof where
  "identity_case_proof session epoch = \<lparr>proof_session = session, proof_epoch = epoch\<rparr>"

definition handover_case_source :: product_world where
  "handover_case_source =
    (let source = terminal_example_world (finality_sample_source 17); durable = product_durable source
     in source\<lparr>product_durable := durable\<lparr>product_owners := (product_owners durable)(17 := Some 7),
        product_sessions := (product_sessions durable)(2 := Some \<lparr>session_principal = 7, session_epoch = 9\<rparr>)\<rparr>\<rparr>)"

definition handover_case_context :: "nat \<Rightarrow> lock_context" where
  "handover_case_context endpoint =
    (let cfg = lock_example_contexts endpoint in cfg\<lparr>lock_authority := (lock_authority cfg)\<lparr>context_authority_epoch := 10\<rparr>\<rparr>)"

definition handover_case_proposal :: ownership_transfer where
  "handover_case_proposal = \<lparr>transfer_asset = 17, transfer_previous = 7, transfer_successor = 8,
    transfer_expected = \<lparr>cut_authority_epoch = 9, cut_revision = 0\<rparr>,
    transfer_old_session = 1, transfer_new_session = 3, transfer_epoch = 10,
    transfer_contexts = [(0, handover_case_context 0), (2, handover_case_context 2)]\<rparr>"

definition identity_case_payload where
  "identity_case_payload = \<lparr>payload_envelope = lock_example_envelope lock_example_dispatch,
    payload_credential = Some lock_example_token, payload_origin_epoch = 9\<rparr>"

lemmas handover_case_defs = handover_case_source_def handover_case_proposal_def handover_case_context_def
  identity_case_user_def identity_case_directory_def identity_case_proof_def terminal_example_world_def lock_example_world_def
  initial_call_machine_def lock_example_contexts_def sample_source_context_def sample_context_def example_context_def Let_def

lemma handover_case_is_admitted:
  "handover_is_authorized identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory
    (\<lambda>_ _. True) 7 8 99 {99} {0,2} handover_case_proposal handover_case_source"
  by (simp add: handover_is_authorized_def handover_case_defs owner_of_product_def current_product_cut_def
      lock_context_batch_is_newer_def active_identity_def)

lemma handover_needs_the_successor_consent:
  "\<not> handover_is_authorized identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory
    (\<lambda>identity _. identity_principal identity = 7) 7 8 99 {99} {0,2} handover_case_proposal handover_case_source"
  by (simp add: handover_is_authorized_def handover_case_defs)

lemma current_identity_can_submit_the_bound_request:
  "endpoint_call_allowed identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory
    (\<lambda>_ _ _ _ _ _. True) 7 (identity_case_proof 1 9) 0 Execute_Ordinary 7 (7,1) identity_case_payload handover_case_source"
  by (simp add: endpoint_call_allowed_def endpoint_call_identity_def active_identity_def product_identity_bound_def current_product_cut_def
      identity_case_payload_def lock_example_envelope_def lock_example_dispatch_def sample_request_def handover_case_defs)

lemma another_namespace_cannot_submit_even_with_a_valid_signature:
  "\<not> endpoint_call_allowed identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory
    (\<lambda>_ _ _ _ _ _. True) 7 (identity_case_proof 1 9) 0 Execute_Ordinary 7 (8,1) identity_case_payload handover_case_source"
  by (simp add: endpoint_call_allowed_def endpoint_call_identity_def product_identity_bound_def Let_def)

lemma missing_exact_role_cannot_enter_the_consumer:
  "\<not> endpoint_call_allowed identity_case_directory (\<lambda>_ _ _ use _. use = Read_Receipt) identity_case_directory
    (\<lambda>_ _ _ _ _ _. True) 7 (identity_case_proof 1 9) 0 Execute_Ordinary 7 (7,1) identity_case_payload handover_case_source"
  by (simp add: endpoint_call_allowed_def endpoint_call_identity_def Let_def)

context source_attestation
begin

abbreviation handover_case_after where
  "handover_case_after \<equiv> apply_owner_handover identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory
    (\<lambda>_ _. True) 7 8 99 {99} {0,2} handover_case_proposal handover_case_source"

lemma handover_case_closes_and_opens_on_one_transition:
  "product_sessions (product_durable handover_case_after) 1 = None \<and>
    product_sessions (product_durable handover_case_after) 3 = Some \<lparr>session_principal = 8, session_epoch = 10\<rparr> \<and>
    owner_of_product handover_case_after 17 = Some 8 \<and> cut_authority_epoch (current_product_cut handover_case_after) = 10"
  using handover_atomically_changes_owner_and_sessions_without_spending[OF handover_case_is_admitted]
  by (simp add: handover_case_proposal_def)

lemma handover_case_preserves_the_actual_five_pending_units:
  "let rs = authoritative_reservation_state handover_case_after in
    source_units rs (0,17) = 5 \<and> sample_binding 17 \<in> unresolved_source_obligations rs \<and>
    destination_units rs (2,17,3) = 0"
  using handover_atomically_changes_owner_and_sessions_without_spending(5)[OF handover_case_is_admitted]
    source_debit_puts_five_into_pending
  by (simp add: authoritative_reservation_state_def handover_case_defs)

end

lemma removing_only_the_epoch_binding_revives_an_old_envelope_under_a_reused_number:
  "let old = handover_case_source; durable = product_durable old;
       reissued = old\<lparr>product_durable := durable\<lparr>product_authority_epoch := 10,
         product_sessions := (product_sessions durable)(1 := Some \<lparr>session_principal = 7, session_epoch = 10\<rparr>)\<rparr>\<rparr>
   in \<not> endpoint_call_allowed identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory
        (\<lambda>_ _ _ _ _ _. True) 7 (identity_case_proof 1 10) 0 Read_Receipt 7 (7,1) identity_case_payload reissued \<and>
      endpoint_call_identity identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory
        (\<lambda>_ _ _ _ _ _. True) 7 (identity_case_proof 1 10) 0 Read_Receipt 7 (7,1) identity_case_payload reissued"
  by (simp add: endpoint_call_allowed_def endpoint_call_identity_def active_identity_def product_identity_bound_def
      current_product_cut_def identity_case_payload_def lock_example_envelope_def lock_example_dispatch_def
      sample_request_def handover_case_defs)

definition handover_case_world where
  "handover_case_world = initial_regulated_product
    (initial_product_reads 1 (initial_settlement_world 2 (initial_origin_world handover_case_source)))"

lemma identity_case_has_the_actual_source:
  "identity_source handover_case_world = handover_case_source"
  by (simp add: identity_source_def handover_case_world_def initial_regulated_product_def initial_governed_world_def
      initial_legal_world_def regulated_read_world_def initial_product_reads_def initial_settlement_world_def
      initial_origin_world_def initial_outcome_world_def observed_product_source_def)

lemma handover_case_retains_a_live_reservation:
  "\<exists>claim. recoverable_reservation handover_case_source (0,17) = Some claim \<and>
    reservation_binding claim = sample_binding 17 \<and> reservation_phase claim = Source_Pending"
  by (simp add: recoverable_reservation_def authoritative_reservation_state_def handover_case_defs
      finality_source_prefix_is_the_actual_parent_prefix sample_data_defs sample.protocol_definitions
      record_observation_def commit_reservation_event_def)

context source_attestation
begin

lemma the_successor_inherits_recovery_control_of_the_actual_pending_origin:
  "recovery_controller handover_case_after (0,17) = Some 8 \<and>
    recovery_controller handover_case_source (0,17) = Some 7"
proof -
  obtain claim where exact: "recoverable_reservation handover_case_source (0,17) = Some claim"
    "reservation_binding claim = sample_binding 17"
    using handover_case_retains_a_live_reservation by blast
  have target: "binding_asset (reservation_binding claim) = transfer_asset handover_case_proposal"
    using exact(2) by (simp add: handover_case_proposal_def sample_binding_def example_binding_def)
  have successor: "recovery_controller handover_case_after (0,17) = Some 8"
    using accepted_handover_transfers_exactly_the_live_claims(2)[OF handover_case_is_admitted, of "(0,17)"]
    by (simp add: exact(1) target handover_case_proposal_def)
  have old_owner: "owner_of_product handover_case_source 17 = Some 7"
    by (simp add: owner_of_product_def handover_case_defs)
  have former: "recovery_controller handover_case_source (0,17) = Some 7"
    unfolding recovery_controller_def exact(1)
    using old_owner target by (simp add: handover_case_proposal_def)
  show ?thesis using successor former by simp
qed

lemma the_new_owner_can_endorse_pending_recovery_and_the_old_owner_cannot:
  "let successor = \<lparr>endorsement_token = 8, endorsement_session = identity_case_proof 3 10\<rparr>;
       former = \<lparr>endorsement_token = 7, endorsement_session = identity_case_proof 2 10\<rparr>
    in recovery_has_current_endorsement identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory
         (\<lambda>_ _ _ _ _ _. True) 0 (0,17) (7,1) identity_case_payload successor handover_case_after \<and>
       \<not> recovery_has_current_endorsement identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory
         (\<lambda>_ _ _ _ _ _. True) 0 (0,17) (7,1) identity_case_payload former handover_case_after"
proof -
  have new_controller: "recovery_controller handover_case_after (0,17) = Some 8"
    using the_successor_inherits_recovery_control_of_the_actual_pending_origin by blast
  have live: "active_identity identity_case_directory (identity_case_user 8) (identity_case_proof 3 10) handover_case_after"
    using handover_case_closes_and_opens_on_one_transition
    by (simp add: active_identity_def identity_case_user_def identity_case_directory_def identity_case_proof_def)
  show ?thesis using new_controller live
    by (simp add: recovery_has_current_endorsement_def identity_case_user_def identity_case_directory_def Let_def)
qed

lemma raw_gate_blocks_an_actual_observation_that_would_expose_five_units:
  "read_at_identity_endpoint identity_case_directory (\<lambda>_ _ _ _. False) identity_case_directory (\<lambda>_ _ _ _. True)
      7 (identity_case_proof 1 9) 0 (Raw_Data (Source_Balance (0,17))) handover_case_world = Identity_Read_Rejected \<and>
    read_at_identity_endpoint identity_case_directory (\<lambda>_ _ _ _. True) identity_case_directory (\<lambda>_ _ _ _. True)
      7 (identity_case_proof 1 9) 0 (Raw_Data (Source_Balance (0,17))) handover_case_world = Authorized_Raw (Units_Value 5)"
proof -
  let ?query = "Raw_Data (Source_Balance (0,17))"
  let ?reads = "regulated_read_world handover_case_world"
  have access: "identity_read_allowed identity_case_directory (\<lambda>_ _ _ _. True) identity_case_directory (\<lambda>_ _ _ _. True)
      7 (identity_case_proof 1 9) 0 ?query (identity_source handover_case_world)"
    unfolding identity_case_has_the_actual_source
    by (simp add: identity_read_allowed_def active_identity_def current_product_cut_def handover_case_defs)
  have calls: "exact_calls (read_authority ?reads) = product_calls handover_case_source"
    using identity_case_has_the_actual_source
    by (simp add: exact_calls_def outcome_calls_def identity_source_def observed_product_source_def)
  have live: "read_authority_available ?reads"
    unfolding read_authority_available_def calls by (simp add: handover_case_defs)
  have source_value: "stored_query (Source_Balance (0,17)) (capture_snapshot (authoritative_read_core (read_authority ?reads))) =
    Units_Value 5"
    using source_debit_puts_five_into_pending
    by (simp add: authoritative_read_core_def calls capture_snapshot_def handover_case_defs)
  have auth: "identity_case_directory 7 = Some (identity_case_user 7)"
    by (simp add: identity_case_directory_def)
  have registered: "read_asset_registered (Source_Balance (0,17)) ?reads"
    by (simp add: read_asset_registered_def identity_source_def[symmetric]
        identity_case_has_the_actual_source handover_case_defs)
  have allow: "read_at_identity_endpoint identity_case_directory (\<lambda>_ _ _ _. True) identity_case_directory (\<lambda>_ _ _ _. True)
      7 (identity_case_proof 1 9) 0 ?query handover_case_world = Authorized_Raw (Units_Value 5)"
    using a_live_authorized_raw_read_observes_the_actual_current_source[OF auth access live registered] source_value by simp
  show ?thesis using allow
    by (simp add: read_at_identity_endpoint_def identity_read_allowed_def)
qed

end

end
