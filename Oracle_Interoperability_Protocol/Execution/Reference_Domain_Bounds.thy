theory Reference_Domain_Bounds
  imports Reference_Trace_Consumers "OIP_Product.Freeze_Interval"
begin

lemma an_actual_thaw_reopens_the_ordinary_mode_gate_for_an_eligible_request:
  assumes valid: "valid_state state" and thaw: "sync issuer action asset state = Some next_state"
    and before: "get_reg_state state observer asset = Some mode"
    and allowed: "(mode,action) \<in> {(FROZEN,UNFREEZE),(SEIZED,RELEASE)}"
  shows "get_reg_state next_state observer asset = Some ACTIVE"
    "\<not> ordinary_transfer_allowed True True mode"
    "ordinary_transfer_allowed True True ACTIVE"
proof -
  obtain source_mode where source: "get_reg_state state issuer asset = Some source_mode"
    using thaw by (auto simp: sync_def Let_def split: option.splits)
  have same: "source_mode = mode" using valid source before unfolding valid_state_def consistent_state_def by blast
  have transition: "reg_transition source_mode action = Some ACTIVE" using same allowed by auto
  have connected: "observer \<in> connected_chains state asset"
    using before by (auto simp: connected_chains_def asset_exists_def get_reg_state_def split: option.splits)
  show "get_reg_state next_state observer asset = Some ACTIVE"
    by (rule regulatory_homomorphism[OF source transition thaw connected])
  show "\<not> ordinary_transfer_allowed True True mode"
    using allowed by (auto simp: ordinary_transfer_allowed_def)
  show "ordinary_transfer_allowed True True ACTIVE" by (simp add: ordinary_transfer_allowed_def)
qed

definition legal_gate_and_external_finding where
  "legal_gate_and_external_finding grant verified stage entry actor order state external_finding =
     (legal_admission_at_cut grant verified stage entry actor order state, external_finding order)"

lemma the_same_verified_order_gate_cannot_decide_an_external_finding:
  assumes admitted: "legal_admission_at_cut grant verified stage entry actor order state = Legal_Admit"
  shows "legal_gate_and_external_finding grant verified stage entry actor order state (\<lambda>_. False) = (Legal_Admit,False)"
    "legal_gate_and_external_finding grant verified stage entry actor order state (\<lambda>_. True) = (Legal_Admit,True)"
    "legal_admission_at_cut grant (\<lambda>_ _ _ _. False) stage entry actor order state = Legal_Refuse Invalid_Legal_Authority"
  using admitted by (simp_all add: legal_gate_and_external_finding_def legal_admission_at_cut_def)

context source_attestation
begin

lemma identical_ledger_and_request_can_have_different_observations_when_the_identity_supplier_changes:
  assumes active: "active_identity directory identity proof (identity_source live)"
    and signature: "verify_read identity proof target (Owner_Data asset)"
    and grant: "policy identity target (Owner_Data asset) (proof_epoch proof)"
    and ready: "read_authority_available (regulated_read_world live)"
  shows "read_at_identity_endpoint directory policy (\<lambda>_. Some identity) verify_read token proof target (Owner_Data asset) live =
         Authorized_Owner (product_owners (product_durable (identity_source live)) asset)"
    "read_at_identity_endpoint directory policy (\<lambda>_. None) verify_read token proof target (Owner_Data asset) live = Identity_Read_Rejected"
proof -
  have permitted: "identity_read_allowed directory policy (\<lambda>_. Some identity) verify_read token proof target
      (Owner_Data asset) (identity_source live)"
    using active signature grant by (simp add: identity_read_allowed_def)
  show "read_at_identity_endpoint directory policy (\<lambda>_. Some identity) verify_read token proof target (Owner_Data asset) live =
         Authorized_Owner (product_owners (product_durable (identity_source live)) asset)"
    by (rule authorized_owner_read_uses_the_same_committed_token_owner[OF _ permitted ready]) simp
  show "read_at_identity_endpoint directory policy (\<lambda>_. None) verify_read token proof target (Owner_Data asset) live = Identity_Read_Rejected"
    by (simp add: read_at_identity_endpoint_def identity_read_allowed_def)
qed

lemma same_signed_read_scope_does_not_make_two_different_authorized_raw_values_indistinguishable:
  assumes token: "authenticate token = Some identity"
    and first: "identity_read_allowed directory policy authenticate verify_read token proof target (Raw_Data query) (identity_source left)"
      "read_authority_available (regulated_read_world left)" "read_asset_registered query (regulated_read_world left)"
    and second: "identity_read_allowed directory policy authenticate verify_read token proof target (Raw_Data query) (identity_source right)"
      "read_authority_available (regulated_read_world right)" "read_asset_registered query (regulated_read_world right)"
    and differing: "stored_query query (capture_snapshot (authoritative_read_core (read_authority (regulated_read_world left)))) \<noteq>
      stored_query query (capture_snapshot (authoritative_read_core (read_authority (regulated_read_world right))))"
  shows "read_at_identity_endpoint directory policy authenticate verify_read token proof target (Raw_Data query) left \<noteq>
     read_at_identity_endpoint directory policy authenticate verify_read token proof target (Raw_Data query) right"
  using differing a_live_authorized_raw_read_observes_the_actual_current_source[OF token first]
    a_live_authorized_raw_read_observes_the_actual_current_source[OF token second] by simp

end

context reference_trace_consumer
begin

theorem a_reference_ack_can_complete_without_an_external_confirmation_for_that_settlement:
  fixes before prefix initial
  defines "before \<equiv> run_reference_word execute prefix initial"
  assumes start: "reference_service_contract registered genesis initial"
    and stored: "retained_secondary (reference_product before) (ack_settlement_key ack) = Some job"
    and exact: "verified_ack ack" "exact_secondary_ack ack job" "secondary_attempts job > 0"
  shows "let observation = (serve connection (Service_Maintenance (Exact_Acknowledge ack)) None before,
         {} :: settlement_identity set)
       in snd (fst observation) = Some (Scheduled_Settlement (Settlement_Changed True)) \<and>
          ack_settlement_key ack \<notin> snd observation"
  using an_ack_after_any_reference_prefix_can_change_only_its_exact_queue_and_keeps_primary_decisions
    [OF start, where prefix=prefix and connection=connection and ack=ack] stored exact
  by (simp add: before_def step_settlement_slot_def Let_def)

theorem an_actual_local_handover_need_not_change_an_external_registry_entry:
  fixes before prefix initial
  defines "before \<equiv> run_reference_word execute prefix initial"
  assumes step: "serve connection (Service_Handover owner_token successor_token maintainer proposal) supplied before =
         (after, Some (Scheduled_Endpoint (Service_Handover_Result True)))"
    and external: "external_registry (transfer_asset proposal) = Some (transfer_previous proposal)"
    and distinct: "transfer_previous proposal \<noteq> transfer_successor proposal"
  shows "let product_and_registry = (fst (serve connection (Service_Handover owner_token successor_token maintainer proposal)
         supplied before), external_registry)
       in product_owners (retained_authority (retained_source (reference_product (fst product_and_registry)))) (transfer_asset proposal) \<noteq>
          snd product_and_registry (transfer_asset proposal)"
  using the_actual_reference_handover_updates_owner_sessions_and_grants_at_one_epoch(1)
    [OF step[unfolded actual_execute reference_service_input.select_convs]] step external distinct
  by (simp add: Let_def)

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms an_actual_thaw_reopens_the_ordinary_mode_gate_for_an_eligible_request
    the_same_verified_order_gate_cannot_decide_an_external_finding
    source_attestation.identical_ledger_and_request_can_have_different_observations_when_the_identity_supplier_changes
    source_attestation.same_signed_read_scope_does_not_make_two_different_authorized_raw_values_indistinguishable
    reference_trace_consumer.a_reference_ack_can_complete_without_an_external_confirmation_for_that_settlement
    reference_trace_consumer.an_actual_local_handover_need_not_change_an_external_registry_entry})
  then () else error "Unexpected oracle in domain bounds"
\<close>

end
