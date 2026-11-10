theory Write_Canary_Base
  imports "OIP_Product_Base.Lock_Endpoint_Examples"
    "OIP_Product.Durable_Execution"
    "OIP_Reference_Profile.Reference_Authority_Grants"
    "OIP_Reference_Profile.Reference_Response_Codes"
    "Preemptive_Lock_Correctness.Reservation_Frame"
begin

definition write_canary_command :: client_command where
  "write_canary_command = Client_Protocol 0 0 (Write_Intent (sample_request 17) 0 [(17,0)] 9)"

definition write_canary_grants :: reference_authority_inputs where
  "write_canary_grants = \<lparr>reference_epoch = 9,
    reference_grants = (\<lambda>endpoint. if endpoint = 0 then {(7,Normal_Lock_Entry,Ref_Write)} else {})\<rparr>"

definition write_canary_core :: "lock_context \<Rightarrow> finality_core" where
  "write_canary_core ctxt = (lock_example_core lock_example_held)\<lparr>core_contexts := (lock_example_contexts)(0 := ctxt)\<rparr>"

definition write_canary_world :: "lock_context \<Rightarrow> product_world" where
  "write_canary_world ctxt = (lock_example_world lock_example_held)\<lparr>product_calls := initial_call_machine (write_canary_core ctxt)\<rparr>"

definition write_canary_verified :: "product_principal \<Rightarrow> client_call_id \<Rightarrow> product_envelope \<Rightarrow>
    product_lock_credential option \<Rightarrow> bool" where
  "write_canary_verified who call_id envelope credential \<longleftrightarrow>
    who = 7 \<and> call_id = (7,1) \<and> envelope = lock_example_envelope write_canary_command \<and>
    credential = Some lock_example_token"

definition write_canary_submit :: "lock_context \<Rightarrow> product_world" where
  "write_canary_submit ctxt = sample.submit_lock_entry (reference_permitted_at write_canary_grants)
    write_canary_verified Normal_Lock_Entry 7 (7,1) (lock_example_envelope write_canary_command)
    (Some lock_example_token) (write_canary_world ctxt)"

lemma write_canary_current_entry:
  "product_new_call 7 (7,1) (lock_example_envelope write_canary_command) (write_canary_world ctxt)"
  "lock_envelope_admitted 7 (lock_example_envelope write_canary_command)
    (Some lock_example_token) (write_canary_world ctxt)"
  "reference_permitted_at write_canary_grants Normal_Lock_Entry 7 write_canary_command"
  by (simp_all add: write_canary_world_def write_canary_core_def write_canary_command_def
      product_new_call_def product_identity_bound_def lock_example_world_def lock_example_core_def
      lock_example_envelope_def initial_call_machine_def current_product_cut_def lock_example_token_def
      lock_envelope_admitted_def envelope_matches_request_def envelope_matches_binding_def
      lock_credential_matches_def authoritative_lock_view_def authoritative_lock_token_def
      authoritative_reservation_state_def product_lock_admitted_def current_lock_token_def
      write_canary_grants_def reference_permitted_at_def lock_example_public_defs)

lemma write_canary_dispatches_the_existing_product_command:
  "product_calls (write_canary_submit ctxt) = sample.finality_calls.run_calls
    [Begin_Call (7,1) write_canary_command, Dispatch_Call (7,1) write_canary_command]
    (initial_call_machine (write_canary_core ctxt))"
proof -
  let ?envelope = "lock_example_envelope write_canary_command"
  let ?world = "write_canary_world ctxt"
  have submit: "write_canary_submit ctxt = sample.product_submit (\<lambda>_ _ _. True) 7 (7,1) ?envelope ?world"
    unfolding write_canary_submit_def
  proof (rule sample.authorized_current_entry_uses_actual_submission)
    show "reference_permitted_at write_canary_grants Normal_Lock_Entry 7 (envelope_command ?envelope)"
      using write_canary_current_entry(3) by (simp add: lock_example_envelope_def)
    show "write_canary_verified 7 (7,1) ?envelope (Some lock_example_token)"
      by (simp add: write_canary_verified_def)
    show "lock_envelope_admitted 7 ?envelope (Some lock_example_token) ?world"
      by (rule write_canary_current_entry(2))
  qed
  have run: "product_calls (sample.product_submit (\<lambda>_ _ _. True) 7 (7,1) ?envelope ?world) =
    sample.finality_calls.run_calls [Begin_Call (7,1) (envelope_command ?envelope),
      Dispatch_Call (7,1) (envelope_command ?envelope)] (product_calls ?world)"
    by (rule sample.product_new_call_uses_authoritative_dispatch) (rule TrueI, rule write_canary_current_entry(1))
  show ?thesis unfolding submit run
    by (simp only: lock_example_envelope_def write_canary_world_def lock_example_world_def
        product_envelope.select_convs product_world.update_convs product_world.select_convs)
qed

definition write_canary_effect :: "lock_context \<Rightarrow> reservation_machine \<times> reservation_reply" where
  "write_canary_effect ctxt = write_asset_data (current_lock_view (write_canary_core ctxt) 0)
    (sample_request 17) 0 (vector_lookup [(17,0)]) 9 lock_example_held"

lemma write_canary_effect_projection:
  "call_authority_results (product_calls (write_canary_submit ctxt)) (7,1) =
    Some (write_canary_command, Protocol_Response (snd (write_canary_effect ctxt)), 0)"
  "authoritative_reservation_state (write_canary_submit ctxt) = machine_state (fst (write_canary_effect ctxt))"
proof -
  let ?execution = "sample.execute_finality_client write_canary_command (write_canary_core ctxt)"
  have parent: "core_parent (write_canary_core ctxt) = lock_example_held"
    by (simp add: write_canary_core_def lock_example_core_def)
  have reply: "snd ?execution = Protocol_Response (snd (write_canary_effect ctxt))"
    and state: "core_parent (fst ?execution) = fst (write_canary_effect ctxt)"
    by (simp_all add: write_canary_command_def sample.execute_finality_client_def sample.finality_step_def
        sample.invoke_protocol_def lift_protocol_result_def parent write_canary_effect_def Let_def)
  show "call_authority_results (product_calls (write_canary_submit ctxt)) (7,1) =
    Some (write_canary_command, Protocol_Response (snd (write_canary_effect ctxt)), 0)"
    by (simp only: write_canary_dispatches_the_existing_product_command
        sample.finality_calls.initial_dispatch_projection(2) fun_upd_same reply)
  show "authoritative_reservation_state (write_canary_submit ctxt) = machine_state (fst (write_canary_effect ctxt))"
    by (simp only: authoritative_reservation_state_def write_canary_dispatches_the_existing_product_command
        sample.finality_calls.initial_dispatch_projection(1) state)
qed

lemma write_canary_current_context:
  "current_lock_view (write_canary_core ctxt) 0 = ctxt\<lparr>lock_metadata := sample_metadata ACTIVE\<rparr>"
  by (simp add: current_lock_view_def write_canary_core_def lock_example_core_def initial_finality_core_def)

lemma write_canary_fixture_success:
  "snd (write_canary_effect (sample_source_context ACTIVE)) = Data_Updated"
proof -
  have view: "current_lock_view (write_canary_core (sample_source_context ACTIVE)) 0 = sample_source_context ACTIVE"
    by (simp add: write_canary_current_context sample_source_context_def sample_context_def)
  have held: "lock_example_held = sample_held_for_write"
    by (simp only: lock_example_held_def sample_held_for_write_def)
  have versions: "vector_lookup [(17,0)] = (\<lambda>_. 0)"
    by (rule ext) (simp add: vector_lookup_def)
  show ?thesis
    by (simp only: write_canary_effect_def view held versions current_write_control_activates[THEN conjunct1])
qed

lemma write_canary_primary_asset:
  "binding_asset (request_binding (sample_request 17)) = 17"
  by (simp add: sample_request_def sample_binding_def example_binding_def)

lemma write_canary_initial_version:
  "asset_version (machine_state lock_example_held) 17 = 0"
  using successful_write_current_owner_and_version[OF write_canary_fixture_success[unfolded write_canary_effect_def]]
  by (auto simp: write_canary_primary_asset vector_lookup_def)

lemma write_canary_success_projects:
  assumes success: "snd (write_canary_effect ctxt) = Data_Updated"
  shows "call_authority_results (product_calls (write_canary_submit ctxt)) (7,1) =
    Some (write_canary_command, Protocol_Response Data_Updated, 0)"
  "asset_value (authoritative_reservation_state (write_canary_submit ctxt)) 17 = 9"
  "asset_version (authoritative_reservation_state (write_canary_submit ctxt)) 17 =
    Suc (asset_version (machine_state lock_example_held) 17)"
proof -
  have changed: "asset_value (machine_state (fst (write_canary_effect ctxt))) 17 = 9 \<and>
    asset_version (machine_state (fst (write_canary_effect ctxt))) 17 = Suc (asset_version (machine_state lock_example_held) 17)"
    using successful_write_value_and_version[OF success[unfolded write_canary_effect_def]]
    by (simp only: write_canary_effect_def write_canary_primary_asset)
  show "call_authority_results (product_calls (write_canary_submit ctxt)) (7,1) =
    Some (write_canary_command, Protocol_Response Data_Updated, 0)"
    by (simp only: write_canary_effect_projection(1) success)
  show "asset_value (authoritative_reservation_state (write_canary_submit ctxt)) 17 = 9"
    by (simp only: write_canary_effect_projection(2) changed[THEN conjunct1])
  show "asset_version (authoritative_reservation_state (write_canary_submit ctxt)) 17 =
    Suc (asset_version (machine_state lock_example_held) 17)"
    by (simp only: write_canary_effect_projection(2) changed[THEN conjunct2])
qed

lemmas held_write_commits_value_version_and_result = write_canary_success_projects[OF write_canary_fixture_success]

definition write_canary_denied_context :: lock_context where
  "write_canary_denied_context = (sample_source_context ACTIVE)\<lparr>lock_write_permissions := {}\<rparr>"

lemma the_same_write_without_the_value_permission_has_no_effect:
  "call_authority_results (product_calls (write_canary_submit write_canary_denied_context)) (7,1) =
    Some (write_canary_command, Protocol_Response Request_Rejected, 0)"
  "authoritative_reservation_state (write_canary_submit write_canary_denied_context) = machine_state lock_example_held"
proof -
  have denied: "snd (write_canary_effect write_canary_denied_context) = Request_Rejected"
    by (simp add: write_canary_effect_def write_canary_current_context write_canary_denied_context_def
        write_asset_data_def record_observation_def)
  have frame: "machine_state (fst (write_canary_effect write_canary_denied_context)) = machine_state lock_example_held"
    using rejected_write_preserves_state_and_journal[OF denied[unfolded write_canary_effect_def], THEN conjunct1]
    by (simp only: write_canary_effect_def)
  show "call_authority_results (product_calls (write_canary_submit write_canary_denied_context)) (7,1) =
    Some (write_canary_command, Protocol_Response Request_Rejected, 0)"
    by (simp only: write_canary_effect_projection(1) denied)
  show "authoritative_reservation_state (write_canary_submit write_canary_denied_context) = machine_state lock_example_held"
    by (simp only: write_canary_effect_projection(2) frame)
qed

lemma weakening_only_the_value_membership_test:
  "snd (write_asset_data (ctxt\<lparr>lock_write_permissions := UNIV\<rparr>) request generation versions value machine) =
    Data_Updated \<longleftrightarrow>
    owns_current_reservation ctxt request generation versions (machine_state machine) \<and>
    phase_at (machine_state machine) (binding_key (request_binding request)) = Some Reservation_Held"
  by (simp add: successful_write_guard owns_current_reservation_def owns_recorded_reservation_def required_footprint_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms write_canary_current_entry write_canary_dispatches_the_existing_product_command
      held_write_commits_value_version_and_result the_same_write_without_the_value_permission_has_no_effect
      weakening_only_the_value_membership_test})
  then () else error "Unexpected oracle in the Write fixture canary"
\<close>

end
