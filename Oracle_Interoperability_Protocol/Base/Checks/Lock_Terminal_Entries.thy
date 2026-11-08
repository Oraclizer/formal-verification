theory Lock_Terminal_Entries
  imports Lock_Endpoint_Examples Lock_Settlement_Examples
begin

definition terminal_example_world where
  "terminal_example_world s = (lock_example_world (core_parent s))
    \<lparr>product_calls := initial_call_machine s\<rparr>"

definition terminal_example_envelope where
  "terminal_example_envelope event command = (lock_example_envelope command)
    \<lparr>envelope_origin := (0,event), envelope_asset := event\<rparr>"

definition terminal_example_credential where
  "terminal_example_credential event = lock_example_token\<lparr>credential_origin := (0,event),
    credential_token := (credential_token lock_example_token)\<lparr>token_asset := event\<rparr>\<rparr>"

definition terminal_example_submit where
  "terminal_example_submit entry event command = sample.submit_lock_entry
    (\<lambda>_ _ _. True) (\<lambda>_ _ _ _. True) entry 7 (7,1) (terminal_example_envelope event command)
    (Some (terminal_example_credential event)) (terminal_example_world (finality_sample_certified event))"

lemma terminal_example_submits_the_actual_consumer:
  assumes "lock_envelope_admitted 7 (terminal_example_envelope event command)
    (Some (terminal_example_credential event)) (terminal_example_world (finality_sample_certified event))"
    and "product_new_call 7 (7,1) (terminal_example_envelope event command)
      (terminal_example_world (finality_sample_certified event))"
  shows "call_authority_results (product_calls (terminal_example_submit entry event command)) (7,1) =
    Some (command, snd (sample.execute_finality_client command (finality_sample_certified event)), 0)"
proof -
  let ?env = "terminal_example_envelope event command"
  let ?world = "terminal_example_world (finality_sample_certified event)"
  have entry: "terminal_example_submit entry event command = sample.product_submit (\<lambda>_ _ _. True) 7 (7,1) ?env ?world"
    unfolding terminal_example_submit_def
    by (rule sample.authorized_current_entry_uses_actual_submission) (rule TrueI, rule TrueI, rule assms(1))
  have run: "product_calls (sample.product_submit (\<lambda>_ _ _. True) 7 (7,1) ?env ?world) =
    sample.finality_calls.run_calls [Begin_Call (7,1) (envelope_command ?env), Dispatch_Call (7,1) (envelope_command ?env)]
      (product_calls ?world)"
    by (rule sample.product_new_call_uses_authoritative_dispatch) (rule TrueI, rule assms(2))
  have initial: "product_calls ?world = initial_call_machine (finality_sample_certified event)"
    by (simp add: terminal_example_world_def)
  have command: "envelope_command ?env = command"
    by (simp add: terminal_example_envelope_def lock_example_envelope_def)
  show ?thesis unfolding entry run initial command
    by (simp only: sample.finality_calls.initial_dispatch_projection(2) fun_upd_same)
qed

lemmas terminal_product_gate_defs = terminal_example_envelope_def terminal_example_credential_def
  terminal_example_world_def lock_example_world_def lock_example_envelope_def lock_example_token_def
  initial_call_machine_def lock_envelope_admitted_def envelope_matches_request_def envelope_matches_binding_def
  lock_credential_matches_def authoritative_lock_view_def authoritative_lock_token_def authoritative_reservation_state_def
  product_lock_admitted_def current_lock_token_def current_product_cut_def product_new_call_def product_identity_bound_def

lemmas terminal_public_fixture_defs = terminal_certificate_publishes_the_actual_parent_evidence
  sample_data_defs sample_auth_defs sample.protocol_definitions record_observation_def commit_reservation_event_def Let_def

lemma product_confirmed_consumer_credits_at_the_bound_entry:
  "call_authority_results (product_calls (terminal_example_submit entry 17
    (Client_Protocol 2 0 (Deliver_Intent Bypass_Route (sample_request 17))))) (7,1) =
    Some (Client_Protocol 2 0 (Deliver_Intent Bypass_Route (sample_request 17)),
      Protocol_Response (Delivery_Response (New_Credit (sample_binding 17))), 0)"
proof -
  let ?command = "Client_Protocol 2 0 (Deliver_Intent Bypass_Route (sample_request 17))"
  have gate: "lock_envelope_admitted 7 (terminal_example_envelope 17 ?command)
    (Some (terminal_example_credential 17)) (terminal_example_world (finality_sample_certified 17))"
    by (simp add: terminal_product_gate_defs terminal_public_fixture_defs)
  have fresh: "product_new_call 7 (7,1) (terminal_example_envelope 17 ?command)
    (terminal_example_world (finality_sample_certified 17))"
    by (simp add: terminal_product_gate_defs sample_request_def)
  show ?thesis unfolding terminal_example_submits_the_actual_consumer[OF gate fresh]
    by (simp only: normal_bypass_credit_uses_the_terminal_record)
qed

lemma product_reversed_consumer_refunds_at_the_bound_entry:
  "call_authority_results (product_calls (terminal_example_submit entry 22
    (Client_Protocol 0 0 (Return_Intent (sample_request 22) 0 [])))) (7,1) =
    Some (Client_Protocol 0 0 (Return_Intent (sample_request 22) 0 []), Protocol_Response Reservation_Released, 0)"
proof -
  let ?command = "Client_Protocol 0 0 (Return_Intent (sample_request 22) 0 [])"
  have gate: "lock_envelope_admitted 7 (terminal_example_envelope 22 ?command)
    (Some (terminal_example_credential 22)) (terminal_example_world (finality_sample_certified 22))"
    by (simp add: terminal_product_gate_defs terminal_public_fixture_defs)
  have fresh: "product_new_call 7 (7,1) (terminal_example_envelope 22 ?command)
    (terminal_example_world (finality_sample_certified 22))"
    by (simp add: terminal_product_gate_defs sample_request_def)
  show ?thesis unfolding terminal_example_submits_the_actual_consumer[OF gate fresh]
    by (simp only: normal_reverse_returns_the_recorded_source)
qed

end
