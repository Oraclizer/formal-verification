theory Outcome_Gates
  imports Call_Outcomes
begin

context source_attestation
begin

lemma first_connected_call_records_its_public_result:
  assumes "result_access_bound verified who call_id payload s"
    and "outcome_entries s call_id = None"
    and "call_invocations (product_calls (outcome_source s)) call_id = None \<and>
      call_authority_results (product_calls (outcome_source s)) call_id = None \<and>
      call_connection (product_calls (outcome_source s)) = Authority_Connected \<and>
      call_local_status (product_calls (outcome_source s)) = Endpoint_Up"
  shows "let next = lock_product_step permitted (\<lambda>_ _ _ _. True) maintainers registered
       (Lock_Submit entry who call_id (payload_envelope payload) (payload_credential payload)) (outcome_source s);
     raw = call_authority_results (product_calls next) call_id
   in submit_authoritative_call permitted verified maintainers registered entry who call_id payload s =
     store_product_result call_id payload
       (case raw of None \<Rightarrow> Authority_Rejected | Some (_,reply,_) \<Rightarrow> normalized_authority_reply reply) next s"
  using assms by (simp del: lock_product_step.simps
      add: submit_authoritative_call_def submit_new_authoritative_call_def Let_def split: option.splits prod.splits)

lemma an_unavailable_unissued_call_records_an_outcome_without_execution:
  assumes access: "result_access_bound verified who call_id payload s"
    and fresh: "outcome_entries s call_id = None"
    and not_invoked: "call_invocations (product_calls (outcome_source s)) call_id = None"
    and no_result: "call_authority_results (product_calls (outcome_source s)) call_id = None"
    and up: "call_local_status (product_calls (outcome_source s)) = Endpoint_Up"
    and unavailable: "call_connection (product_calls (outcome_source s)) = Authority_Disconnected"
  shows "submit_authoritative_call permitted verified maintainers registered entry who call_id payload s =
    store_product_result call_id payload Authority_Unavailable (outcome_source s) s"
  using assms
  by (simp add: submit_authoritative_call_def submit_new_authoritative_call_def Let_def)

lemma crashed_endpoint_cannot_record_an_unissued_call:
  "call_local_status (product_calls (outcome_source s)) = Endpoint_Down \<Longrightarrow>
    submit_authoritative_call permitted verified maintainers registered entry who call_id payload s = s"
  by (simp add: submit_authoritative_call_def submit_new_authoritative_call_def Let_def)

end

lemma final_effect_cannot_complete_while_its_lock_is_held:
  assumes effect: "final_effect_key (envelope_command (payload_envelope (result_payload recorded))) (result_outcome recorded) = Some key"
    and held: "asset_owner (machine_state (core_parent (call_authority_state (product_calls (outcome_source s)))))
      (envelope_asset (payload_envelope (result_payload recorded))) = Some key"
  shows "\<not> result_completion_ready recorded s"
  using assms by (simp add: result_completion_ready_def Let_def)

lemma final_effect_cannot_complete_before_primary_publication:
  assumes effect: "final_effect_key (envelope_command (payload_envelope (result_payload recorded))) (result_outcome recorded) = Some key"
    and unpublished: "key \<notin> core_published (call_authority_state (product_calls (outcome_source s)))"
  shows "\<not> result_completion_ready recorded s"
  using assms by (simp add: result_completion_ready_def Let_def)

end
