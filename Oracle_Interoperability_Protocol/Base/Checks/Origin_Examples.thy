theory Origin_Examples
  imports "../Exact_Source_Safety" Propagation_Examples
begin

definition origin_example_funded where
  "origin_example_funded = (queue_example_primary call_example_ready)\<lparr>
    origin_debits := (\<lambda>_. None)((0,17) := Some (sample_binding 17, 9))\<rparr>"

definition origin_example_claim where
  "origin_example_claim epoch = \<lparr>payload_envelope = terminal_example_envelope 17 (Client_Terminal (sample_certificate 17)),
    payload_credential = None, payload_origin_epoch = epoch\<rparr>"

lemma repeated_exact_terminal_binding_is_admissible:
  "origin_command_allowed origin_example_funded (payload_envelope (origin_example_claim 9)) 9
     (Client_Terminal (sample_certificate 17))"
  by (simp add: origin_example_funded_def origin_example_claim_def queue_example_primary_def queue_example_decision_def
      terminal_admission_def decision_matches_def call_example_certificate_fields Let_def)

lemma same_event_with_a_different_origin_epoch_cannot_change_public_state:
  "outcome_source (origin_outcomes (sample.submit_origin_call permitted verified maintainers registered entry 7 (7,1)
     (origin_example_claim 10) origin_example_funded)) = outcome_source (origin_outcomes origin_example_funded)"
  by (rule sample.conflicting_origin_binding_cannot_change_public_state)
    (simp add: origin_example_claim_def origin_example_funded_def terminal_example_envelope_def lock_example_envelope_def
      terminal_admission_def decision_matches_def queue_example_primary_def queue_example_decision_def
      call_example_certificate_fields Let_def)

text \<open>The two independent invocations below start from separate copies of
  the same certified, unpaid source. This is a control for removing the common
  authority: each copy independently records a newly credited result.\<close>

lemma splitting_the_authority_allows_two_new_credit_results:
  "let command = Client_Protocol 2 0 (Deliver_Intent Bypass_Route (sample_request 17));
       first = terminal_example_submit Normal_Lock_Entry 17 command;
       second = terminal_example_submit Adapter_Lock_Entry 17 command;
       expected = Some (command, Protocol_Response (Delivery_Response (New_Credit (sample_binding 17))), 0)
    in call_authority_results (product_calls first) (7,1) = expected \<and>
       call_authority_results (product_calls second) (7,1) = expected"
  by (simp only: Let_def product_confirmed_consumer_credits_at_the_bound_entry)

end
