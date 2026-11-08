theory Recovery_Records
  imports Owner_Recovery_Effect
begin

section \<open>Retained source fields and fresh runtime construction\<close>

record retained_call_source =
  retained_authority :: product_durable
  retained_genesis :: finality_core
  retained_core :: finality_core
  retained_log :: "(client_command, finality_reply, nat \<times> lock_context) authority_call_entry list"
  retained_results :: "client_call_id \<Rightarrow> (client_command \<times> finality_reply \<times> nat) option"
  retained_invocations :: "client_call_id \<Rightarrow> (client_command \<times> nat) option"
  retained_completions :: "client_call_id \<Rightarrow> finality_reply option"
  retained_call_history :: "(client_command, finality_reply) client_call_event list"

definition capture_retained_source where
  "capture_retained_source s =
    (let calls = product_calls s in
      \<lparr>retained_authority = product_durable s, retained_genesis = call_genesis calls,
       retained_core = call_authority_state calls, retained_log = call_authority_log calls,
       retained_results = call_authority_results calls, retained_invocations = call_invocations calls,
       retained_completions = call_completions calls, retained_call_history = call_history calls\<rparr>)"

definition reopen_retained_source where
  "reopen_retained_source connection retained =
    \<lparr>product_durable = retained_authority retained, product_calls =
      \<lparr>call_genesis = retained_genesis retained, call_authority_state = retained_core retained,
       call_authority_log = retained_log retained, call_authority_results = retained_results retained,
       call_invocations = retained_invocations retained, call_completions = retained_completions retained,
       call_local_results = (\<lambda>_. None), call_local_status = Endpoint_Up, call_connection = connection,
       call_history = retained_call_history retained\<rparr>\<rparr>"

lemma reopened_source_has_no_old_process_or_response_cache:
  "call_local_results (product_calls (reopen_retained_source connection retained)) = (\<lambda>_. None)"
  "call_local_status (product_calls (reopen_retained_source connection retained)) = Endpoint_Up"
  "call_connection (product_calls (reopen_retained_source connection retained)) = connection"
  by (simp_all add: reopen_retained_source_def)

lemma source_round_trip_retains_every_durable_field:
  "capture_retained_source (reopen_retained_source connection retained) = retained"
  by (cases retained) (simp add: capture_retained_source_def reopen_retained_source_def Let_def)

record retained_product =
  retained_source :: retained_call_source
  retained_outcomes :: "client_call_id \<Rightarrow> product_result_entry option"
  retained_completed_ids :: "client_call_id set"
  retained_debits :: "source_key \<Rightarrow> (transfer_binding \<times> nat) option"
  retained_decisions :: "source_key \<Rightarrow> product_origin_decision option"
  retained_settlement_target :: nat
  retained_secondary :: "settlement_identity \<Rightarrow> product_secondary_job option"
  retained_provider :: nat
  retained_issued_orders :: "source_key \<Rightarrow> product_legal_order option"
  retained_legal_events :: "source_key \<Rightarrow> product_legal_event option"
  retained_freezes :: "product_asset \<Rightarrow> source_key option"
  retained_seizures :: "product_asset \<Rightarrow> source_key option"
  retained_legal_receipts :: "client_call_id \<Rightarrow> legal_request_receipt option"
  retained_spend_receipts :: "client_call_id \<Rightarrow> governed_spend_receipt option"

definition capture_retained_product where
  "capture_retained_product s =
    (let governed = regulated_orders s; legal = governed_legal governed; reads = legal_reads legal;
         authority = read_authority reads; origins = settlement_primary authority; outcomes = origin_outcomes origins
     in \<lparr>retained_source = capture_retained_source (outcome_source outcomes), retained_outcomes = outcome_entries outcomes,
         retained_completed_ids = outcome_completed outcomes, retained_debits = origin_debits origins,
         retained_decisions = origin_decisions origins, retained_settlement_target = settlement_target authority,
         retained_secondary = settlement_jobs authority, retained_provider = read_provider reads,
         retained_issued_orders = issued_legal_orders legal, retained_legal_events = committed_legal_events legal,
         retained_freezes = active_freeze_event legal, retained_seizures = active_seizure_event legal,
         retained_legal_receipts = legal_receipts governed, retained_spend_receipts = spend_receipts s\<rparr>)"

definition reopen_retained_product where
  "reopen_retained_product connection retained =
    (let outcomes = \<lparr>outcome_source = reopen_retained_source connection (retained_source retained),
           outcome_entries = retained_outcomes retained, outcome_completed = retained_completed_ids retained\<rparr>;
         origins = \<lparr>origin_outcomes = outcomes, origin_debits = retained_debits retained,
           origin_decisions = retained_decisions retained\<rparr>;
         authority = \<lparr>settlement_primary = origins, settlement_target = retained_settlement_target retained,
           settlement_jobs = retained_secondary retained\<rparr>;
         reads = initial_product_reads (retained_provider retained) authority;
         legal = \<lparr>legal_reads = reads, issued_legal_orders = retained_issued_orders retained,
           committed_legal_events = retained_legal_events retained, active_freeze_event = retained_freezes retained,
           active_seizure_event = retained_seizures retained\<rparr>
     in \<lparr>regulated_orders = \<lparr>governed_legal = legal, legal_receipts = retained_legal_receipts retained\<rparr>,
         spend_receipts = retained_spend_receipts retained\<rparr>)"

lemma product_round_trip_preserves_the_durable_projection:
  "capture_retained_product (reopen_retained_product connection retained) = retained"
  by (cases retained) (simp add: capture_retained_product_def reopen_retained_product_def initial_product_reads_def
      source_round_trip_retains_every_durable_field Let_def)

lemma recovery_projection_supplies_the_exact_source:
  "identity_source (reopen_retained_product connection retained) = reopen_retained_source connection (retained_source retained)"
  by (simp add: identity_source_def regulated_read_world_def observed_product_source_def reopen_retained_product_def
      initial_product_reads_def Let_def)

lemma reopened_runtime_does_not_use_erased_cache_entries:
  "query_cache (regulated_read_world (reopen_retained_product connection retained)) = (\<lambda>_. None)"
  by (simp add: regulated_read_world_def reopen_retained_product_def initial_product_reads_def Let_def)

end
