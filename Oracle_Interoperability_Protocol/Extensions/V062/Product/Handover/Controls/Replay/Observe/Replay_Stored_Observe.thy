theory Replay_Stored_Observe
  imports "OIP_V062_P13_Replay_Stored_Outcome_Repair.Replay_Stored_Outcome"
begin

text \<open>This observation reads the logical outcome. The wire arrival
and its binding record are outside this observation's state scope.\<close>

lemma pro_exact_observation_is_the_original_computed_outcome:
  "observe_collection pro_verified 7 ((7,1)::client_call_id) prp_original_payload pro_completed = Collected pro_original_outcome"
proof -
  let ?id = "((7,1)::client_call_id)"
  have source: "outcome_source pro_completed = hf_reserved"
    by (rule pro_completed_retains_the_produced_source_and_entry(1))
  have access: "result_access_bound pro_verified 7 ?id prp_original_payload pro_completed"
    unfolding result_access_bound_def source pro_verified_def
    by (rule conjI[OF TrueI pro_reserve_identity_is_bound_before_and_after_submission(2)])
  have access_test: "(\<not> result_access_bound pro_verified 7 ?id prp_original_payload pro_completed) = False"
    using access by blast
  have up: "call_local_status (product_calls (outcome_source pro_completed)) = Endpoint_Up"
    unfolding source by (rule pro_reserved_endpoint_is_up)
  have up_test: "(call_local_status (product_calls (outcome_source pro_completed)) \<noteq> Endpoint_Up) = False"
    unfolding up by simp
  have entry: "outcome_entries pro_completed ?id = Some pro_original_entry"
    by (rule pro_completed_retains_the_produced_source_and_entry(2))
  have exact: "result_payload pro_original_entry = prp_original_payload"
    and outcome: "result_outcome pro_original_entry = pro_original_outcome"
    by (simp_all add: pro_original_entry_def)
  have ready: "result_completion_ready pro_original_entry pro_completed"
    by (rule pro_original_reserve_result_needs_no_terminal_publication_to_be_read)
  have ready_test: "result_completion_ready pro_original_entry pro_completed = True"
    using ready by (rule iffD2[OF eq_True])
  show ?thesis
    unfolding observe_collection_def
    by (simp only: access_test up_test entry option.case exact ready_test outcome
        simp_thms if_False if_True)
qed

lemma pro_altered_payload_cannot_observe_that_original_result:
  "observe_collection pro_verified 7 ((7,1)::client_call_id) prp_changed_payload pro_completed = Collection_Rejected"
proof -
  have entry: "outcome_entries pro_completed (7,1) = Some pro_original_entry"
    by (rule pro_completed_retains_the_produced_source_and_entry(2))
  have original: "result_payload pro_original_entry = prp_original_payload"
    by (simp add: pro_original_entry_def)
  have changed: "result_payload pro_original_entry \<noteq> prp_changed_payload"
    unfolding original
    by (rule not_sym[OF prp_changed_payload_is_a_distinct_request])
  have available: "call_local_status (product_calls (outcome_source pro_completed)) = Endpoint_Up"
    unfolding pro_completed_retains_the_produced_source_and_entry(1)
    by (rule pro_reserved_endpoint_is_up)
  show ?thesis
    by (rule conflicting_payload_is_observably_rejected[OF entry changed available])
qed

thm_oracles pro_submit_constructs_the_entry_from_the_actual_reserve_reply
  pro_fresh_completion_only_marks_the_actual_completed_identifier
  pro_exact_observation_is_the_original_computed_outcome pro_altered_payload_cannot_observe_that_original_result

ML \<open>
  if null (Thm_Deps.all_oracles @{thms pro_submit_constructs_the_entry_from_the_actual_reserve_reply
      pro_fresh_completion_only_marks_the_actual_completed_identifier
      pro_exact_observation_is_the_original_computed_outcome pro_altered_payload_cannot_observe_that_original_result})
  then writeln "P13_STORED_OUTCOME_ORACLES_EMPTY"
  else error "Unexpected oracle in stored outcome observation"
\<close>

end
