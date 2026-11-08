theory Recovery_Ordinary_Completion_Projection
  imports Recovery_Ordinary_Projection
begin

lemma ordinary_collection_ignores_only_the_completed_set:
  "observe_collection verified actor call_id payload (outcomes\<lparr>outcome_completed := completed\<rparr>) =
    observe_collection verified actor call_id payload outcomes"
proof (cases "outcome_entries outcomes call_id")
  case None
  then show ?thesis by (simp add: observe_collection_def result_access_bound_def)
next
  case (Some saved)
  have ready: "result_completion_ready saved (outcomes\<lparr>outcome_completed := completed\<rparr>) =
      result_completion_ready saved outcomes"
    by (simp add: result_completion_ready_def Let_def)
  show ?thesis using Some ready
    by (simp add: observe_collection_def result_access_bound_def split: if_splits)
qed

lemma ordinary_completion_preserves_the_collection_observation:
  "observe_collection verified actor call_id payload
      (fst (complete_authoritative_result verified actor call_id payload outcomes)) =
    observe_collection verified actor call_id payload outcomes"
  by (simp add: complete_authoritative_result_def ordinary_collection_ignores_only_the_completed_set
    split: option.splits if_splits)

context source_attestation
begin

lemma ordinary_finishing_preserves_the_collection_observation:
  "observe_collection verified actor call_id payload
      (current_product_outcomes (fst (finish_durable_execution verified actor
        (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect claimed_actor call_id payload))) s))) =
    observe_collection verified actor call_id payload (current_product_outcomes s)"
  by (cases "unclaimed_regulated_call s call_id")
    (simp_all add: Let_def ordinary_completion_preserves_the_collection_observation)

lemma ordinary_finishing_preserves_its_regulated_claim_gate:
  "unclaimed_regulated_call (fst (finish_durable_execution verified actor
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect claimed_actor call_id payload))) s)) call_id =
    unclaimed_regulated_call s call_id"
  by (cases "unclaimed_regulated_call s call_id")
    (simp_all add: Let_def unclaimed_regulated_call_def replace_product_outcomes_def replace_regulated_reads_def)

lemma ordinary_finish_reply_is_recoverable_from_its_post_state:
  fixes verified :: "product_principal \<Rightarrow> client_call_id \<Rightarrow> product_call_payload \<Rightarrow> bool"
    and actor claimed_actor :: product_principal
    and call_id :: client_call_id
    and payload :: product_call_payload
    and s :: "'more regulated_product_world_scheme"
  defines "result \<equiv> finish_durable_execution verified actor
    (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect claimed_actor call_id payload))) s"
  shows "snd result =
    (if \<not> unclaimed_regulated_call (fst result) call_id then Durable_Execution_Reject
     else Durable_Execution_Reply (Observed_Ordinary_Result
       (observe_collection verified actor call_id payload (current_product_outcomes (fst result)))))"
proof -
  have gate: "unclaimed_regulated_call (fst result) call_id = unclaimed_regulated_call s call_id"
    unfolding result_def by (rule ordinary_finishing_preserves_its_regulated_claim_gate)
  have observation: "observe_collection verified actor call_id payload (current_product_outcomes (fst result)) =
      observe_collection verified actor call_id payload (current_product_outcomes s)"
    unfolding result_def by (rule ordinary_finishing_preserves_the_collection_observation)
  have reply_before: "snd result =
      (if \<not> unclaimed_regulated_call s call_id then Durable_Execution_Reject
       else Durable_Execution_Reply (Observed_Ordinary_Result
         (observe_collection verified actor call_id payload (current_product_outcomes s))))"
  proof (cases "unclaimed_regulated_call s call_id")
    case True
    then show ?thesis unfolding result_def by (simp add: Let_def)
  next
    case False
    then show ?thesis unfolding result_def by simp
  qed
  show ?thesis by (simp only: reply_before gate observation)
qed

lemma ordinary_equal_captures_have_equal_regulated_claim_gates:
  assumes "capture_retained_product a = capture_retained_product b"
  shows "unclaimed_regulated_call a call_id = unclaimed_regulated_call b call_id"
  using assms
  by (simp add: unclaimed_regulated_call_def ordinary_capture_keeps_the_legal_receipt_map
    ordinary_capture_keeps_the_spend_receipt_map)

lemma ordinary_same_post_capture_for_one_request_determines_finish_reply:
  fixes verified :: "product_principal \<Rightarrow> client_call_id \<Rightarrow> product_call_payload \<Rightarrow> bool"
    and actor claimed_a claimed_b :: product_principal
    and call_id :: client_call_id
    and payload :: product_call_payload
    and a :: "'more_a regulated_product_world_scheme"
    and b :: "'more_b regulated_product_world_scheme"
  defines "result_a \<equiv> finish_durable_execution verified actor
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect claimed_a call_id payload))) a"
    and "result_b \<equiv> finish_durable_execution verified actor
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect claimed_b call_id payload))) b"
  assumes same: "capture_retained_product (fst result_a) = capture_retained_product (fst result_b)"
    and status: "call_local_status (product_calls (outcome_source (current_product_outcomes (fst result_a)))) =
      call_local_status (product_calls (outcome_source (current_product_outcomes (fst result_b))))"
  shows "snd result_a = snd result_b"
proof -
  have gates: "unclaimed_regulated_call (fst result_a) call_id = unclaimed_regulated_call (fst result_b) call_id"
    by (rule ordinary_equal_captures_have_equal_regulated_claim_gates[OF same])
  have observations: "observe_collection verified actor call_id payload (current_product_outcomes (fst result_a)) =
      observe_collection verified actor call_id payload (current_product_outcomes (fst result_b))"
    by (rule ordinary_collection_depends_only_on_capture_and_local_status[OF same status])
  have reply_a: "snd result_a =
      (if \<not> unclaimed_regulated_call (fst result_a) call_id then Durable_Execution_Reject
       else Durable_Execution_Reply (Observed_Ordinary_Result
         (observe_collection verified actor call_id payload (current_product_outcomes (fst result_a)))))"
    unfolding result_a_def by (rule ordinary_finish_reply_is_recoverable_from_its_post_state)
  have reply_b: "snd result_b =
      (if \<not> unclaimed_regulated_call (fst result_b) call_id then Durable_Execution_Reject
       else Durable_Execution_Reply (Observed_Ordinary_Result
         (observe_collection verified actor call_id payload (current_product_outcomes (fst result_b)))))"
    unfolding result_b_def by (rule ordinary_finish_reply_is_recoverable_from_its_post_state)
  show ?thesis using reply_a reply_b gates observations by simp
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ordinary_collection_ignores_only_the_completed_set
      ordinary_completion_preserves_the_collection_observation
      source_attestation.ordinary_finishing_preserves_the_collection_observation
      source_attestation.ordinary_finishing_preserves_its_regulated_claim_gate
      source_attestation.ordinary_finish_reply_is_recoverable_from_its_post_state
      source_attestation.ordinary_equal_captures_have_equal_regulated_claim_gates
      source_attestation.ordinary_same_post_capture_for_one_request_determines_finish_reply})
  then () else error "Unexpected oracle in ordinary completion post-state observation"
\<close>

end
