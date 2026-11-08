theory Recovery_Ordinary_Completion_Shape
  imports Recovery_Execute_Typed_Reply_Pairs
begin

lemma equal_fresh_set_insertions_identify_the_same_key:
  assumes "key_a \<notin> before" "key_b \<notin> before" "insert key_a before = insert key_b before"
  shows "key_a = key_b"
  using assms by blast

lemma replacing_the_exact_current_outcomes_is_identity:
  "replace_product_outcomes (current_product_outcomes s) s = s"
  by (simp add: replace_product_outcomes_def current_product_outcomes_def regulated_read_world_def
    legal_underlying_outcomes_def update_settlement_outcomes_def replace_regulated_reads_def Let_def)

lemma capture_retains_the_exact_completed_set:
  "retained_completed_ids (capture_retained_product s) = outcome_completed (current_product_outcomes s)"
  by (simp add: capture_retained_product_def current_product_outcomes_def legal_underlying_outcomes_def Let_def)

lemma capture_retains_the_exact_outcome_map:
  "retained_outcomes (capture_retained_product s) = outcome_entries (current_product_outcomes s)"
  by (simp add: capture_retained_product_def current_product_outcomes_def legal_underlying_outcomes_def Let_def)

lemma capture_of_a_completed_set_replacement:
  "capture_retained_product (replace_product_outcomes
      ((current_product_outcomes s)\<lparr>outcome_completed := completed\<rparr>) s) =
    (capture_retained_product s)\<lparr>retained_completed_ids := completed\<rparr>"
  by (simp add: capture_retained_product_def replace_product_outcomes_def current_product_outcomes_def
    regulated_read_world_def legal_underlying_outcomes_def update_settlement_outcomes_def replace_regulated_reads_def Let_def)

context source_attestation
begin

lemma a_changed_ordinary_completion_has_a_fresh_completed_key_and_the_stored_reply:
  assumes produced: "result = finish_durable_execution verified actor
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect claimed_actor call_id payload))) before"
    and changed: "capture_retained_product (fst result) \<noteq> capture_retained_product before"
  shows "\<exists>outcome. read_authoritative_result verified actor call_id payload (current_product_outcomes before) = Some outcome \<and>
    call_id \<notin> outcome_completed (current_product_outcomes before) \<and>
    result = (replace_product_outcomes ((current_product_outcomes before)
       \<lparr>outcome_completed := insert call_id (outcome_completed (current_product_outcomes before))\<rparr>) before,
      Durable_Execution_Reply (Observed_Ordinary_Result (Collected outcome)))"
proof -
  let ?outcomes = "current_product_outcomes before"
  have access: "unclaimed_regulated_call before call_id"
  proof (cases "unclaimed_regulated_call before call_id")
    case True
    then show ?thesis .
  next
    case False
    then have "fst result = before" using produced by simp
    then show ?thesis using changed by simp
  qed
  have live: "call_local_status (product_calls (outcome_source ?outcomes)) = Endpoint_Up"
  proof (cases "call_local_status (product_calls (outcome_source ?outcomes)) = Endpoint_Up")
    case True
    then show ?thesis .
  next
    case False
    have "fst result = before" using produced access False
      by (simp add: complete_authoritative_result_def Let_def replacing_the_exact_current_outcomes_is_identity)
    then show ?thesis using changed by simp
  qed
  have present: "read_authoritative_result verified actor call_id payload ?outcomes \<noteq> None"
  proof
    assume missing: "read_authoritative_result verified actor call_id payload ?outcomes = None"
    have "fst result = before" using produced access live missing
      by (simp add: complete_authoritative_result_def Let_def replacing_the_exact_current_outcomes_is_identity)
    then show False using changed by simp
  qed
  then obtain outcome where read: "read_authoritative_result verified actor call_id payload ?outcomes = Some outcome"
    by (cases "read_authoritative_result verified actor call_id payload ?outcomes") auto
  have observed: "observe_collection verified actor call_id payload ?outcomes = Collected outcome"
    using read live by (auto simp: read_authoritative_result_def observe_collection_def
      split: option.splits if_splits)
  have shape: "result = (replace_product_outcomes (?outcomes
       \<lparr>outcome_completed := insert call_id (outcome_completed ?outcomes)\<rparr>) before,
      Durable_Execution_Reply (Observed_Ordinary_Result (Collected outcome)))"
    using produced access live read observed by (simp add: complete_authoritative_result_def Let_def)
  have fresh: "call_id \<notin> outcome_completed ?outcomes"
  proof
    assume old: "call_id \<in> outcome_completed ?outcomes"
    have same_set: "insert call_id (outcome_completed ?outcomes) = outcome_completed ?outcomes"
      by (rule insert_absorb[OF old])
    have same_outcomes: "?outcomes\<lparr>outcome_completed := insert call_id (outcome_completed ?outcomes)\<rparr> = ?outcomes"
      using same_set by simp
    have first_component: "fst result = replace_product_outcomes
        (?outcomes\<lparr>outcome_completed := insert call_id (outcome_completed ?outcomes)\<rparr>) before"
      using arg_cong[OF shape, of fst] by simp
    have "fst result = before"
      by (simp only: first_component same_outcomes replacing_the_exact_current_outcomes_is_identity)
    then show False using changed by simp
  qed
  show ?thesis using read fresh shape by blast
qed

end

text \<open>This handles only a completion whose retained image changes. Fresh ordinary execution
  may return Waiting or Rejected after inserting a result; that outer producer case remains to
  be reconstructed rather than being treated as a successful changed completion.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms equal_fresh_set_insertions_identify_the_same_key
      replacing_the_exact_current_outcomes_is_identity capture_retains_the_exact_completed_set
      capture_retains_the_exact_outcome_map capture_of_a_completed_set_replacement
      source_attestation.a_changed_ordinary_completion_has_a_fresh_completed_key_and_the_stored_reply})
  then () else error "Unexpected oracle in ordinary completion reconstruction"
\<close>

end
