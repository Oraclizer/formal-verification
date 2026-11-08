theory Recovery_Ordinary_Durable_Shape
  imports Recovery_Ordinary_Fresh_Effect Recovery_Ordinary_Finish_Frames
begin

context source_attestation
begin

lemma ordinary_a_changed_durable_execute_passed_authentication_and_was_up:
  assumes produced: "result = durable_execute directory policy authenticate verify endorse route token proof target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s"
    and changed: "capture_retained_product (fst result) \<noteq> capture_retained_product s"
  shows "authorized_endpoint_action directory policy authenticate verify route token proof target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s"
    and "call_local_status (product_calls (identity_source s)) = Endpoint_Up"
proof -
  have admitted: "authorized_endpoint_action directory policy authenticate verify route token proof target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s"
  proof (rule ccontr)
    assume denied: "\<not> authorized_endpoint_action directory policy authenticate verify route token proof target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s"
    have "fst result = s" using produced denied by (simp add: durable_execute_def)
    then show False using changed by simp
  qed
  show "authorized_endpoint_action directory policy authenticate verify route token proof target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s" by (rule admitted)
  show "call_local_status (product_calls (identity_source s)) = Endpoint_Up"
  proof (rule ccontr)
    assume down: "call_local_status (product_calls (identity_source s)) \<noteq> Endpoint_Up"
    have "fst result = s" using produced admitted down by (simp add: durable_execute_def)
    then show False using changed by simp
  qed
qed

lemma ordinary_a_changed_prior_execute_is_its_exact_finish:
  assumes produced: "result = durable_execute directory policy authenticate verify endorse route token proof target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s"
    and changed: "capture_retained_product (fst result) \<noteq> capture_retained_product s"
    and prior: "authority_has_call_id call_id s"
  shows "result = finish_durable_execution verified actor
    (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect actor call_id payload))) s"
proof -
  have admitted: "authorized_endpoint_action directory policy authenticate verify route token proof target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s"
    and up: "call_local_status (product_calls (identity_source s)) = Endpoint_Up"
    using ordinary_a_changed_durable_execute_passed_authentication_and_was_up[OF produced changed] .
  have permission: "retained_receipt_permission policy authenticate token proof target payload"
  proof (rule ccontr)
    assume denied: "\<not> retained_receipt_permission policy authenticate token proof target payload"
    have "fst result = s" using produced admitted up prior denied by (simp add: durable_execute_def)
    then show False using changed by simp
  qed
  show ?thesis using produced admitted up prior permission by (simp add: durable_execute_def)
qed

lemma ordinary_a_changed_fresh_execute_finishes_and_inserts_the_exact_request_row:
  assumes produced: "result = durable_execute directory policy authenticate verify endorse route token proof target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s"
    and changed: "capture_retained_product (fst result) \<noteq> capture_retained_product s"
    and fresh: "\<not> authority_has_call_id call_id s"
  defines "executed \<equiv> run_fresh_durable_effect permitted verified maintainers registered verified_ack legal_grant order_verified
    spend_grant spend_verified read_permitted (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s"
  shows "result = finish_durable_execution verified actor
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect actor call_id payload))) executed"
    and "outcome_entries (current_product_outcomes s) call_id = None"
    and "\<exists>reply. outcome_entries (current_product_outcomes (fst result)) =
      (outcome_entries (current_product_outcomes s))
        (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>)"
proof -
  have admitted: "authorized_endpoint_action directory policy authenticate verify route token proof target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s"
    and up: "call_local_status (product_calls (identity_source s)) = Endpoint_Up"
    using ordinary_a_changed_durable_execute_passed_authentication_and_was_up[OF produced changed] .
  have recovery: "recovery_requirements directory policy authenticate endorse target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) authorization (identity_source s)"
  proof (rule ccontr)
    assume denied: "\<not> recovery_requirements directory policy authenticate endorse target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) authorization (identity_source s)"
    have "fst result = s" using produced admitted up fresh denied by (simp add: durable_execute_def)
    then show False using changed by simp
  qed
  have shape: "result =
      (if authority_has_call_id call_id executed then finish_durable_execution verified actor
        (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect actor call_id payload))) executed
       else (executed, Durable_Execution_Reject))"
    using produced admitted up fresh recovery by (simp add: durable_execute_def Let_def executed_def)
  have changed_effect: "executed \<noteq> s"
  proof
    assume stutter: "executed = s"
    have "fst result = s" using shape stutter fresh by simp
    then show False using changed by simp
  qed
  have alternatives: "executed = s \<or>
      (\<exists>reply. outcome_entries (current_product_outcomes executed) =
        (outcome_entries (current_product_outcomes s))
          (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>))"
    unfolding executed_def by (rule ordinary_fresh_effect_stutters_or_inserts_the_exact_request_row[OF fresh])
  obtain reply where inserted: "outcome_entries (current_product_outcomes executed) =
      (outcome_entries (current_product_outcomes s))
        (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>)"
    using alternatives changed_effect by blast
  have now_has_call: "authority_has_call_id call_id executed"
    using inserted by (simp add: authority_has_call_id_def)
  show finish: "result = finish_durable_execution verified actor
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect actor call_id payload))) executed"
    using shape now_has_call by simp
  show "outcome_entries (current_product_outcomes s) call_id = None"
    using fresh by (simp add: authority_has_call_id_def)
  show "\<exists>reply. outcome_entries (current_product_outcomes (fst result)) =
      (outcome_entries (current_product_outcomes s))
        (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>)"
  proof (rule exI[of _ reply])
    show "outcome_entries (current_product_outcomes (fst result)) =
        (outcome_entries (current_product_outcomes s))
          (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>)"
    proof -
      have "outcome_entries (current_product_outcomes (fst result)) =
          outcome_entries (current_product_outcomes (fst (finish_durable_execution verified actor
            (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect actor call_id payload))) executed)))"
        by (rule arg_cong[OF finish, of "\<lambda>computed_result. outcome_entries (current_product_outcomes (fst computed_result))"])
      also have "... = outcome_entries (current_product_outcomes executed)"
        by (rule ordinary_finishing_keeps_the_entire_outcome_map)
      also have "... = (outcome_entries (current_product_outcomes s))
          (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>)"
        by (rule inserted)
      finally show ?thesis .
    qed
  qed
qed

end

text \<open>Freshness and prior-call predicates split the actual durable branch. They are not
  added environment restrictions. Fresh changed execution is not assumed to return Collected;
  the preserved row covers Waiting and Rejected until observation projection is applied.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.ordinary_a_changed_durable_execute_passed_authentication_and_was_up
      source_attestation.ordinary_a_changed_prior_execute_is_its_exact_finish
      source_attestation.ordinary_a_changed_fresh_execute_finishes_and_inserts_the_exact_request_row})
  then () else error "Unexpected oracle in ordinary full durable branch reconstruction"
\<close>

end
