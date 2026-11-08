theory Recovery_Ordinary_Fresh_Pairs
  imports Recovery_Ordinary_Prior_Pairs Recovery_Ordinary_Completion_Projection
    Recovery_Ordinary_Execute_Control_Frames Recovery_Ordinary_Receipt_Frames
begin

context source_attestation
begin

lemma two_changed_fresh_ordinary_executes_with_equal_images_have_equal_replies:
  assumes produced_a: "result_a = durable_execute directory policy authenticate verify endorse route_a token_a proof_a target_a
      (Ordinary_Product_Action (Execute_Checked entry_a actor_a expected_a id_a payload_a)) authorization_a
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_a"
    and produced_b: "result_b = durable_execute directory policy authenticate verify endorse route_b token_b proof_b target_b
      (Ordinary_Product_Action (Execute_Checked entry_b actor_b expected_b id_b payload_b)) authorization_b
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_b"
    and before_images: "capture_retained_product before_a = capture_retained_product before_b"
    and changed_a: "capture_retained_product (fst result_a) \<noteq> capture_retained_product before_a"
    and same_images: "capture_retained_product (fst result_a) = capture_retained_product (fst result_b)"
    and fresh_a: "\<not> authority_has_call_id id_a before_a"
    and fresh_b: "\<not> authority_has_call_id id_b before_b"
  shows "snd result_a = snd result_b"
proof -
  let ?oa = "outcome_entries (current_product_outcomes before_a)"
  let ?ob = "outcome_entries (current_product_outcomes before_b)"
  let ?executed_a = "run_fresh_durable_effect permitted verified maintainers registered verified_ack legal_grant order_verified
    spend_grant spend_verified read_permitted (Ordinary_Product_Action (Execute_Checked entry_a actor_a expected_a id_a payload_a)) before_a"
  let ?executed_b = "run_fresh_durable_effect permitted verified maintainers registered verified_ack legal_grant order_verified
    spend_grant spend_verified read_permitted (Ordinary_Product_Action (Execute_Checked entry_b actor_b expected_b id_b payload_b)) before_b"
  have changed_b: "capture_retained_product (fst result_b) \<noteq> capture_retained_product before_b"
    using before_images changed_a same_images by auto
  have rows_a: "\<exists>reply. outcome_entries (current_product_outcomes (fst result_a)) =
      ?oa(id_a := Some \<lparr>result_payload = payload_a, result_outcome = reply\<rparr>)"
    by (rule ordinary_a_changed_fresh_execute_finishes_and_inserts_the_exact_request_row(3)[OF produced_a changed_a fresh_a])
  have rows_b: "\<exists>reply. outcome_entries (current_product_outcomes (fst result_b)) =
      ?ob(id_b := Some \<lparr>result_payload = payload_b, result_outcome = reply\<rparr>)"
    by (rule ordinary_a_changed_fresh_execute_finishes_and_inserts_the_exact_request_row(3)[OF produced_b changed_b fresh_b])
  obtain outcome_a where row_a: "outcome_entries (current_product_outcomes (fst result_a)) =
      ?oa(id_a := Some \<lparr>result_payload = payload_a, result_outcome = outcome_a\<rparr>)" using rows_a by blast
  obtain outcome_b where row_b: "outcome_entries (current_product_outcomes (fst result_b)) =
      ?ob(id_b := Some \<lparr>result_payload = payload_b, result_outcome = outcome_b\<rparr>)" using rows_b by blast
  have absent_a: "?oa id_a = None" using fresh_a by (simp add: authority_has_call_id_def)
  have absent_b: "?ob id_b = None" using fresh_b by (simp add: authority_has_call_id_def)
  have bases: "?oa = ?ob" using before_images by (simp add: ordinary_capture_keeps_the_outcome_map)
  have same_rows: "outcome_entries (current_product_outcomes (fst result_a)) =
      outcome_entries (current_product_outcomes (fst result_b))"
    using same_images by (simp add: ordinary_capture_keeps_the_outcome_map)
  have second_fresh: "?oa id_b = None" using bases absent_b by simp
  have updates: "?oa(id_a := Some \<lparr>result_payload = payload_a, result_outcome = outcome_a\<rparr>) =
      ?oa(id_b := Some \<lparr>result_payload = payload_b, result_outcome = outcome_b\<rparr>)"
    using row_a row_b same_rows bases by simp
  have keys: "id_a = id_b"
    by (rule equal_fresh_single_insertions_identify_the_same_key_and_value(1)[OF absent_a second_fresh updates])
  have saved_rows: "\<lparr>result_payload = payload_a, result_outcome = outcome_a\<rparr> =
      \<lparr>result_payload = payload_b, result_outcome = outcome_b\<rparr>"
    by (rule equal_fresh_single_insertions_identify_the_same_key_and_value(2)[OF absent_a second_fresh updates])
  have payloads: "payload_a = payload_b" using arg_cong[OF saved_rows, of result_payload] by simp
  have admitted_a: "authorized_endpoint_action directory policy authenticate verify route_a token_a proof_a target_a
      (Ordinary_Product_Action (Execute_Checked entry_a actor_a expected_a id_a payload_a)) before_a"
    and up_a: "call_local_status (product_calls (identity_source before_a)) = Endpoint_Up"
    using ordinary_a_changed_durable_execute_passed_authentication_and_was_up[OF produced_a changed_a] .
  have admitted_b: "authorized_endpoint_action directory policy authenticate verify route_b token_b proof_b target_b
      (Ordinary_Product_Action (Execute_Checked entry_b actor_b expected_b id_b payload_b)) before_b"
    and up_b: "call_local_status (product_calls (identity_source before_b)) = Endpoint_Up"
    using ordinary_a_changed_durable_execute_passed_authentication_and_was_up[OF produced_b changed_b] .
  have actor_a: "actor_a = fst id_a"
    using admitted_a by (auto simp: authorized_endpoint_action_def endpoint_call_allowed_on_def endpoint_call_allowed_def
      endpoint_call_identity_def product_identity_bound_def Let_def)
  have actor_b: "actor_b = fst id_b"
    using admitted_b by (auto simp: authorized_endpoint_action_def endpoint_call_allowed_on_def endpoint_call_allowed_def
      endpoint_call_identity_def product_identity_bound_def Let_def)
  have actors: "actor_a = actor_b" using actor_a actor_b keys by simp
  have post_up_a: "call_local_status (product_calls (outcome_source (current_product_outcomes (fst result_a)))) = Endpoint_Up"
    using ordinary_full_execute_keeps_source_controls(4)[OF produced_a] up_a
    by (simp add: ordinary_identity_source_is_the_outcome_source)
  have post_up_b: "call_local_status (product_calls (outcome_source (current_product_outcomes (fst result_b)))) = Endpoint_Up"
    using ordinary_full_execute_keeps_source_controls(4)[OF produced_b] up_b
    by (simp add: ordinary_identity_source_is_the_outcome_source)
  have status: "call_local_status (product_calls (outcome_source (current_product_outcomes (fst result_a)))) =
      call_local_status (product_calls (outcome_source (current_product_outcomes (fst result_b))))"
    using post_up_a post_up_b by simp
  have finish_a: "result_a = finish_durable_execution verified actor_a
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect actor_a id_a payload_a))) ?executed_a"
    by (rule ordinary_a_changed_fresh_execute_finishes_and_inserts_the_exact_request_row(1)[OF produced_a changed_a fresh_a])
  have finish_b: "result_b = finish_durable_execution verified actor_b
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect actor_b id_b payload_b))) ?executed_b"
    by (rule ordinary_a_changed_fresh_execute_finishes_and_inserts_the_exact_request_row(1)[OF produced_b changed_b fresh_b])
  have unclaimed_a: "unclaimed_regulated_call before_a id_a" using fresh_a by (simp add: authority_has_call_id_def)
  have unclaimed_b: "unclaimed_regulated_call before_b id_b" using fresh_b by (simp add: authority_has_call_id_def)
  have gate_a: "unclaimed_regulated_call ?executed_a id_a"
    using unclaimed_a by (simp only: unclaimed_regulated_call_def ordinary_fresh_effect_keeps_both_regulated_receipt_maps)
  have gate_b: "unclaimed_regulated_call ?executed_b id_b"
    using unclaimed_b by (simp only: unclaimed_regulated_call_def ordinary_fresh_effect_keeps_both_regulated_receipt_maps)
  have observation_a: "observe_collection verified actor_a id_a payload_a (current_product_outcomes (fst result_a)) =
      observe_collection verified actor_a id_a payload_a (current_product_outcomes ?executed_a)"
    using ordinary_finishing_preserves_the_collection_observation
      [where verified = verified and actor = actor_a and call_id = id_a and payload = payload_a
        and claimed_actor = actor_a and s = ?executed_a] finish_a by simp
  have observation_b: "observe_collection verified actor_b id_b payload_b (current_product_outcomes (fst result_b)) =
      observe_collection verified actor_b id_b payload_b (current_product_outcomes ?executed_b)"
    using ordinary_finishing_preserves_the_collection_observation
      [where verified = verified and actor = actor_b and call_id = id_b and payload = payload_b
        and claimed_actor = actor_b and s = ?executed_b] finish_b by simp
  have reply_a: "snd result_a = Durable_Execution_Reply (Observed_Ordinary_Result
      (observe_collection verified actor_a id_a payload_a (current_product_outcomes (fst result_a))))"
    using finish_a gate_a observation_a by (simp add: Let_def)
  have reply_b: "snd result_b = Durable_Execution_Reply (Observed_Ordinary_Result
      (observe_collection verified actor_b id_b payload_b (current_product_outcomes (fst result_b))))"
    using finish_b gate_b observation_b by (simp add: Let_def)
  have observations: "observe_collection verified actor_a id_a payload_a (current_product_outcomes (fst result_a)) =
      observe_collection verified actor_b id_b payload_b (current_product_outcomes (fst result_b))"
    using ordinary_collection_depends_only_on_capture_and_local_status[OF same_images status,
      where verified = verified and actor = actor_a and call_id = id_a and payload = payload_a]
      actors keys payloads by simp
  show ?thesis using reply_a reply_b observations by simp
qed

lemma two_changed_ordinary_executes_with_equal_images_have_equal_replies:
  assumes produced_a: "result_a = durable_execute directory policy authenticate verify endorse route_a token_a proof_a target_a
      (Ordinary_Product_Action (Execute_Checked entry_a actor_a expected_a id_a payload_a)) authorization_a
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_a"
    and produced_b: "result_b = durable_execute directory policy authenticate verify endorse route_b token_b proof_b target_b
      (Ordinary_Product_Action (Execute_Checked entry_b actor_b expected_b id_b payload_b)) authorization_b
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_b"
    and before_images: "capture_retained_product before_a = capture_retained_product before_b"
    and changed_a: "capture_retained_product (fst result_a) \<noteq> capture_retained_product before_a"
    and same_images: "capture_retained_product (fst result_a) = capture_retained_product (fst result_b)"
  shows "snd result_a = snd result_b"
proof (cases "authority_has_call_id id_a before_a")
  case prior_a: True
  show ?thesis
  proof (cases "authority_has_call_id id_b before_b")
    case prior_b: True
    show ?thesis by (rule two_changed_prior_ordinary_executes_with_equal_images_have_equal_replies
      [OF produced_a produced_b before_images changed_a same_images prior_a prior_b])
  next
    case fresh_b: False
    have changed_b: "capture_retained_product (fst result_b) \<noteq> capture_retained_product before_b"
      using before_images changed_a same_images by auto
    have before_reverse: "capture_retained_product before_b = capture_retained_product before_a" by (rule sym[OF before_images])
    have different: "capture_retained_product (fst result_b) \<noteq> capture_retained_product (fst result_a)"
      by (rule a_changed_fresh_ordinary_execute_cannot_share_a_prior_execute_image
        [OF produced_b produced_a before_reverse changed_b fresh_b prior_a])
    then show ?thesis using same_images by simp
  qed
next
  case fresh_a: False
  show ?thesis
  proof (cases "authority_has_call_id id_b before_b")
    case prior_b: True
    have different: "capture_retained_product (fst result_a) \<noteq> capture_retained_product (fst result_b)"
      by (rule a_changed_fresh_ordinary_execute_cannot_share_a_prior_execute_image
        [OF produced_a produced_b before_images changed_a fresh_a prior_b])
    then show ?thesis using same_images by simp
  next
    case fresh_b: False
    show ?thesis by (rule two_changed_fresh_ordinary_executes_with_equal_images_have_equal_replies
      [OF produced_a produced_b before_images changed_a same_images fresh_a fresh_b])
  qed
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.two_changed_fresh_ordinary_executes_with_equal_images_have_equal_replies
      source_attestation.two_changed_ordinary_executes_with_equal_images_have_equal_replies})
  then () else error "Unexpected oracle in full ordinary durable reply pairs"
\<close>

end
