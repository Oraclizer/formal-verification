theory Recovery_Ordinary_Prior_Pairs
  imports Recovery_Ordinary_Durable_Shape Recovery_Ordinary_Projection "Recovery_Ordinary_Completion_Pairs"
begin

context source_attestation
begin

lemma a_changed_fresh_ordinary_execute_cannot_share_a_prior_execute_image:
  assumes produced_a: "result_a = durable_execute directory policy authenticate verify endorse route_a token_a proof_a target_a
      (Ordinary_Product_Action (Execute_Checked entry_a actor_a expected_a id_a payload_a)) authorization_a
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_a"
    and produced_b: "result_b = durable_execute directory policy authenticate verify endorse route_b token_b proof_b target_b
      (Ordinary_Product_Action (Execute_Checked entry_b actor_b expected_b id_b payload_b)) authorization_b
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_b"
    and before_images: "capture_retained_product before_a = capture_retained_product before_b"
    and changed_a: "capture_retained_product (fst result_a) \<noteq> capture_retained_product before_a"
    and fresh_a: "\<not> authority_has_call_id id_a before_a"
    and prior_b: "authority_has_call_id id_b before_b"
  shows "capture_retained_product (fst result_a) \<noteq> capture_retained_product (fst result_b)"
proof
  assume equal_images: "capture_retained_product (fst result_a) = capture_retained_product (fst result_b)"
  have rows: "\<exists>reply. outcome_entries (current_product_outcomes (fst result_a)) =
      (outcome_entries (current_product_outcomes before_a))
        (id_a := Some \<lparr>result_payload = payload_a, result_outcome = reply\<rparr>)"
    by (rule ordinary_a_changed_fresh_execute_finishes_and_inserts_the_exact_request_row(3)
      [OF produced_a changed_a fresh_a])
  then obtain reply where inserted: "outcome_entries (current_product_outcomes (fst result_a)) =
      (outcome_entries (current_product_outcomes before_a))
        (id_a := Some \<lparr>result_payload = payload_a, result_outcome = reply\<rparr>)" by blast
  have fresh_row: "outcome_entries (current_product_outcomes before_a) id_a = None"
    by (rule ordinary_a_changed_fresh_execute_finishes_and_inserts_the_exact_request_row(2)
      [OF produced_a changed_a fresh_a])
  have changed_map: "outcome_entries (current_product_outcomes (fst result_a)) \<noteq>
      outcome_entries (current_product_outcomes before_a)"
    by (rule ordinary_a_fresh_result_changes_the_outcome_map[OF fresh_row inserted])
  have prior_frame: "outcome_entries (current_product_outcomes (fst result_b)) =
      outcome_entries (current_product_outcomes before_b)"
    using ordinary_prior_durable_execute_keeps_the_entire_outcome_map[OF prior_b] produced_b by simp
  have same_before: "outcome_entries (current_product_outcomes before_a) = outcome_entries (current_product_outcomes before_b)"
    using before_images by (simp add: ordinary_capture_keeps_the_outcome_map)
  have same_after: "outcome_entries (current_product_outcomes (fst result_a)) =
      outcome_entries (current_product_outcomes (fst result_b))"
    using equal_images by (simp add: ordinary_capture_keeps_the_outcome_map)
  show False using changed_map prior_frame same_before same_after by simp
qed

lemma two_changed_prior_ordinary_executes_with_equal_images_have_equal_replies:
  assumes produced_a: "result_a = durable_execute directory policy authenticate verify endorse route_a token_a proof_a target_a
      (Ordinary_Product_Action (Execute_Checked entry_a actor_a expected_a id_a payload_a)) authorization_a
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_a"
    and produced_b: "result_b = durable_execute directory policy authenticate verify endorse route_b token_b proof_b target_b
      (Ordinary_Product_Action (Execute_Checked entry_b actor_b expected_b id_b payload_b)) authorization_b
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack before_b"
    and before_images: "capture_retained_product before_a = capture_retained_product before_b"
    and changed_a: "capture_retained_product (fst result_a) \<noteq> capture_retained_product before_a"
    and same_images: "capture_retained_product (fst result_a) = capture_retained_product (fst result_b)"
    and prior_a: "authority_has_call_id id_a before_a"
    and prior_b: "authority_has_call_id id_b before_b"
  shows "snd result_a = snd result_b"
proof -
  have changed_b: "capture_retained_product (fst result_b) \<noteq> capture_retained_product before_b"
    using before_images changed_a same_images by auto
  have finish_a: "result_a = finish_durable_execution verified actor_a
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect actor_a id_a payload_a))) before_a"
    by (rule ordinary_a_changed_prior_execute_is_its_exact_finish[OF produced_a changed_a prior_a])
  have finish_b: "result_b = finish_durable_execution verified actor_b
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect actor_b id_b payload_b))) before_b"
    by (rule ordinary_a_changed_prior_execute_is_its_exact_finish[OF produced_b changed_b prior_b])
  show ?thesis
    by (rule two_changed_ordinary_completions_with_equal_images_have_equal_replies
      [OF finish_a finish_b before_images changed_a same_images])
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.a_changed_fresh_ordinary_execute_cannot_share_a_prior_execute_image
      source_attestation.two_changed_prior_ordinary_executes_with_equal_images_have_equal_replies})
  then () else error "Unexpected oracle in full ordinary prior/fresh pair separation"
\<close>

end
