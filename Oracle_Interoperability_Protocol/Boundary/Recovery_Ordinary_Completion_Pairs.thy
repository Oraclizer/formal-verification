theory Recovery_Ordinary_Completion_Pairs
  imports Recovery_Ordinary_Completion_Shape
begin

context source_attestation
begin

lemma two_changed_ordinary_completions_with_equal_images_have_equal_replies:
  assumes produced_a: "result_a = finish_durable_execution verified actor_a
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect claimed_a id_a payload_a))) before_a"
    and produced_b: "result_b = finish_durable_execution verified actor_b
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect claimed_b id_b payload_b))) before_b"
    and before_images: "capture_retained_product before_a = capture_retained_product before_b"
    and changed_a: "capture_retained_product (fst result_a) \<noteq> capture_retained_product before_a"
    and same_images: "capture_retained_product (fst result_a) = capture_retained_product (fst result_b)"
  shows "snd result_a = snd result_b"
proof -
  let ?oa = "current_product_outcomes before_a"
  let ?ob = "current_product_outcomes before_b"
  have changed_b: "capture_retained_product (fst result_b) \<noteq> capture_retained_product before_b"
    using before_images changed_a same_images by auto
  obtain outcome_a where read_a: "read_authoritative_result verified actor_a id_a payload_a ?oa = Some outcome_a"
    and fresh_a: "id_a \<notin> outcome_completed ?oa"
    and shape_a: "result_a = (replace_product_outcomes (?oa
      \<lparr>outcome_completed := insert id_a (outcome_completed ?oa)\<rparr>) before_a,
      Durable_Execution_Reply (Observed_Ordinary_Result (Collected outcome_a)))"
    using a_changed_ordinary_completion_has_a_fresh_completed_key_and_the_stored_reply[OF produced_a changed_a] by blast
  obtain outcome_b where read_b: "read_authoritative_result verified actor_b id_b payload_b ?ob = Some outcome_b"
    and fresh_b: "id_b \<notin> outcome_completed ?ob"
    and shape_b: "result_b = (replace_product_outcomes (?ob
      \<lparr>outcome_completed := insert id_b (outcome_completed ?ob)\<rparr>) before_b,
      Durable_Execution_Reply (Observed_Ordinary_Result (Collected outcome_b)))"
    using a_changed_ordinary_completion_has_a_fresh_completed_key_and_the_stored_reply[OF produced_b changed_b] by blast
  have same_before_sets: "outcome_completed ?oa = outcome_completed ?ob"
    using arg_cong[OF before_images, of retained_completed_ids]
    by (simp add: capture_retains_the_exact_completed_set)
  have same_after_sets: "insert id_a (outcome_completed ?oa) = insert id_b (outcome_completed ?ob)"
    using arg_cong[OF same_images, of retained_completed_ids] shape_a shape_b
    by (simp add: capture_of_a_completed_set_replacement)
  have second_fresh: "id_b \<notin> outcome_completed ?oa" using fresh_b same_before_sets by simp
  have inserts: "insert id_a (outcome_completed ?oa) = insert id_b (outcome_completed ?oa)"
    using same_after_sets same_before_sets by simp
  have keys: "id_a = id_b"
    by (rule equal_fresh_set_insertions_identify_the_same_key[OF fresh_a second_fresh inserts])
  have same_before_maps: "outcome_entries ?oa = outcome_entries ?ob"
    using arg_cong[OF before_images, of retained_outcomes]
    by (simp add: capture_retains_the_exact_outcome_map)
  obtain record_a where row_a: "outcome_entries ?oa id_a = Some record_a" "result_outcome record_a = outcome_a"
    using read_a by (auto simp: read_authoritative_result_def split: option.splits if_splits)
  obtain record_b where row_b: "outcome_entries ?ob id_b = Some record_b" "result_outcome record_b = outcome_b"
    using read_b by (auto simp: read_authoritative_result_def split: option.splits if_splits)
  have at_id: "outcome_entries ?oa id_a = outcome_entries ?ob id_a"
    by (rule fun_cong[OF same_before_maps])
  have at_key: "outcome_entries ?ob id_a = outcome_entries ?ob id_b"
    by (rule arg_cong[OF keys, of "outcome_entries ?ob"])
  have same_options: "Some record_a = Some record_b"
  proof -
    have "Some record_a = outcome_entries ?oa id_a" by (rule sym[OF row_a(1)])
    also have "... = outcome_entries ?ob id_a" by (rule at_id)
    also have "... = outcome_entries ?ob id_b" by (rule at_key)
    also have "... = Some record_b" by (rule row_b(1))
    finally show ?thesis .
  qed
  have records: "record_a = record_b"
    by (rule option.inject[THEN iffD1, OF same_options])
  have replies: "outcome_a = outcome_b" using records row_a(2) row_b(2) by simp
  show ?thesis using shape_a shape_b replies by simp
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.two_changed_ordinary_completions_with_equal_images_have_equal_replies})
  then () else error "Unexpected oracle in ordinary completion pair target"
\<close>

end
