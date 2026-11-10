theory Response_Code_Extension
  imports "OIP_Response_Code_Allocation.Response_Code_Extension_Input"
begin

lemma sync_response_allocation_is_valid:
  "response_allocations_valid sync_response_allocations"
  by (simp add: sync_response_allocations_def response_allocations_valid_def response_allocations_fresh_def
    response_allocations_in_range_def response_allocation_range_def code_known_response_number_def reference_result_codes_def)

lemma sync_response_lookup_is_exact:
  "map_of sync_response_allocations number =
    (if number \<in> {29,39,40,41}
     then Some (Recorded_Result,number = 29,[sync_response_operation]) else None)"
  by (auto simp: sync_response_allocations_def split: if_splits)

lemma sync_response_numbers_are_legacy_unknown:
  fixes number :: nat
  assumes "number \<in> {29,39,40,41}"
  shows "\<not> code_known_response_number number"
proof -
  have fresh: "response_allocations_fresh sync_response_allocations"
    using sync_response_allocation_is_valid by (simp add: response_allocations_valid_def)
  have assigned: "map_of sync_response_allocations number =
    Some (Recorded_Result,number = 29,[sync_response_operation])"
    using assms by (simp add: sync_response_lookup_is_exact)
  show ?thesis by (rule a_fresh_assignment_number_is_legacy_unknown[OF fresh assigned])
qed

theorem legacy_sync_response_numbers_follow_the_declared_category:
  assumes "number \<in> {29,39,40,41}"
  shows "code_decode_raw_response_status raw_kind number committed =
    Option.bind (response_kind_at raw_kind) (\<lambda>kind.
      if kind = Recorded_Result \<or> \<not> committed
      then Some (Code_Unknown_Response kind number) else None)"
  by (simp add: code_decode_raw_response_status_def
      an_unknown_number_is_accepted_only_as_its_declared_category[OF sync_response_numbers_are_legacy_unknown[OF assms]])

theorem sync_response_kind_commit_and_original_call_are_fixed:
  assumes "number \<in> {29,39,40,41}"
  shows "response_extended_raw_status sync_response_allocations raw_kind number committed =
      (if raw_kind = 1 \<and> committed = (number = 29)
       then Some (Code_Known_Response Recorded_Result number) else None)"
    "response_extended_compatible sync_response_allocations [sync_response_operation] family operation kind number committed
      \<longleftrightarrow> kind = Recorded_Result \<and> committed = (number = 29) \<and>
        (family,operation) = sync_response_operation"
  using assms by (auto simp: response_extended_raw_status_def response_kind_at_def response_extended_status_def
    response_extended_compatible_def sync_response_lookup_is_exact split: if_splits)

lemma sync_response_words_use_the_fixed_descriptor:
  assumes assigned: "number \<in> {29,39,40,41}"
    and original: "(wire_message_family original,wire_opcode (wire_operation_body original)) = sync_response_operation"
  shows "response_extended_words sync_response_allocations [sync_response_operation] original call_id Recorded_Result number position =
    (if (position \<noteq> None) = (number = 29)
     then Some (wire_words (reference_response_body call_id Recorded_Result number position original)) else None)"
  using assigned original
  by (auto simp: response_extended_words_def response_extended_status_def sync_response_lookup_is_exact
      sync_response_kind_commit_and_original_call_are_fixed(2)[OF assigned] split: if_splits)

lemma legacy_response_correlation_requires_a_decodable_original:
  assumes "(wire_message_family original,wire_opcode (wire_operation_body original)) = sync_response_operation"
  shows "decode_wire_core bytes \<noteq> Some original"
proof
  assume decoded: "decode_wire_core bytes = Some original"
  have "wire_core_wellformed original"
    using accepted_core_bytes_preserve_all_original_fields[OF decoded] by blast
  with assms show False by (auto simp: wire_core_wellformed_def sync_response_operation_def)
qed

lemma the_sync_call_keeps_the_shared_legacy_responses:
  "response_extended_compatible sync_response_allocations [sync_response_operation] Wire_State_Sync 7 Recorded_Result 1 False"
  "response_extended_compatible sync_response_allocations [sync_response_operation] Wire_State_Sync 7 Recorded_Result 2 False"
  "response_extended_compatible sync_response_allocations [sync_response_operation] Wire_State_Sync 7 Recorded_Result 3 False"
  "response_extended_compatible sync_response_allocations [sync_response_operation] Wire_State_Sync 7 Delivery_Refusal 50 False"
  "response_extended_compatible sync_response_allocations [sync_response_operation] Wire_State_Sync 7 Validation_Refusal 70 False"
  "\<not> response_extended_compatible sync_response_allocations [sync_response_operation] Wire_State_Sync 7 Recorded_Result 12 True"
  by (simp_all add: response_extended_compatible_def sync_response_lookup_is_exact sync_response_operation_def
    code_response_compatible_def code_response_call_shape_def reference_response_compatible_def reference_result_targets_def
    code_decode_response_status_def code_known_response_number_def reference_result_codes_def)

lemma sync_response_kind_commit_and_target_checks_have_independent_counterexamples:
  "map_of sync_response_allocations 29 = Some (Recorded_Result,True,[sync_response_operation])"
  "\<not> response_extended_compatible sync_response_allocations [sync_response_operation]
    Wire_State_Sync 7 Recorded_Result 29 False"
  "map_of sync_response_allocations 39 = Some (Recorded_Result,False,[sync_response_operation])"
  "\<not> response_extended_compatible sync_response_allocations [sync_response_operation]
    Wire_State_Sync 7 Delivery_Refusal 39 False"
  "response_extended_raw_status sync_response_allocations 1 29 True = Some (Code_Known_Response Recorded_Result 29)"
  "\<not> response_extended_compatible sync_response_allocations [sync_response_operation]
    Wire_State_Sync 1 Recorded_Result 29 True"
  "code_response_compatible Wire_State_Sync 1 Recorded_Result 29 True"
  "code_decode_raw_response_status 2 39 False = Some (Code_Unknown_Response Delivery_Refusal 39)"
  by (simp_all add: sync_response_lookup_is_exact sync_response_operation_def response_extended_compatible_def
    response_extended_raw_status_def response_extended_status_def code_decode_raw_response_status_def response_kind_at_def
    code_response_compatible_def code_response_call_shape_def code_decode_response_status_def
    code_known_response_number_def reference_result_codes_def)

definition response_replace_number :: "nat \<Rightarrow> nat \<Rightarrow> response_allocations \<Rightarrow> response_allocations" where
  "response_replace_number old new allocations =
    map (\<lambda>(number,descriptor). (if number = old then new else number,descriptor)) allocations"

lemma a_duplicate_new_number_fails_the_uniqueness_guard:
  "response_allocations_fresh (response_replace_number 41 40 sync_response_allocations)"
  "response_allocations_in_range (response_replace_number 41 40 sync_response_allocations)"
  "\<not> response_allocations_valid (response_replace_number 41 40 sync_response_allocations)"
  by (simp_all add: response_replace_number_def sync_response_allocations_def response_allocations_valid_def
    response_allocations_fresh_def response_allocations_in_range_def response_allocation_range_def
    code_known_response_number_def reference_result_codes_def)

lemma a_legacy_number_collision_requires_the_freshness_guard:
  "distinct (map fst (response_replace_number 29 28 sync_response_allocations))"
  "response_allocations_in_range (response_replace_number 29 28 sync_response_allocations)"
  "\<not> response_allocations_valid (response_replace_number 29 28 sync_response_allocations)"
  "code_response_compatible Wire_State_Sync 6 Recorded_Result 28 True"
  "\<not> response_extended_compatible (response_replace_number 29 28 sync_response_allocations) [sync_response_operation]
    Wire_State_Sync 6 Recorded_Result 28 True"
  by (simp_all add: response_replace_number_def sync_response_allocations_def sync_response_operation_def
    response_allocations_valid_def response_allocations_fresh_def response_allocations_in_range_def response_allocation_range_def
    code_response_compatible_def response_extended_compatible_def reference_response_compatible_def
    code_known_response_number_def reference_result_codes_def reference_result_targets_def)

definition response_change_commit :: "nat \<Rightarrow> bool \<Rightarrow> response_allocations \<Rightarrow> response_allocations" where
  "response_change_commit chosen present allocations =
    map (\<lambda>(number,kind,committed,targets). (number,kind,if number = chosen then present else committed,targets)) allocations"

lemma an_out_of_range_commit_requires_the_allocation_range_guard:
  "distinct (map fst (response_change_commit 29 False sync_response_allocations))"
  "response_allocations_fresh (response_change_commit 29 False sync_response_allocations)"
  "\<not> response_allocations_valid (response_change_commit 29 False sync_response_allocations)"
  "response_extended_raw_status (response_change_commit 29 False sync_response_allocations) 1 29 True = None"
  "response_extended_raw_status (response_change_commit 29 False sync_response_allocations) 1 29 False =
    Some (Code_Known_Response Recorded_Result 29)"
  by (simp_all add: response_change_commit_def sync_response_allocations_def response_allocations_valid_def
    response_allocations_fresh_def response_allocations_in_range_def response_allocation_range_def
    code_known_response_number_def reference_result_codes_def response_extended_raw_status_def
    response_extended_status_def response_kind_at_def)

thm_oracles sync_response_allocation_is_valid valid_response_allocations_are_unique_by_number
  legacy_known_responses_keep_their_status_and_call_compatibility an_unallocated_status_keeps_the_legacy_decoder
  a_valid_assigned_status_is_known_in_the_extension_and_unknown_in_the_legacy_decoder
  legacy_correlated_status_uses_the_unknown_rule_for_an_already_recognized_call
  a_legacy_undecodable_original_cannot_reach_status legacy_response_correlation_requires_a_decodable_original
  legacy_sync_response_numbers_follow_the_declared_category sync_response_kind_commit_and_original_call_are_fixed
  the_extended_sender_uses_the_existing_response_word_format sync_response_words_use_the_fixed_descriptor
  the_sync_call_keeps_the_shared_legacy_responses
  sync_response_kind_commit_and_target_checks_have_independent_counterexamples
  a_duplicate_new_number_fails_the_uniqueness_guard a_legacy_number_collision_requires_the_freshness_guard
  an_out_of_range_commit_requires_the_allocation_range_guard

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_response_allocation_is_valid
    valid_response_allocations_are_unique_by_number legacy_known_responses_keep_their_status_and_call_compatibility
    an_unallocated_status_keeps_the_legacy_decoder
    a_valid_assigned_status_is_known_in_the_extension_and_unknown_in_the_legacy_decoder
    legacy_correlated_status_uses_the_unknown_rule_for_an_already_recognized_call
    a_legacy_undecodable_original_cannot_reach_status legacy_response_correlation_requires_a_decodable_original
    legacy_sync_response_numbers_follow_the_declared_category sync_response_kind_commit_and_original_call_are_fixed
    the_extended_sender_uses_the_existing_response_word_format sync_response_words_use_the_fixed_descriptor
    the_sync_call_keeps_the_shared_legacy_responses
    sync_response_kind_commit_and_target_checks_have_independent_counterexamples
    a_duplicate_new_number_fails_the_uniqueness_guard a_legacy_number_collision_requires_the_freshness_guard
    an_out_of_range_commit_requires_the_allocation_range_guard})
  then () else error "Unexpected oracle in the response code extension"
\<close>

end
