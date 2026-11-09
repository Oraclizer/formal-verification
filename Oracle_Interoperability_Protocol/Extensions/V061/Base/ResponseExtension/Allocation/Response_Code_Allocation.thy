theory Response_Code_Allocation
  imports "OIP_Message_Code.Wire_Code_Response_Status"
    "OIP_Message_Code.Wire_Code_Response_Preflight"
begin

type_synonym response_operation = "wire_family \<times> nat"
type_synonym response_allocation = "reference_response_kind \<times> bool \<times> response_operation list"
type_synonym response_allocations = "(nat \<times> response_allocation) list"

definition response_allocation_range :: "reference_response_kind \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> bool" where
  "response_allocation_range kind committed number \<longleftrightarrow>
    number < 2 ^ 64 \<and> (case kind of
       Recorded_Result \<Rightarrow> if committed then 10 \<le> number \<and> number \<le> 29
         else (1 \<le> number \<and> number \<le> 9) \<or> (30 \<le> number \<and> number \<le> 49)
     | Delivery_Refusal \<Rightarrow> \<not> committed \<and> 50 \<le> number \<and> number \<le> 69
     | Validation_Refusal \<Rightarrow> \<not> committed \<and> 70 \<le> number)"

definition response_allocations_fresh :: "response_allocations \<Rightarrow> bool" where
  "response_allocations_fresh allocations \<longleftrightarrow>
    list_all (\<lambda>entry. \<not> code_known_response_number (fst entry)) allocations"

definition response_allocations_in_range :: "response_allocations \<Rightarrow> bool" where
  "response_allocations_in_range allocations \<longleftrightarrow>
    list_all (\<lambda>(number,kind,committed,targets). response_allocation_range kind committed number) allocations"

definition response_allocations_valid :: "response_allocations \<Rightarrow> bool" where
  "response_allocations_valid allocations \<longleftrightarrow>
    distinct (map fst allocations) \<and> response_allocations_fresh allocations \<and>
      response_allocations_in_range allocations"

definition response_extended_status ::
  "response_allocations \<Rightarrow> reference_response_kind \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> code_response_status option" where
  "response_extended_status allocations kind number committed =
    (case map_of allocations number of
       None \<Rightarrow> code_decode_response_status kind number committed
     | Some (assigned_kind,assigned_commit,targets) \<Rightarrow>
         if kind = assigned_kind \<and> committed = assigned_commit
         then Some (Code_Known_Response kind number) else None)"

definition response_extended_raw_status where
  "response_extended_raw_status allocations kind number committed =
    Option.bind (response_kind_at kind) (\<lambda>category. response_extended_status allocations category number committed)"

definition response_extended_compatible ::
  "response_allocations \<Rightarrow> response_operation list \<Rightarrow> wire_family \<Rightarrow> nat \<Rightarrow>
    reference_response_kind \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool" where
  "response_extended_compatible allocations added_calls family operation kind number committed \<longleftrightarrow>
    (case map_of allocations number of
       Some (assigned_kind,assigned_commit,targets) \<Rightarrow>
         kind = assigned_kind \<and> committed = assigned_commit \<and> (family,operation) \<in> set targets
     | None \<Rightarrow> code_response_compatible family operation kind number committed \<or>
         (\<not> code_response_call_shape family operation \<and> (family,operation) \<in> set added_calls \<and>
          code_decode_response_status kind number committed \<noteq> None \<and>
          (\<not> code_known_response_number number \<or> kind \<noteq> Recorded_Result \<or> number \<in> {1,2,3})))"

lemma valid_response_allocations_have_exact_lookup:
  assumes "response_allocations_valid allocations"
  shows "map_of allocations number = Some descriptor \<longleftrightarrow> (number,descriptor) \<in> set allocations"
  using assms by (simp add: response_allocations_valid_def)

lemma valid_response_allocations_are_unique_by_number:
  assumes valid: "response_allocations_valid allocations"
    and first: "(number,first) \<in> set allocations"
    and second: "(number,second) \<in> set allocations"
  shows "first = second"
proof -
  have "map_of allocations number = Some first"
    using valid_response_allocations_have_exact_lookup[OF valid] first by blast
  moreover have "map_of allocations number = Some second"
    using valid_response_allocations_have_exact_lookup[OF valid] second by blast
  ultimately show ?thesis by simp
qed

lemma a_fresh_assignment_number_is_legacy_unknown:
  assumes "response_allocations_fresh allocations" "map_of allocations number = Some descriptor"
  shows "\<not> code_known_response_number number"
  using assms(1) map_of_SomeD[OF assms(2)]
  by (auto simp: response_allocations_fresh_def list_all_iff)

lemma fresh_allocations_leave_legacy_numbers_unassigned:
  assumes fresh: "response_allocations_fresh allocations" and known: "code_known_response_number number"
  shows "map_of allocations number = None"
  using fresh known a_fresh_assignment_number_is_legacy_unknown[OF fresh]
  by (cases "map_of allocations number") auto

theorem legacy_known_responses_keep_their_status_and_call_compatibility:
  assumes "response_allocations_valid allocations" "code_known_response_number number"
  shows "response_extended_raw_status allocations raw_kind number committed =
      code_decode_raw_response_status raw_kind number committed"
    "code_response_call_shape family operation \<Longrightarrow>
      response_extended_compatible allocations added_calls family operation kind number committed =
        reference_response_compatible family operation kind number committed"
proof -
  have fresh: "response_allocations_fresh allocations" using assms(1)
    by (simp add: response_allocations_valid_def)
  have unassigned: "map_of allocations number = None"
    by (rule fresh_allocations_leave_legacy_numbers_unassigned[OF fresh assms(2)])
  show "response_extended_raw_status allocations raw_kind number committed =
      code_decode_raw_response_status raw_kind number committed"
    by (simp add: response_extended_raw_status_def code_decode_raw_response_status_def
        response_extended_status_def unassigned)
  show "code_response_call_shape family operation \<Longrightarrow>
      response_extended_compatible allocations added_calls family operation kind number committed =
        reference_response_compatible family operation kind number committed"
    using assms(2) by (simp add: response_extended_compatible_def code_response_compatible_def unassigned)
qed

lemma an_unallocated_status_keeps_the_legacy_decoder:
  assumes "map_of allocations number = None"
  shows "response_extended_raw_status allocations raw_kind number committed =
      code_decode_raw_response_status raw_kind number committed"
  using assms by (simp add: response_extended_raw_status_def code_decode_raw_response_status_def
      response_extended_status_def)

lemma a_known_extension_status_and_target_are_exact:
  assumes assigned: "map_of allocations number = Some (assigned_kind,assigned_commit,targets)"
  shows "response_extended_status allocations kind number committed =
      (if kind = assigned_kind \<and> committed = assigned_commit
       then Some (Code_Known_Response kind number) else None)"
    "response_extended_compatible allocations added_calls family operation kind number committed \<longleftrightarrow>
      kind = assigned_kind \<and> committed = assigned_commit \<and> (family,operation) \<in> set targets"
  using assigned by (simp_all add: response_extended_status_def response_extended_compatible_def)

lemma a_valid_extension_keeps_the_legacy_unknown_rule:
  assumes valid: "response_allocations_valid allocations"
    and assigned: "map_of allocations number = Some descriptor"
  shows "code_decode_response_status kind number committed =
    (if kind = Recorded_Result \<or> \<not> committed
     then Some (Code_Unknown_Response kind number) else None)"
proof -
  have fresh: "response_allocations_fresh allocations"
    using valid by (simp add: response_allocations_valid_def)
  show ?thesis
    by (rule an_unknown_number_is_accepted_only_as_its_declared_category
        [OF a_fresh_assignment_number_is_legacy_unknown[OF fresh assigned]])
qed

theorem a_valid_assigned_status_is_known_in_the_extension_and_unknown_in_the_legacy_decoder:
  assumes valid: "response_allocations_valid allocations"
    and assigned: "map_of allocations number = Some (kind,committed,targets)"
  shows "response_extended_status allocations kind number committed = Some (Code_Known_Response kind number)"
    "code_decode_response_status kind number committed = Some (Code_Unknown_Response kind number)"
proof -
  have row: "(number,(kind,committed,targets)) \<in> set allocations"
    by (rule map_of_SomeD[OF assigned])
  have in_range: "response_allocation_range kind committed number"
    using valid row
    by (auto simp: response_allocations_valid_def response_allocations_in_range_def list_all_iff)
  then have fits_legacy: "kind = Recorded_Result \<or> \<not> committed"
    by (cases kind) (simp_all add: response_allocation_range_def)
  show "response_extended_status allocations kind number committed = Some (Code_Known_Response kind number)"
    by (simp add: a_known_extension_status_and_target_are_exact(1)[OF assigned])
  show "code_decode_response_status kind number committed = Some (Code_Unknown_Response kind number)"
    by (simp add: a_valid_extension_keeps_the_legacy_unknown_rule[OF valid assigned] fits_legacy)
qed

definition legacy_status_with_original where
  "legacy_status_with_original original_bytes packet =
    (case decode_wire_core original_bytes of None \<Rightarrow> None | Some original \<Rightarrow>
      (case code_response_caller original of Inl reason \<Rightarrow> None | Inr expected_id \<Rightarrow>
        Option.bind (code_correlate_reference_response original packet)
          (\<lambda>(call_id,kind,number,position). if call_id = expected_id
            then code_decode_response_status kind number (position \<noteq> None) else None)))"

theorem legacy_correlated_status_uses_the_unknown_rule_for_an_already_recognized_call:
  assumes valid: "response_allocations_valid allocations"
    and assigned: "map_of allocations number = Some descriptor"
    and original: "decode_wire_core original_bytes = Some original"
    and caller: "code_response_caller original = Inr call_id"
    and old_call: "code_response_call_shape (wire_message_family original) (wire_opcode (wire_operation_body original))"
    and response: "wire_message_family (packet_core packet) = Wire_Ack"
      "wire_operation_body (packet_core packet) = reference_response_body call_id kind number position original"
      "reference_response_header_matches (packet_core packet) original call_id"
      "reference_response_position_matches original kind position"
  shows "legacy_status_with_original original_bytes packet = Some (Code_Unknown_Response kind number)"
proof -
  have fresh: "response_allocations_fresh allocations"
    using valid by (simp add: response_allocations_valid_def)
  have unknown: "\<not> code_known_response_number number"
    by (rule a_fresh_assignment_number_is_legacy_unknown[OF fresh assigned])
  have fits: "kind = Recorded_Result \<or> position = None"
    using response(4) by (auto simp: reference_response_position_matches_def)
  have compatible: "code_response_compatible (wire_message_family original) (wire_opcode (wire_operation_body original))
      kind number (position \<noteq> None)"
    using old_call fits unknown by (auto simp: code_response_compatible_def)
  have correlated: "code_correlate_reference_response original packet = Some (call_id,kind,number,position)"
    using response compatible
    by (simp add: code_correlate_reference_response_def Let_def the_reference_response_words_recover_the_typed_result)
  have status: "code_decode_response_status kind number (position \<noteq> None) =
      Some (Code_Unknown_Response kind number)"
    using fits by (auto simp: an_unknown_number_is_accepted_only_as_its_declared_category[OF unknown])
  show ?thesis using original caller correlated status
    by (simp add: legacy_status_with_original_def)
qed

lemma a_legacy_undecodable_original_cannot_reach_status:
  assumes "decode_wire_core original_bytes = None"
  shows "legacy_status_with_original original_bytes packet = None"
  using assms by (simp add: legacy_status_with_original_def)

definition response_extended_words where
  "response_extended_words allocations added_calls original call_id kind number position =
    (if response_extended_status allocations kind number (position \<noteq> None) =
        Some (Code_Known_Response kind number) \<and>
      response_extended_compatible allocations added_calls (wire_message_family original)
        (wire_opcode (wire_operation_body original)) kind number (position \<noteq> None)
     then Some (wire_words (reference_response_body call_id kind number position original)) else None)"

lemma the_extended_sender_uses_the_existing_response_word_format:
  assumes "response_extended_words allocations added_calls original call_id kind number position = Some words"
  shows "response_result_words words = Some (call_id,kind,number,position)"
    "words = wire_words (reference_response_body call_id kind number position original)"
  using assms by (auto simp: response_extended_words_def the_reference_response_words_recover_the_typed_result
      split: if_splits)

end
