theory Wire_Response_General_Receipt_Query
  imports Wire_Response_General_Correlation
begin

definition response_general_nested_receipt ::
  "nat \<Rightarrow> wire_packet \<Rightarrow> (response_fixed_decoded \<times> wire_core) option" where
  "response_general_nested_receipt fuel packet =
    (case response_fixed_parse_response fuel (packet_core packet) of Inl reason \<Rightarrow> None | Inr viewed \<Rightarrow>
      let nested = response_decoded_original viewed in
      if wire_message_family nested \<noteq> Wire_Query \<or> wire_opcode (wire_operation_body nested) \<noteq> 8 then None
      else (case code_decode_operand_tree fuel nested of
        Code_Tree_Ready (Code_Nested_Receipt inner) \<Rightarrow> Some (viewed,inner)
       | _ \<Rightarrow> None))"

lemma response_general_nested_receipt_is_selected_by_the_actual_decoder:
  assumes "response_general_nested_receipt fuel packet = Some (viewed,inner)"
  shows "response_fixed_parse_response fuel (packet_core packet) = Inr viewed"
    "wire_message_family (response_decoded_original viewed) = Wire_Query"
    "wire_opcode (wire_operation_body (response_decoded_original viewed)) = 8"
    "code_decode_operand_tree fuel (response_decoded_original viewed) = Code_Tree_Ready (Code_Nested_Receipt inner)"
  using assms by (auto simp: response_general_nested_receipt_def Let_def
    split: sum.splits code_operand_tree_result.splits code_nested_operand.splits if_splits)

theorem response_general_nested_receipt_consumes_its_actual_inner_identity_and_commit_check:
  assumes selected: "response_general_nested_receipt fuel packet = Some (viewed,inner)"
  obtains native where "wire_version inner = 6"
    "code_same_original (response_decoded_original viewed) inner"
    "decode_native_call_prefix inner = Some native"
    "native_id native = response_decoded_id viewed"
    "wire_message_family inner = Wire_State_Sync \<and> wire_opcode (wire_operation_body inner) = 1
       \<longrightarrow> code_response_commit_matches (response_decoded_position viewed) (cut_revision (native_cut native))"
proof -
  have parsed: "response_fixed_parse_response fuel (packet_core packet) = Inr viewed"
    by (rule response_general_nested_receipt_is_selected_by_the_actual_decoder(1)[OF selected])
  have actual_receipt: "code_decode_operand_tree fuel (response_decoded_original viewed) = Code_Tree_Ready (Code_Nested_Receipt inner)"
    by (rule response_general_nested_receipt_is_selected_by_the_actual_decoder(4)[OF selected])
  obtain classified where tree: "code_decode_operand_tree fuel (response_decoded_original viewed) = Code_Tree_Ready classified"
    and guarded: "code_check_nested_response (response_decoded_original viewed) classified
        (response_decoded_id viewed) (response_decoded_position viewed) = None"
    by (rule response_fixed_parser_preserves_the_actual_nested_fields_and_checks[OF parsed]) blast
  have same_class: "classified = Code_Nested_Receipt inner" using tree actual_receipt by simp
  have checked: "code_check_nested_response (response_decoded_original viewed) (Code_Nested_Receipt inner)
      (response_decoded_id viewed) (response_decoded_position viewed) = None"
    using guarded same_class by simp
  have same_source: "code_same_original (response_decoded_original viewed) inner"
  proof (rule ccontr)
    assume absent: "\<not> code_same_original (response_decoded_original viewed) inner"
    have "code_check_nested_response (response_decoded_original viewed) (Code_Nested_Receipt inner)
        (response_decoded_id viewed) (response_decoded_position viewed) = Some Invalid_Wire_Source"
      using absent by simp
    then show False using checked by simp
  qed
  obtain native where version: "wire_version inner = 6"
    and prefix: "decode_native_call_prefix inner = Some native"
    and identity: "native_id native = response_decoded_id viewed"
    and position: "wire_message_family inner = Wire_State_Sync \<and> wire_opcode (wire_operation_body inner) = 1
       \<longrightarrow> code_response_commit_matches (response_decoded_position viewed) (cut_revision (native_cut native))"
    by (rule a_response_around_an_exact_receipt_checks_the_inner_version_identity_and_debit_cut[OF checked]) blast
  show thesis by (rule that[OF version same_source prefix identity position])
qed

theorem response_general_nested_receipt_keeps_the_exact_response_word_tuple:
  assumes selected: "response_general_nested_receipt fuel packet = Some (viewed,inner)"
  shows "response_result_words (wire_words (wire_operation_body (packet_core packet))) = Some
    (response_decoded_id viewed,response_decoded_kind viewed,response_decoded_number viewed,response_decoded_position viewed)"
proof -
  have parsed: "response_fixed_parse_response fuel (packet_core packet) = Inr viewed"
    by (rule response_general_nested_receipt_is_selected_by_the_actual_decoder(1)[OF selected])
  show ?thesis
    by (rule response_fixed_parser_preserves_the_actual_nested_fields_and_checks[OF parsed]) blast
qed

lemma response_general_query_has_no_depth_one_response_caller:
  fixes query :: wire_core
  assumes "wire_message_family query = Wire_Query"
  shows "code_response_caller query = Inl Invalid_Wire_Format"
  using assms by (simp add: code_response_caller_def One_nat_def Let_def
    split: option.splits list.splits prod.splits if_splits)

lemma response_general_query_eight_is_refused_at_one_core_level:
  fixes query :: wire_core
  assumes "wire_message_family query = Wire_Query" "wire_opcode (wire_operation_body query) = 8"
  shows "code_decode_operand_tree 1 query = Code_Tree_Refused Invalid_Wire_Format"
  using assms by (simp add: One_nat_def Let_def split: list.splits prod.splits if_splits)

theorem response_general_structural_receipt_requires_the_actual_larger_nesting_depth:
  assumes selected: "response_general_nested_receipt fuel packet = Some (viewed,inner)"
  shows "2 \<le> fuel" "3 \<le> Suc fuel"
proof -
  have tree: "code_decode_operand_tree fuel (response_decoded_original viewed) = Code_Tree_Ready (Code_Nested_Receipt inner)"
    by (rule response_general_nested_receipt_is_selected_by_the_actual_decoder(4)[OF selected])
  have not_zero: "fuel \<noteq> 0"
    using tree by (cases fuel; simp_all)
  have one_refused: "code_decode_operand_tree 1 (response_decoded_original viewed) = Code_Tree_Refused Invalid_Wire_Format"
    by (rule response_general_query_eight_is_refused_at_one_core_level)
      (rule response_general_nested_receipt_is_selected_by_the_actual_decoder(2,3)[OF selected])+
  have not_one: "fuel \<noteq> 1" using tree one_refused by auto
  have lower_bound: "2 \<le> fuel" using not_zero not_one by arith
  show "2 \<le> fuel" by (rule lower_bound)
  show "3 \<le> Suc fuel" using lower_bound by arith
qed

theorem response_general_expected_query_is_format_refused_after_response_shape:
  fixes query :: wire_core and packet :: wire_packet
  assumes "response_fixed_parse_response fuel (packet_core packet) = Inr viewed"
    "wire_message_family query = Wire_Query"
    "response_decoded_original_bytes viewed = encode_wire_core query"
  shows "response_fixed_validate (Suc fuel) query packet = Inl Invalid_Wire_Format"
  using assms response_fixed_expected_query_decode_is_read_or_format_error[OF assms(2)]
  by (auto simp: response_fixed_validate_def split: sum.splits)

theorem response_general_query_decode_success_and_original_mismatch_is_replay:
  fixes query :: wire_core and packet :: wire_packet
  assumes "response_fixed_parse_response fuel (packet_core packet) = Inr viewed"
    "response_fixed_expected_decode query = Inr Code_Nested_Other"
    "response_decoded_original_bytes viewed \<noteq> encode_wire_core query"
  shows "response_fixed_validate (Suc fuel) query packet = Inl Conflicting_Wire_Replay"
  by (rule response_fixed_original_mismatch_precedes_caller_projection[OF assms])

theorem response_general_query_eight_decode_error_precedes_any_original_mismatch:
  fixes query :: wire_core and packet :: wire_packet
  assumes "response_fixed_parse_response fuel (packet_core packet) = Inr viewed"
    "wire_message_family query = Wire_Query" "wire_opcode (wire_operation_body query) = 8"
  shows "response_fixed_validate (Suc fuel) query packet = Inl Invalid_Wire_Format"
  by (rule response_fixed_expected_decode_error_precedes_original_byte_comparison[OF assms(1)])
    (rule response_fixed_expected_query_eight_fails_before_byte_comparison[OF assms(2,3)])

theorem response_general_query_is_never_an_accepted_expected_native_call:
  fixes query :: wire_core and packet :: wire_packet
  assumes "wire_message_family query = Wire_Query"
  shows "response_fixed_validate depth query packet \<noteq> Inr result"
  using response_fixed_expected_query_decode_is_read_or_format_error[OF assms]
  by (cases depth; auto simp: response_fixed_validate_def split: sum.splits)

theorem response_general_current_client_does_not_accept_an_expected_query:
  fixes expected :: wire_packet
  assumes query: "wire_message_family (packet_core expected) = Wire_Query"
  shows "response_fixed_admit curve_verify channel current expected bytes \<noteq> Inr (result,status)"
proof
  assume admitted: "response_fixed_admit curve_verify channel current expected bytes = Inr (result,status)"
  obtain packet where checked:
      "response_fixed_validate (response_client_max_nesting current) (packet_core expected) (packet::wire_packet) = Inr result"
    by (rule response_fixed_admission_keeps_the_actual_client_boundary_and_parsed_value[OF admitted]) blast
  have refused: "response_fixed_validate (response_client_max_nesting current) (packet_core expected) packet \<noteq> Inr result"
    by (rule response_general_query_is_never_an_accepted_expected_native_call[OF query])
  show False using checked refused by contradiction
qed

theorem response_general_query_cannot_pass_signed_response_preparation:
  assumes decoded: "decode_wire_packet bytes = Some packet"
    and query: "wire_message_family (packet_core packet) = Wire_Query"
  shows "response_fixed_original_preflight config channel site curve_verify frame_limit bytes \<noteq> Inr (actual,call_id)"
  using decoded response_general_query_has_no_depth_one_response_caller[OF query]
  by (auto simp: response_fixed_original_preflight_def code_original_response_preflight_def Let_def
    split: option.splits sum.splits prod.splits if_splits)

theorem response_general_query_original_cannot_produce_a_signed_emission:
  assumes decoded: "decode_wire_packet bytes = Some packet"
    and query: "wire_message_family (packet_core packet) = Wire_Query"
  shows "response_fixed_encode_for_received_original hash curve_sign signing_key curve_verify config channel site
      parameters_clock signing_clock bytes observation frame_limit \<noteq> Inr emission"
proof -
  have refused: "response_fixed_original_preflight config channel site curve_verify frame_limit bytes \<noteq> Inr pair" for pair
  proof -
    obtain actual original_id where parts: "pair = (actual,original_id)"
      by (cases pair) auto
    show ?thesis unfolding parts
      by (rule response_general_query_cannot_pass_signed_response_preparation[OF decoded query])
  qed
  show ?thesis using refused
    by (auto simp: response_fixed_encode_for_received_original_def split: sum.splits prod.splits)
qed

lemma response_general_distinct_canonical_families_have_distinct_original_bytes:
  fixes first second :: wire_core
  assumes "wire_core_wellformed first" "wire_core_wellformed second"
    "wire_message_family first \<noteq> wire_message_family second"
  shows "encode_wire_core first \<noteq> encode_wire_core second"
proof
  assume equal_bytes: "encode_wire_core first = encode_wire_core second"
  have "decode_wire_core (encode_wire_core first) = decode_wire_core (encode_wire_core second)"
    by (rule arg_cong[OF equal_bytes])
  then have "first = second"
    by (simp only: wellformed_canonical_core_has_a_two_way_encoding[OF assms(1)]
      wellformed_canonical_core_has_a_two_way_encoding[OF assms(2)] option.inject)
  then show False using assms(3) by simp
qed

theorem response_general_receipt_wrapper_cannot_be_relabelled_as_its_inner_expected_call:
  fixes packet :: wire_packet and inner :: wire_core
  assumes selected: "response_general_nested_receipt fuel packet = Some (viewed,inner)"
    and expected: "wire_core_wellformed inner"
    and call: "code_decode_source_call_operand inner = Code_Source_Call_Ready operand"
  shows "response_fixed_validate (Suc fuel) inner packet = Inl Conflicting_Wire_Replay"
proof -
  have parsed: "response_fixed_parse_response fuel (packet_core packet) = Inr viewed"
    by (rule response_general_nested_receipt_is_selected_by_the_actual_decoder(1)[OF selected])
  have query: "wire_message_family (response_decoded_original viewed) = Wire_Query"
    by (rule response_general_nested_receipt_is_selected_by_the_actual_decoder(2)[OF selected])
  have inner_family: "wire_message_family inner \<noteq> Wire_Query"
    using call by (auto simp: code_decode_source_call_operand_def Let_def split: if_splits)
  have original_decoded:
      "decode_wire_core (response_decoded_original_bytes viewed) = Some (response_decoded_original viewed)"
    by (rule response_fixed_parser_preserves_the_actual_nested_fields_and_checks[OF parsed]) blast
  have outer_domain: "wire_core_wellformed (response_decoded_original viewed)"
    using accepted_core_bytes_preserve_all_original_fields[OF original_decoded] by simp
  have exact_outer: "response_decoded_original_bytes viewed = encode_wire_core (response_decoded_original viewed)"
    using accepted_core_bytes_preserve_all_original_fields[OF original_decoded] by simp
  have different: "encode_wire_core (response_decoded_original viewed) \<noteq> encode_wire_core inner"
    by (rule response_general_distinct_canonical_families_have_distinct_original_bytes[OF outer_domain expected])
      (use query inner_family in simp)
  have actual_caller: "code_response_caller inner = Inr (native_id (code_source_operand_native operand))"
  proof -
    have one_tree: "code_decode_operand_tree 1 inner = Code_Tree_Ready (response_general_nested_operand operand)"
      using response_general_actual_call_has_the_same_recursive_source_class[OF call,where fuel=0]
      by (simp only: One_nat_def)
    show ?thesis using one_tree by (cases operand) (simp_all add: code_response_caller_def)
  qed
  show ?thesis
    by (rule response_fixed_original_byte_conflict_is_a_replay_refusal_after_shape_and_caller[OF parsed actual_caller])
      (use exact_outer different in simp)
qed

lemma response_general_format_and_original_conflict_keep_the_source_error_numbers:
  "code_transport_refusal_number Invalid_Wire_Format = 70"
  "code_transport_refusal_number Conflicting_Wire_Replay = 76"
  by simp_all

text \<open>
  Source ack can structurally decode a nested Query8 receipt at larger depth,
  checking its actual inner identity and optional Debit commit. That does not
  make Query an expected native call for response.rs: caller_id accepts only
  Ordinary/Legal/Spend and the expected decoder uses depth1. Local format and
  replay refusals above are not fabricated signed Response packets.
\<close>

end
