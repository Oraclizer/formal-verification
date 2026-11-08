theory Wire_Response_Fixed_Validation
  imports Wire_Response_Fixed_Expected
begin

record response_fixed_decoded =
  response_decoded_id :: client_call_id
  response_decoded_kind :: reference_response_kind
  response_decoded_number :: nat
  response_decoded_position :: "nat option"
  response_decoded_original_bytes :: wire_bytes
  response_decoded_original :: wire_core

definition response_fixed_parse_response where
  "response_fixed_parse_response fuel core =
    (if wire_message_family core \<noteq> Wire_Ack \<or> wire_opcode (wire_operation_body core) \<noteq> 2 \<or>
       wire_deadline (wire_operation_body core) \<noteq> Deadline_Absent then Inl Invalid_Wire_Format
     else case wire_blobs (wire_operation_body core) of [raw] \<Rightarrow>
       (case decode_wire_core raw of None \<Rightarrow> Inl Invalid_Wire_Format | Some nested \<Rightarrow>
         case code_decode_operand_tree fuel nested of Code_Tree_Refused reason \<Rightarrow> Inl reason
          | Code_Tree_Pending \<Rightarrow> Inl Invalid_Wire_Format
          | Code_Tree_Ready classified \<Rightarrow>
            (case response_result_words (wire_words (wire_operation_body core)) of None \<Rightarrow> Inl Invalid_Wire_Format
             | Some (call_id,kind,number,position) \<Rightarrow>
               if kind \<noteq> Recorded_Result \<and> position \<noteq> None then Inl Invalid_Wire_Format
               else if wire_version nested \<noteq> wire_version core \<or> wire_deployment nested \<noteq> wire_deployment core \<or>
                 wire_principal nested \<noteq> fst call_id \<or> wire_source_domain nested \<noteq> wire_target_domain core \<or>
                 wire_target_domain nested \<noteq> wire_source_domain core then Inl Invalid_Wire_Source
               else case code_check_nested_response nested classified call_id position of Some reason \<Rightarrow> Inl reason
                | None \<Rightarrow> Inr \<lparr>response_decoded_id = call_id,response_decoded_kind = kind,
                    response_decoded_number = number,response_decoded_position = position,
                    response_decoded_original_bytes = raw,response_decoded_original = nested\<rparr>))
       | _ \<Rightarrow> Inl Invalid_Wire_Format)"

lemma response_fixed_parser_preserves_the_actual_nested_fields_and_checks:
  assumes "response_fixed_parse_response fuel core = Inr viewed"
  obtains classified
  where
    "wire_message_family core = Wire_Ack"
    "wire_opcode (wire_operation_body core) = 2"
    "wire_deadline (wire_operation_body core) = Deadline_Absent"
    "wire_blobs (wire_operation_body core) = [response_decoded_original_bytes viewed]"
    "decode_wire_core (response_decoded_original_bytes viewed) = Some (response_decoded_original viewed)"
    "code_decode_operand_tree fuel (response_decoded_original viewed) = Code_Tree_Ready classified"
    "response_result_words (wire_words (wire_operation_body core)) = Some
      (response_decoded_id viewed,response_decoded_kind viewed,response_decoded_number viewed,response_decoded_position viewed)"
    "response_decoded_position viewed = None \<or> response_decoded_kind viewed = Recorded_Result"
    "wire_version (response_decoded_original viewed) = wire_version core"
    "wire_deployment (response_decoded_original viewed) = wire_deployment core"
    "wire_principal (response_decoded_original viewed) = fst (response_decoded_id viewed)"
    "wire_source_domain (response_decoded_original viewed) = wire_target_domain core"
    "wire_target_domain (response_decoded_original viewed) = wire_source_domain core"
    "code_check_nested_response (response_decoded_original viewed) classified
       (response_decoded_id viewed) (response_decoded_position viewed) = None"
  using assms
  by (auto simp: response_fixed_parse_response_def split: option.splits list.splits
      prod.splits code_operand_tree_result.splits if_splits)

theorem response_fixed_parser_reuses_the_existing_recursive_source_decoder:
  assumes "response_fixed_parse_response fuel core = Inr viewed"
  shows "code_decode_operand_tree (Suc fuel) core = Code_Tree_Ready Code_Nested_Response"
proof -
  obtain classified where parsed:
      "wire_message_family core = Wire_Ack"
      "wire_opcode (wire_operation_body core) = 2"
      "wire_deadline (wire_operation_body core) = Deadline_Absent"
      "wire_blobs (wire_operation_body core) = [response_decoded_original_bytes viewed]"
      "decode_wire_core (response_decoded_original_bytes viewed) = Some (response_decoded_original viewed)"
      "code_decode_operand_tree fuel (response_decoded_original viewed) = Code_Tree_Ready classified"
      "response_result_words (wire_words (wire_operation_body core)) = Some
        (response_decoded_id viewed,response_decoded_kind viewed,response_decoded_number viewed,response_decoded_position viewed)"
      "response_decoded_position viewed = None \<or> response_decoded_kind viewed = Recorded_Result"
      "wire_version (response_decoded_original viewed) = wire_version core"
      "wire_deployment (response_decoded_original viewed) = wire_deployment core"
      "wire_principal (response_decoded_original viewed) = fst (response_decoded_id viewed)"
      "wire_source_domain (response_decoded_original viewed) = wire_target_domain core"
      "wire_target_domain (response_decoded_original viewed) = wire_source_domain core"
      "code_check_nested_response (response_decoded_original viewed) classified
        (response_decoded_id viewed) (response_decoded_position viewed) = None"
    by (rule response_fixed_parser_preserves_the_actual_nested_fields_and_checks[OF assms]) blast
  have kind_guard: "\<not> (response_decoded_kind (viewed :: response_fixed_decoded) \<noteq> Recorded_Result \<and>
      response_decoded_position viewed \<noteq> None)"
    using parsed(8)
    by (cases "response_decoded_position viewed = None"; auto)
  have finished_leaf: "code_response_tree_finish core (response_decoded_original viewed) classified =
      Code_Tree_Ready Code_Nested_Response"
    using parsed(7,9-14) kind_guard
    by (simp add: code_response_tree_finish_def Let_def)
  have outer_only: "code_decode_operand_tree (Suc fuel) core =
      code_response_tree_after_nested core (response_decoded_original viewed) (Code_Tree_Ready classified)"
    using parsed(1-6) by (simp add: Let_def)
  show ?thesis unfolding outer_only
    by (simp add: code_response_tree_after_nested_def finished_leaf)
qed

definition response_fixed_validate where
  "response_fixed_validate depth expected packet =
    (case depth of 0 \<Rightarrow> Inl Invalid_Wire_Format | Suc fuel \<Rightarrow>
      (case response_fixed_parse_response fuel (packet_core packet) of Inl reason \<Rightarrow> Inl reason | Inr viewed \<Rightarrow>
        (case response_fixed_expected_decode expected of Inl reason \<Rightarrow> Inl reason | Inr decoded_expected \<Rightarrow>
          if response_decoded_original_bytes viewed \<noteq> encode_wire_core expected then Inl Conflicting_Wire_Replay
          else (case response_fixed_caller_from_decoded decoded_expected of Inl reason \<Rightarrow> Inl reason | Inr original_id \<Rightarrow>
            if response_decoded_id viewed \<noteq> original_id then Inl Conflicting_Wire_Replay
            else (case code_decode_response_status (response_decoded_kind viewed) (response_decoded_number viewed)
               (response_decoded_position viewed \<noteq> None) of None \<Rightarrow> Inl Invalid_Wire_Format
            | Some status \<Rightarrow>
              if code_known_response_number (response_decoded_number viewed) \<and>
                \<not> reference_response_compatible (wire_message_family expected) (wire_opcode (wire_operation_body expected))
                   (response_decoded_kind viewed) (response_decoded_number viewed) (response_decoded_position viewed \<noteq> None)
              then Inl Invalid_Wire_Format
              else Inr (response_decoded_id viewed,response_decoded_kind viewed,
                         response_decoded_number viewed,response_decoded_position viewed))))))"

lemma response_fixed_expected_decode_error_precedes_original_byte_comparison:
  fixes expected :: wire_core and packet :: wire_packet
  assumes "response_fixed_parse_response fuel (packet_core packet) = Inr viewed"
    "response_fixed_expected_decode expected = Inl reason"
  shows "response_fixed_validate (Suc fuel) expected packet = Inl reason"
  using assms by (simp add: response_fixed_validate_def)

lemma response_fixed_original_mismatch_precedes_caller_projection:
  fixes expected :: wire_core and packet :: wire_packet
  assumes "response_fixed_parse_response fuel (packet_core packet) = Inr viewed"
    "response_fixed_expected_decode expected = Inr decoded"
    "response_decoded_original_bytes viewed \<noteq> encode_wire_core expected"
  shows "response_fixed_validate (Suc fuel) expected packet = Inl Conflicting_Wire_Replay"
  using assms by (simp add: response_fixed_validate_def)

lemma response_fixed_matching_original_reaches_the_actual_caller_projection:
  fixes expected :: wire_core and packet :: wire_packet
  assumes "response_fixed_parse_response fuel (packet_core packet) = Inr viewed"
    "response_fixed_expected_decode expected = Inr decoded"
    "response_decoded_original_bytes viewed = encode_wire_core expected"
    "response_fixed_caller_from_decoded decoded = Inl reason"
  shows "response_fixed_validate (Suc fuel) expected packet = Inl reason"
  using assms by (simp add: response_fixed_validate_def)

lemma response_fixed_validation_keeps_the_exact_original_and_caller:
  assumes "response_fixed_validate (Suc fuel) expected packet = Inr (call_id,kind,number,position)"
  obtains viewed where "response_fixed_parse_response fuel (packet_core packet) = Inr viewed"
    "response_decoded_original_bytes viewed = encode_wire_core expected"
    "code_response_caller expected = Inr call_id"
    "response_decoded_id viewed = call_id" "response_decoded_kind viewed = kind"
    "response_decoded_number viewed = number" "response_decoded_position viewed = position"
    "code_decode_response_status kind number (position \<noteq> None) \<noteq> None"
    "code_known_response_number number \<longrightarrow>
      reference_response_compatible (wire_message_family expected) (wire_opcode (wire_operation_body expected)) kind number (position \<noteq> None)"
  using assms
  by (auto simp: response_fixed_validate_def
    dest: response_fixed_actual_expected_and_caller_keep_the_original_call_id
    split: sum.splits option.splits if_splits)

lemma response_fixed_direct_debit_caller_is_the_actual_native_id:
  assumes "wire_message_family original = Wire_State_Sync" "wire_opcode (wire_operation_body original) = 1"
    "code_decode_ordinary original = Code_Ordinary_Ready native credential versions (Wire_Debit generation)"
  shows "code_response_caller original = Inr (native_id native)"
    "code_decode_operand_tree (Suc fuel) original = Code_Tree_Ready (Code_Nested_Ordinary native (Wire_Debit generation))"
  using assms by (simp_all add: code_response_caller_def code_decode_operand_tree.simps code_ordinary_tree_def Let_def)

theorem response_fixed_direct_debit_validation_consumes_the_existing_hol_correlation:
  assumes original: "wire_core_wellformed original"
    and family: "wire_message_family original = Wire_State_Sync"
    and operation: "wire_opcode (wire_operation_body original) = 1"
    and decoded: "code_decode_ordinary original = Code_Ordinary_Ready native credential versions (Wire_Debit generation)"
    and accepted: "response_fixed_validate (Suc (Suc fuel)) original packet = Inr (call_id,kind,number,position)"
  shows "code_correlate_reference_response original packet = Some (call_id,kind,number,position)"
proof -
  obtain viewed where selected: "response_fixed_parse_response (Suc fuel) (packet_core packet) = Inr viewed"
    and raw: "response_decoded_original_bytes viewed = encode_wire_core original"
    and caller: "code_response_caller original = Inr call_id"
    and projected_fields: "response_decoded_id viewed = call_id" "response_decoded_kind viewed = kind"
      "response_decoded_number viewed = number" "response_decoded_position viewed = position"
    and compatible: "code_known_response_number number \<longrightarrow>
      reference_response_compatible (wire_message_family original) (wire_opcode (wire_operation_body original)) kind number (position \<noteq> None)"
    by (rule response_fixed_validation_keeps_the_exact_original_and_caller[OF accepted]) blast
  obtain classified where parsed:
      "wire_message_family (packet_core packet) = Wire_Ack"
      "wire_opcode (wire_operation_body (packet_core packet)) = 2"
      "wire_deadline (wire_operation_body (packet_core packet)) = Deadline_Absent"
      "wire_blobs (wire_operation_body (packet_core packet)) = [response_decoded_original_bytes viewed]"
      "decode_wire_core (response_decoded_original_bytes viewed) = Some (response_decoded_original viewed)"
      "code_decode_operand_tree (Suc fuel) (response_decoded_original viewed) = Code_Tree_Ready classified"
      "response_result_words (wire_words (wire_operation_body (packet_core packet))) = Some
        (response_decoded_id viewed,response_decoded_kind viewed,response_decoded_number viewed,response_decoded_position viewed)"
      "response_decoded_position viewed = None \<or> response_decoded_kind viewed = Recorded_Result"
      "wire_version (response_decoded_original viewed) = wire_version (packet_core packet)"
      "wire_deployment (response_decoded_original viewed) = wire_deployment (packet_core packet)"
      "wire_principal (response_decoded_original viewed) = fst (response_decoded_id viewed)"
      "wire_source_domain (response_decoded_original viewed) = wire_target_domain (packet_core packet)"
      "wire_target_domain (response_decoded_original viewed) = wire_source_domain (packet_core packet)"
      "code_check_nested_response (response_decoded_original viewed) classified
         (response_decoded_id viewed) (response_decoded_position viewed) = None"
    by (rule response_fixed_parser_preserves_the_actual_nested_fields_and_checks[OF selected]) blast
  have same_original: "response_decoded_original viewed = original"
    using parsed(5) raw wellformed_canonical_core_has_a_two_way_encoding[OF original] by simp
  have source_tree: "code_decode_operand_tree (Suc fuel) original =
      Code_Tree_Ready (Code_Nested_Ordinary native (Wire_Debit generation))"
    by (rule response_fixed_direct_debit_caller_is_the_actual_native_id(2)[OF family operation decoded])
  have actual_class: "classified = Code_Nested_Ordinary native (Wire_Debit generation)"
    using parsed(6) source_tree same_original by simp
  have checked_nested_debit: "code_check_nested_response original
      (Code_Nested_Ordinary native (Wire_Debit generation)) call_id position = None"
    using parsed(14) same_original actual_class projected_fields by simp
  have nested_guards: "native_id native = call_id \<and>
      code_response_commit_matches position (cut_revision (native_cut native))"
    using checked_nested_debit by (auto split: if_splits)
  have actual_call_id: "native_id native = call_id" by (rule conjunct1[OF nested_guards])
  have commit_checked: "code_response_commit_matches position (cut_revision (native_cut native))"
    by (rule conjunct2[OF nested_guards])
  have prefix: "decode_native_call_prefix original = Some native"
    by (rule every_source_ordinary_result_retains_the_existing_decoded_operands(1)[OF decoded])
  have body_words: "wire_words (wire_operation_body (packet_core packet)) =
      wire_words (reference_response_body call_id kind number position original)"
    by (rule response_fixed_parsed_words_reconstruct_the_actual_response_body)
      (use parsed(7) projected_fields in simp)
  have exact_body: "wire_operation_body (packet_core packet) = reference_response_body call_id kind number position original"
    using parsed(2-4) raw body_words
    by (cases "wire_operation_body (packet_core packet)") (simp add: reference_response_body_def)
  have exact_header: "reference_response_header_matches (packet_core packet) original call_id"
    using parsed(9-13) same_original projected_fields prefix actual_call_id
    by (auto simp: reference_response_header_matches_def)
  have kind_or_absent: "position = None \<or> kind = Recorded_Result"
    using parsed(8) projected_fields by simp
  have retained_positions: "\<forall>retained_native revision.
      wire_message_family original = Wire_State_Sync \<and> wire_opcode (wire_operation_body original) = 1 \<and>
      decode_native_call_prefix original = Some retained_native \<and> position = Some revision
      \<longrightarrow> revision = cut_revision (native_cut retained_native)"
  proof (intro allI impI)
    fix retained_native revision
    assume selected_position: "wire_message_family original = Wire_State_Sync \<and>
      wire_opcode (wire_operation_body original) = 1 \<and>
      decode_native_call_prefix original = Some retained_native \<and> position = Some revision"
    have same_native: "retained_native = native" using prefix selected_position by auto
    have actual_position: "position = Some revision" using selected_position by blast
    have actual_revision: "revision = cut_revision (native_cut native)"
      using commit_checked actual_position by (simp add: code_response_commit_matches_def)
    show "revision = cut_revision (native_cut retained_native)"
      using same_native actual_revision by simp
  qed
  have exact_position: "reference_response_position_matches original kind position"
    unfolding reference_response_position_matches_def
    by (rule conjI[OF kind_or_absent retained_positions])
  have extended: "code_response_compatible (wire_message_family original)
      (wire_opcode (wire_operation_body original)) kind number (position \<noteq> None)"
    using compatible parsed(8) projected_fields family operation
    by (auto simp: code_response_compatible_def code_response_call_shape_def)
  show ?thesis using parsed(1,7) projected_fields exact_body exact_header exact_position extended
    by (simp add: code_correlate_reference_response_def Let_def)
qed

text \<open>
  Source anchors: operands.rs ack and response.rs validate_response. Parsing
  returns the actual id/kind/code/optional commit/original bytes before status
  interpretation. The direct Debit correlation theorem consumes the recursive
  nested decoder's real commit check, not an assumed retained-commit annotation.
  It does not establish that a caller-supplied Outcome was actually committed.
  General legal/spend correlation and receipt-of-call nesting remain separate
  interfaces; the parser and status conversion are defined for those branches.
\<close>

end
