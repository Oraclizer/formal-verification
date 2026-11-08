theory Wire_Response_General_Correlation
  imports Wire_Response_General_Getters
begin

theorem response_general_nonordinary_validation_consumes_hol_correlation:
  fixes original :: wire_core and packet :: wire_packet
  assumes formed: "wire_core_wellformed original"
    and chosen: "response_general_nonordinary original = Some operand"
    and accepted: "response_fixed_validate (Suc fuel) original packet = Inr (call_id,kind,number,position)"
  shows "code_correlate_reference_response original packet = Some (call_id,kind,number,position)"
proof -
  obtain viewed where selected: "response_fixed_parse_response fuel (packet_core packet) = Inr viewed"
    and raw: "response_decoded_original_bytes viewed = encode_wire_core original"
    and caller: "code_response_caller original = Inr call_id"
    and projected: "response_decoded_id viewed = call_id" "response_decoded_kind viewed = kind"
      "response_decoded_number viewed = number" "response_decoded_position viewed = position"
    and compatible: "code_known_response_number number \<longrightarrow>
      reference_response_compatible (wire_message_family original) (wire_opcode (wire_operation_body original))
        kind number (position \<noteq> None)"
    by (rule response_fixed_validation_keeps_the_exact_original_and_caller[OF accepted]) blast
  obtain classified where parsed:
      "wire_message_family (packet_core packet) = Wire_Ack"
      "wire_opcode (wire_operation_body (packet_core packet)) = 2"
      "wire_deadline (wire_operation_body (packet_core packet)) = Deadline_Absent"
      "wire_blobs (wire_operation_body (packet_core packet)) = [response_decoded_original_bytes viewed]"
      "decode_wire_core (response_decoded_original_bytes viewed) = Some (response_decoded_original viewed)"
      "code_decode_operand_tree fuel (response_decoded_original viewed) = Code_Tree_Ready classified"
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
    using parsed(5) raw wellformed_canonical_core_has_a_two_way_encoding[OF formed] by simp
  have actual_caller: "code_response_caller original = Inr (native_id (code_source_operand_native operand))"
    by (rule response_general_selected_caller_is_the_fixed_native_id(1)[OF chosen])
  have actual_id: "native_id (code_source_operand_native operand) = call_id"
    using actual_caller caller by simp
  have prefix: "decode_native_call_prefix original = Some (code_source_operand_native operand)"
    by (rule response_general_selected_caller_is_the_fixed_native_id(2)[OF chosen])
  have exact_words: "wire_words (wire_operation_body (packet_core packet)) =
      wire_words (reference_response_body call_id kind number position original)"
    by (rule response_fixed_parsed_words_reconstruct_the_actual_response_body)
      (use parsed(7) projected in simp)
  have exact_body: "wire_operation_body (packet_core packet) = reference_response_body call_id kind number position original"
    using parsed(2-4) raw exact_words
    by (cases "wire_operation_body (packet_core packet)") (simp add: reference_response_body_def)
  have exact_header: "reference_response_header_matches (packet_core packet) original call_id"
    using parsed(9-13) same_original projected prefix actual_id
    by (auto simp: reference_response_header_matches_def)
  have nondebit: "\<not> (wire_message_family original = Wire_State_Sync \<and> wire_opcode (wire_operation_body original) = 1)"
    by (rule response_general_selected_legal_or_spend_is_not_an_original_debit[OF chosen])
  have kind_or_absent: "position = None \<or> kind = Recorded_Result"
    using parsed(8) projected by simp
  have exact_position: "reference_response_position_matches original kind position"
    using nondebit kind_or_absent
    by (auto simp: reference_response_position_matches_def)
  have actual_shape: "code_response_call_shape (wire_message_family original) (wire_opcode (wire_operation_body original))"
    by (rule response_general_selected_call_has_the_actual_native_response_shape[OF chosen])
  have extended: "code_response_compatible (wire_message_family original)
      (wire_opcode (wire_operation_body original)) kind number (position \<noteq> None)"
    using compatible actual_shape kind_or_absent
    by (auto simp: code_response_compatible_def split: if_splits)
  show ?thesis using parsed(1,7) projected exact_body exact_header exact_position extended
    by (simp add: code_correlate_reference_response_def Let_def)
qed

theorem response_general_source_emission_correlates_for_the_selected_legal_or_spend:
  fixes original :: wire_core
  assumes emitted: "response_fixed_encode hash curve_sign signing_key curve_verify config channel parameters_clock signing_clock
      original call_id observation frame_limit = Inr emission"
    and formed: "wire_core_wellformed original"
    and selected: "response_general_nonordinary original = Some operand"
  shows "code_correlate_reference_response original (response_emission_packet emission) =
      Some (response_emission_converted emission)"
proof -
  have source_checked: "response_fixed_validate 2 original (response_emission_packet emission) = Inr (response_emission_verified emission)"
    by (rule response_fixed_encoding_has_actual_source_getter_preimage_and_postcheck_evidence[OF emitted]) blast
  obtain actual_id kind number position where result:
      "response_emission_verified emission = (actual_id,kind,number,position)"
    by (cases "response_emission_verified emission" rule: prod_cases4) auto
  have actual_checked: "response_fixed_validate (Suc 1) original (response_emission_packet emission) =
      Inr (actual_id,kind,number,position)"
    using source_checked result by (simp only: numeral_2_eq_2 One_nat_def)
  have correlated: "code_correlate_reference_response original (response_emission_packet emission) =
      Some (response_emission_verified emission)"
    unfolding result
    by (rule response_general_nonordinary_validation_consumes_hol_correlation[OF formed selected actual_checked])
  show ?thesis
    using correlated response_fixed_emission_returns_the_exact_converted_kind_code_and_position[OF emitted] by simp
qed

theorem response_general_current_client_correlates_the_same_legal_or_spend_original:
  fixes expected :: wire_packet
  assumes admitted: "response_fixed_admit curve_verify channel current expected bytes = Inr (result,status)"
    and depth: "response_client_max_nesting current = Suc fuel"
    and formed: "wire_core_wellformed (packet_core expected)"
    and selected: "response_general_nonordinary (packet_core expected) = Some operand"
  shows "map_option (code_correlate_reference_response (packet_core expected)) (decode_wire_packet bytes) = Some (Some result)"
proof -
  obtain packet where parsed: "decode_wire_packet bytes = Some packet"
    and checked: "response_fixed_validate (response_client_max_nesting current) (packet_core expected) (packet::wire_packet) = Inr result"
    by (rule response_fixed_admission_keeps_the_actual_client_boundary_and_parsed_value[OF admitted]) blast
  obtain call_id kind number position where result: "result = (call_id,kind,number,position)"
    by (cases result rule: prod_cases4) auto
  have actual_checked: "response_fixed_validate (Suc fuel) (packet_core expected) packet = Inr (call_id,kind,number,position)"
    using checked depth result by simp
  have correlated: "code_correlate_reference_response (packet_core expected) packet = Some result"
    unfolding result
    by (rule response_general_nonordinary_validation_consumes_hol_correlation[OF formed selected actual_checked])
  show ?thesis by (simp add: parsed correlated)
qed

text \<open>
  Legal and Spend are selected by the real source decoder, not by a supplied
  outer header. Every call/native id, original bytes, result words, kind and
  optional position are those observed in the fixed parser and validator.
  These originals are not Debit, so the existing HOL position relation adds
  no equation between their actual commit and an input cut. This theorem
  consumes result data without certifying its StoredCall/product provenance.
\<close>

end
