theory Reference_Response_Correlation
  imports Reference_Response_Codes
begin

definition response_kind_at :: "nat \<Rightarrow> reference_response_kind option" where
  "response_kind_at number =
    (if number = 1 then Some Recorded_Result else if number = 2 then Some Delivery_Refusal
     else if number = 3 then Some Validation_Refusal else None)"

lemma response_kind_roundtrip [simp]:
  "response_kind_at (reference_response_kind_number kind) = Some kind"
  by (cases kind) (simp_all add: response_kind_at_def)

definition response_result_words where
  "response_result_words words =
    (case words of [namespace, sequence, kind, code, present] \<Rightarrow>
       if present = 0 then map_option (\<lambda>tag. ((namespace, sequence), tag, code, None)) (response_kind_at kind) else None
     | [namespace, sequence, kind, code, present, revision] \<Rightarrow>
       if present = 1 then map_option (\<lambda>tag. ((namespace, sequence), tag, code, Some revision)) (response_kind_at kind) else None
     | _ \<Rightarrow> None)"

definition correlate_reference_response where
  "correlate_reference_response original packet =
    (let core = packet_core packet; body = wire_operation_body core in
     case response_result_words (wire_words body) of None \<Rightarrow> None
       | Some (call_id, kind, code, position) \<Rightarrow>
         if wire_message_family core = Wire_Ack \<and> body = reference_response_body call_id kind code position original \<and>
            reference_response_header_matches core original call_id \<and>
            reference_response_position_matches original kind position \<and>
            reference_response_compatible (wire_message_family original) (wire_opcode (wire_operation_body original))
              kind code (position \<noteq> None)
         then Some (call_id, kind, code, position) else None)"

lemma the_reference_response_words_recover_the_typed_result:
  "response_result_words (wire_words (reference_response_body call_id kind code position original)) =
      Some (call_id, kind, code, position)"
  by (cases call_id; cases position) (simp_all add: response_result_words_def reference_response_body_def)

theorem a_guarded_native_response_decodes_and_correlates_to_its_exact_result:
  assumes encoded: "encode_guarded_reference_response outer original call_id kind code position signature = Some bytes"
  shows "map_option (correlate_reference_response original) (decode_wire_packet bytes) =
      Some (Some (call_id, kind, code, position))"
proof -
  let ?body = "reference_response_body call_id kind code position original"
  let ?core = "outer\<lparr>wire_message_family := Wire_Ack, wire_operation_body := ?body\<rparr>"
  let ?packet = "\<lparr>packet_core = ?core, packet_signature = signature\<rparr>"
  have compatible: "reference_response_compatible (wire_message_family original) (wire_opcode (wire_operation_body original))
      kind code (position \<noteq> None)"
    and header: "reference_response_header_matches outer original call_id"
    and position: "reference_response_position_matches original kind position"
    and valid: "wire_packet_wellformed ?packet" and exact: "encode_wire_packet ?packet = bytes"
    using encoded by (auto simp: encode_guarded_reference_response_def encode_reference_response_def Let_def split: if_splits)
  have parsed: "decode_wire_packet bytes = Some ?packet"
    unfolding exact[symmetric]
    by (rule the_exact_wire_message_decodes_from_its_canonical_bytes[OF valid])
  have updated_header: "reference_response_header_matches ?core original call_id"
    using header by (simp add: reference_response_header_matches_def)
  have matches: "correlate_reference_response original ?packet = Some (call_id, kind, code, position)"
    using updated_header position compatible
    by (simp add: correlate_reference_response_def Let_def the_reference_response_words_recover_the_typed_result)
  show ?thesis by (simp add: parsed matches)
qed

lemma a_different_embedded_original_cannot_be_correlated:
  assumes "wire_blobs (wire_operation_body (packet_core packet)) \<noteq> [encode_wire_core original]"
  shows "correlate_reference_response original packet = None"
  using assms by (auto simp: correlate_reference_response_def reference_response_body_def Let_def
    split: option.splits prod.splits if_splits)

lemma the_canonical_uuid_input_distinguishes_different_negotiated_atomicities:
  fixes first second :: wire_core
  assumes wellformed: "wire_core_wellformed (first\<lparr>wire_uuid := placeholder\<rparr>)"
    "wire_core_wellformed (second\<lparr>wire_uuid := placeholder\<rparr>)"
    and atomicity: "wire_atomicity first \<noteq> wire_atomicity second"
  shows "encode_wire_core (first\<lparr>wire_uuid := placeholder\<rparr>) \<noteq>
    encode_wire_core (second\<lparr>wire_uuid := placeholder\<rparr>)"
proof
  let ?first = "first\<lparr>wire_uuid := placeholder\<rparr>"
  let ?second = "second\<lparr>wire_uuid := placeholder\<rparr>"
  assume equal: "encode_wire_core ?first = encode_wire_core ?second"
  have "decode_wire_core (encode_wire_core ?first) = decode_wire_core (encode_wire_core ?second)"
    by (rule arg_cong[OF equal])
  then have "?first = ?second"
    by (simp add: wellformed_canonical_core_has_a_two_way_encoding[OF wellformed(1)]
      wellformed_canonical_core_has_a_two_way_encoding[OF wellformed(2)])
  then have "wire_atomicity ?first = wire_atomicity ?second" by (rule arg_cong)
  then show False using atomicity by simp
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms a_guarded_native_response_decodes_and_correlates_to_its_exact_result
      a_different_embedded_original_cannot_be_correlated
      the_canonical_uuid_input_distinguishes_different_negotiated_atomicities})
  then () else error "Unexpected oracle in reference response correlation"
\<close>

end
