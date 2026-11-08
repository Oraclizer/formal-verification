theory Wire_Code_Response_Assembly
  imports Wire_Code_Response_Size "OIP_Reference_Profile.Reference_Response_Correlation"
begin

definition code_response_outer :: "wire_core \<Rightarrow> nat \<Rightarrow> wire_core" where
  "code_response_outer outer atomicity = code_response_core outer atomicity [] []"

definition code_known_source_response_packet ::
  "wire_core \<Rightarrow> nat \<Rightarrow> client_call_id \<Rightarrow> reference_response_kind \<Rightarrow> nat \<Rightarrow>
    nat option \<Rightarrow> wire_core \<Rightarrow> wire_bytes \<Rightarrow> wire_packet option" where
  "code_known_source_response_packet outer atomicity call_id kind number position original signature =
    map_option (\<lambda>words.
      \<lparr>packet_core = code_response_core outer atomicity words (encode_wire_core original),
       packet_signature = signature\<rparr>) (code_response_words call_id kind number position)"

lemma the_source_response_core_has_exactly_the_existing_typed_response_body:
  assumes words: "code_response_words call_id kind number position = Some actual_words"
  shows "code_response_core outer atomicity actual_words (encode_wire_core original) =
    (code_response_outer outer atomicity)\<lparr>wire_message_family := Wire_Ack,
      wire_operation_body := reference_response_body call_id kind number position original\<rparr>"
proof -
  have sequence: "actual_words = wire_words (reference_response_body call_id kind number position original)"
    by (rule source_response_words_have_the_existing_model_word_sequence(1)[OF words])
  show ?thesis
    by (simp add: code_response_core_def code_response_outer_def reference_response_body_def sequence)
qed

theorem a_checked_source_response_packet_is_the_actual_guarded_reference_encoding:
  assumes packet: "code_known_source_response_packet outer atomicity call_id kind number position original signature = Some response"
    and header: "reference_response_header_matches (code_response_outer outer atomicity) original call_id"
    and commit: "reference_response_position_matches original kind position"
    and compatible: "reference_response_compatible (wire_message_family original)
      (wire_opcode (wire_operation_body original)) kind number (position \<noteq> None)"
    and wellformed: "wire_packet_wellformed response"
  shows "encode_guarded_reference_response (code_response_outer outer atomicity) original
      call_id kind number position signature = Some (encode_wire_packet response)"
proof -
  obtain actual_words where words: "code_response_words call_id kind number position = Some actual_words"
    and response: "response = \<lparr>packet_core = code_response_core outer atomicity actual_words (encode_wire_core original),
      packet_signature = signature\<rparr>"
    using packet by (auto simp: code_known_source_response_packet_def)
  have core: "code_response_core outer atomicity actual_words (encode_wire_core original) =
    (code_response_outer outer atomicity)\<lparr>wire_message_family := Wire_Ack,
      wire_operation_body := reference_response_body call_id kind number position original\<rparr>"
    by (rule the_source_response_core_has_exactly_the_existing_typed_response_body[OF words])
  show ?thesis using header commit compatible wellformed
    by (simp add: encode_guarded_reference_response_def encode_reference_response_def Let_def response core)
qed

theorem the_checked_source_response_decodes_and_correlates_to_the_exact_original:
  assumes packet: "code_known_source_response_packet outer atomicity call_id kind number position original signature = Some response"
    and header: "reference_response_header_matches (code_response_outer outer atomicity) original call_id"
    and commit: "reference_response_position_matches original kind position"
    and compatible: "reference_response_compatible (wire_message_family original)
      (wire_opcode (wire_operation_body original)) kind number (position \<noteq> None)"
    and wellformed: "wire_packet_wellformed response"
  shows "map_option (correlate_reference_response original) (decode_wire_packet (encode_wire_packet response)) =
      Some (Some (call_id,kind,number,position))"
proof -
  have encoded: "encode_guarded_reference_response (code_response_outer outer atomicity) original
      call_id kind number position signature = Some (encode_wire_packet response)"
    by (rule a_checked_source_response_packet_is_the_actual_guarded_reference_encoding[OF packet header commit compatible wellformed])
  show ?thesis by (rule a_guarded_native_response_decodes_and_correlates_to_its_exact_result[OF encoded])
qed

lemma a_checked_source_response_has_the_exact_source_packet_bytes:
  assumes packet: "code_known_source_response_packet outer atomicity call_id kind number position original signature = Some response"
  shows "code_packet_bytes response = encode_wire_packet response"
  by (rule the_source_packet_field_sequence_is_the_exact_model_sequence)

text \<open>
  response_words and response_core are source value projections; signature
  bytes are supplied by the named signer boundary. Header, commit and known
  compatibility are separate visible premises. The full source validator
  and result conversion must establish these premises before this bridge is
  used as an encode_response claim. The SHA256 binding/UUID derivation,
  signer authorization/error order and post-sign admission are outstanding
  source-path obligations, not hidden in the signature parameter.
\<close>

end
