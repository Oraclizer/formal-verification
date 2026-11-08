theory Reference_Outbound_Comparison
  imports Reference_Outbound_Data "OIP_Reference_Profile.Reference_Response_Codes"
begin

abbreviation native_outbound_packet where
  "native_outbound_packet \<equiv>
    \<lparr>packet_core = native_outbound_outer, packet_signature = native_outbound_signature\<rparr>"

lemma outbound_small_varint: "number < 128 \<Longrightarrow> put_wire_varint number = [number]"
  by (subst put_wire_varint.simps) simp

lemma outbound_large_varints:
  "put_wire_varint 162 = [162,1]"
  "put_wire_varint 184 = [184,1]"
  "put_wire_varint 192 = [192,1]"
  "put_wire_varint 201 = [201,1]"
  "put_wire_varint 356 = [228,2]"
  "put_wire_varint 415 = [159,3]"
  "put_wire_varint 535 = [151,4]"
  by (subst put_wire_varint.simps; simp add: outbound_small_varint)+

lemmas outbound_field_encoding = put_proto_fields_def make_proto_tag_def
  small_number_eight_octets outbound_small_varint outbound_large_varints

lemma outbound_known_lengths:
  "length actual_debit_core_bytes = 356"
  "length native_outbound_body_bytes = 415"
  "length native_outbound_core_bytes = 535"
  "length native_outbound_signature = 64"
  by (simp_all add: actual_debit_core_bytes_def native_outbound_body_bytes_def
      native_outbound_core_bytes_def native_outbound_signature_def)

lemma observed_body_bytes:
  "encode_wire_body (wire_operation_body native_outbound_outer) = native_outbound_body_bytes"
proof -
  have "encode_wire_body (wire_operation_body native_outbound_outer) =
      [8,2,17,7,0,0,0,0,0,0,0,17,33,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,
       17,12,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,26,228,2] @
      actual_debit_core_bytes"
    by (simp add: native_outbound_outer_def reference_response_body_def encode_wire_body_def
      body_fields_def outbound_field_encoding debit_fixture_core_encoding outbound_known_lengths)
  then show ?thesis by (simp add: actual_debit_core_bytes_def native_outbound_body_bytes_def)
qed

lemma observed_core_bytes:
  "encode_wire_core native_outbound_outer = native_outbound_core_bytes"
proof -
  have body: "encode_wire_body (reference_response_body (7,33) Recorded_Result 12 (Some 2) debit_fixture_core) =
      native_outbound_body_bytes"
    using observed_body_bytes by (simp add: native_outbound_outer_def)
  have "encode_wire_core native_outbound_outer =
      [8,6,16,1,25,7,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,41,0,0,0,0,0,0,0,0,
       49,42,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,
       73,105,0,0,0,0,0,0,0,81,20,0,0,0,0,0,0,0,90,16,212,1,2,3,4,5,64,7,128,
       9,10,11,12,13,14,15,96,5,104,1,120,1,162,1,159,3] @ native_outbound_body_bytes @
      [184,1,1,192,1,3,201,1,1,0,0,0,0,0,0,0]"
    by (simp add: native_outbound_outer_def encode_wire_core_def core_fields_def secondary_field_def
      body outbound_field_encoding outbound_known_lengths)
  then show ?thesis by (simp add: native_outbound_body_bytes_def native_outbound_core_bytes_def)
qed

lemma the_observed_reference_response_is_its_exact_model_encoding:
  "encode_reference_response native_outbound_outer debit_fixture_core (7,33) Recorded_Result 12
      (Some 2) native_outbound_signature = Some native_outbound_bytes"
proof -
  obtain native where decoded: "decode_native_call_prefix debit_fixture_core = Some native"
    and native_call: "native_id native = (7,33)"
    and native_cut: "native_cut native = \<lparr>cut_authority_epoch = 9, cut_revision = 2\<rparr>"
    by (rule debit_fixture_operands)
  have header: "reference_response_header_matches native_outbound_outer debit_fixture_core (7,33)"
    using decoded native_call
    by (simp add: reference_response_header_matches_def native_outbound_outer_def debit_fixture_core_def)
  have position: "reference_response_position_matches debit_fixture_core Recorded_Result (Some 2)"
    using decoded native_cut by (simp add: reference_response_position_matches_def)
  have body: "wire_body_wellformed (wire_operation_body native_outbound_outer)"
    by (simp add: native_outbound_outer_def reference_response_body_def body_fields_def
        wire_body_wellformed_def debit_fixture_core_encoding actual_debit_core_bytes_def wire_octets_def)
  have octets: "wire_octets (encode_wire_body (wire_operation_body native_outbound_outer))"
    unfolding encode_wire_body_def
    by (rule encoded_wire_fields_are_octets) (use body in \<open>simp add: wire_body_wellformed_def\<close>)
  have fields: "\<forall>field \<in> set (core_fields native_outbound_outer). wellformed_proto_field field"
    using octets by (simp add: native_outbound_outer_def core_fields_def secondary_field_def wire_octets_def)
  have core: "wire_core_wellformed native_outbound_outer"
    using body fields by (simp add: wire_core_wellformed_def native_outbound_outer_def reference_response_body_def)
  have length: "length (encode_wire_core native_outbound_outer) < 256^4"
    by (simp add: observed_core_bytes outbound_known_lengths)
  have scheme: "wire_signature_scheme native_outbound_outer = 1"
    by (simp add: native_outbound_outer_def)
  have valid: "wire_packet_wellformed native_outbound_packet"
    using core length scheme
    by (simp add: wire_packet_wellformed_def native_outbound_signature_def wire_octets_def)
  have packet: "encode_wire_packet native_outbound_packet =
      [10,151,4] @ native_outbound_core_bytes @ [18,64] @ native_outbound_signature"
    by (simp add: encode_wire_packet_def packet_fields_def outbound_field_encoding observed_core_bytes
      outbound_known_lengths)
  have exact: "encode_wire_packet native_outbound_packet = native_outbound_bytes"
    using packet by (simp add: native_outbound_core_bytes_def native_outbound_signature_def native_outbound_bytes_def)
  have unchanged: "native_outbound_outer\<lparr>wire_message_family := Wire_Ack,
      wire_operation_body := reference_response_body (7,33) Recorded_Result 12 (Some 2) debit_fixture_core\<rparr> =
      native_outbound_outer"
    by (simp add: native_outbound_outer_def)
  show ?thesis using header position valid exact unchanged
    by (simp add: encode_reference_response_def Let_def)
qed

lemma the_observed_reference_response_is_the_exact_guarded_model_encoding:
  "encode_guarded_reference_response native_outbound_outer debit_fixture_core (7,33) Recorded_Result 12
      (Some 2) native_outbound_signature = Some native_outbound_bytes"
proof -
  have family: "wire_message_family debit_fixture_core = Wire_State_Sync"
    and opcode: "wire_opcode (wire_operation_body debit_fixture_core) = 1"
    by (simp_all add: debit_fixture_core_def debit_fixture_body_def)
  show ?thesis using reference_debit_accepts_its_committed_result_and_original_rejection(1)
    the_observed_reference_response_is_its_exact_model_encoding
    by (simp add: encode_guarded_reference_response_def family opcode)
qed

lemma a_different_wellformed_original_core_has_different_response_binding_bytes:
  fixes expected other :: wire_core
  assumes first: "wire_core_wellformed expected"
    and second: "wire_core_wellformed other"
    and differs: "expected \<noteq> other"
  shows "wire_blobs (reference_response_body call_id kind code position expected) \<noteq>
      wire_blobs (reference_response_body call_id kind code position other)"
proof
  assume equal: "wire_blobs (reference_response_body call_id kind code position expected) =
      wire_blobs (reference_response_body call_id kind code position other)"
  then have bytes: "encode_wire_core expected = encode_wire_core other"
    by (simp add: reference_response_body_def)
  have "decode_wire_core (encode_wire_core expected) = decode_wire_core (encode_wire_core other)"
    by (rule arg_cong[OF bytes])
  moreover have "decode_wire_core (encode_wire_core expected) = Some expected"
    using first by (simp add: wellformed_canonical_core_has_a_two_way_encoding)
  moreover have "decode_wire_core (encode_wire_core other) = Some other"
    using second by (simp add: wellformed_canonical_core_has_a_two_way_encoding)
  ultimately show False using differs by simp
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_observed_reference_response_is_its_exact_model_encoding
      the_observed_reference_response_is_the_exact_guarded_model_encoding
      a_different_wellformed_original_core_has_different_response_binding_bytes})
  then () else error "Unexpected oracle in exact outbound comparison"
\<close>

end
