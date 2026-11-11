theory Boundary_G0_Canary
  imports "OIP_Transport_Boundary_Typed.Boundary_Typed_G0"
begin

text \<open>
  The original raw Packet and original decoded-packet definition are retained.
  Concrete encoding plus the existing canonical round-trip theorem replaces
  repeated simplifier execution of the entire raw-byte parser.  No generated
  evaluator oracle is introduced.  Pinned raw model/Rust/Go runs remain
  separate implementation evidence with the unchanged 46 input rows.
\<close>

definition boundary_g0_packet_bytes :: wire_bytes where
  "boundary_g0_packet_bytes = [10,228,2,8,6,16,1,25,7,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,41,0,0,0,0,0,0,0,0,49,7,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,1,104,1,112,77,120,1,130,1,234,1,8,1,17,33,0,0,0,0,0,0,0,17,33,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,26,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0,18,64,254,173,113,58,226,33,234,102,211,135,76,109,223,32,108,55,115,188,185,242,176,65,203,155,229,203,241,209,9,107,152,67,245,31,44,234,145,226,75,23,25,39,212,101,95,47,224,183,204,210,182,144,148,244,15,145,184,20,20,45,66,157,98,6]"

definition boundary_g0_packet :: wire_packet where
  "boundary_g0_packet = the (decode_wire_packet boundary_g0_packet_bytes)"

definition boundary_g0_exact_core_bytes :: wire_bytes where
  "boundary_g0_exact_core_bytes = [8,6,16,1,25,7,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,41,0,0,0,0,0,0,0,0,49,7,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,1,104,1,112,77,120,1,130,1,234,1,8,1,17,33,0,0,0,0,0,0,0,17,33,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,26,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0]"

lemma boundary_g0_typed_core_has_exact_source_encoding:
  "encode_wire_core boundary_g0_typed_core = boundary_g0_exact_core_bytes"
  by (simp add: boundary_g0_exact_core_bytes_def boundary_g0_typed_core_def
    boundary_g0_typed_body_def encode_wire_core_def encode_wire_body_def
    core_fields_def body_fields_def secondary_field_def put_proto_fields_def
    make_proto_tag_def put_wire_varint.simps small_number_eight_octets)

lemma boundary_g0_typed_body_is_wellformed:
  "wire_body_wellformed boundary_g0_typed_body"
  by (simp add: wire_body_wellformed_def boundary_g0_typed_body_def body_fields_def wire_octets_def)

lemma boundary_g0_typed_core_is_wellformed:
  "wire_core_wellformed boundary_g0_typed_core"
proof -
  have body_bytes: "wire_octets (encode_wire_body boundary_g0_typed_body)"
    unfolding encode_wire_body_def
    by (rule encoded_wire_fields_are_octets)
      (use boundary_g0_typed_body_is_wellformed in \<open>simp add: wire_body_wellformed_def\<close>)
  show ?thesis using boundary_g0_typed_body_is_wellformed body_bytes
    by (simp add: wire_core_wellformed_def boundary_g0_typed_core_def
      core_fields_def boundary_g0_typed_body_def secondary_field_def wire_octets_def)
qed

lemma boundary_g0_typed_packet_is_wellformed:
  "wire_packet_wellformed boundary_g0_typed_packet"
proof -
  have below: "length (encode_wire_core boundary_g0_typed_core) < 256^4"
    by (simp add: boundary_g0_typed_core_has_exact_source_encoding boundary_g0_exact_core_bytes_def)
  have scheme: "wire_signature_scheme boundary_g0_typed_core = 1"
    by (simp add: boundary_g0_typed_core_def)
  show ?thesis using boundary_g0_typed_core_is_wellformed below scheme
    by (simp add: wire_packet_wellformed_def boundary_g0_typed_packet_def wire_octets_def)
qed

lemma boundary_g0_typed_packet_has_exact_source_encoding:
  "encode_wire_packet boundary_g0_typed_packet = boundary_g0_packet_bytes"
  by (simp add: encode_wire_packet_def packet_fields_def put_proto_fields_def
    boundary_g0_typed_packet_def boundary_g0_typed_core_has_exact_source_encoding
    boundary_g0_exact_core_bytes_def boundary_g0_packet_bytes_def
    make_proto_tag_def put_wire_varint.simps)

lemma boundary_g0_source_bytes_decode_to_the_typed_packet:
  "decode_wire_packet boundary_g0_packet_bytes = Some boundary_g0_typed_packet"
  using the_exact_wire_message_decodes_from_its_canonical_bytes[OF boundary_g0_typed_packet_is_wellformed]
    boundary_g0_typed_packet_has_exact_source_encoding by simp

lemma boundary_g0_packet_is_the_typed_source_packet:
  "boundary_g0_packet = boundary_g0_typed_packet"
  by (simp add: boundary_g0_packet_def boundary_g0_source_bytes_decode_to_the_typed_packet)

lemma the_same_signed_source_bytes_have_a_typed_packet:
  "decode_wire_packet boundary_g0_packet_bytes = Some boundary_g0_packet"
  using boundary_g0_source_bytes_decode_to_the_typed_packet
    boundary_g0_packet_is_the_typed_source_packet by simp

lemma the_source_packet_has_the_arithmetic_carriers:
  "wire_sent_seconds (packet_core boundary_g0_packet) = 100"
  "wire_ttl_seconds (packet_core boundary_g0_packet) = 5"
  using typed_source_packet_has_the_arithmetic_carriers
  by (simp_all only: boundary_g0_packet_is_the_typed_source_packet)

lemma source_positive_and_overflow_branches_are_reached:
  "code_admit_packet (\<lambda>_ _ _. True) boundary_g0_packet
      (boundary_g0_authority 105 0 0) = None"
  "code_admit_packet (\<lambda>_ _ _. True) boundary_g0_packet
      (boundary_g0_authority 0 (2^64 - 1) 100) = Some Wire_TTL_Invalid"
  "code_admit_packet (\<lambda>_ _ _. True) boundary_g0_packet
      (boundary_g0_authority 105 0 (2^64 - 1)) = Some Wire_TTL_Invalid"
  using typed_source_positive_and_overflow_branches_are_reached
  by (simp_all only: boundary_g0_packet_is_the_typed_source_packet)

lemma removing_either_overflow_guard_reaches_the_success_tail:
  "boundary_g0_mutated_ttl_tail False True (packet_core boundary_g0_packet)
      (boundary_g0_authority 0 (2^64 - 1) 100) = None"
  "boundary_g0_mutated_ttl_tail True False (packet_core boundary_g0_packet)
      (boundary_g0_authority 105 0 (2^64 - 1)) = None"
  using typed_removing_either_overflow_guard_reaches_the_success_tail
  by (simp_all only: boundary_g0_packet_is_the_typed_source_packet)

lemma the_unchanged_operand_and_binding_continuation_really_accepts:
  "code_transport_after_operands code_transport_operand_verdict boundary_g0_packet 4 None =
      (Code_Transport_First, Some (encode_wire_core (packet_core boundary_g0_packet)))"
  apply (simp only: boundary_g0_packet_is_the_typed_source_packet)
  by code_simp

lemma the_old_clock_skew_vector_masks_removal_of_the_latest_guard:
  "boundary_g0_mutated_ttl_tail True False (packet_core boundary_g0_packet)
      (boundary_g0_authority (2^64 - 1) 0 1) = Some Wire_TTL_Invalid"
  using typed_old_clock_skew_vector_masks_removal_of_the_latest_guard
  by (simp only: boundary_g0_packet_is_the_typed_source_packet)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      boundary_g0_typed_core_has_exact_source_encoding
      boundary_g0_typed_body_is_wellformed
      boundary_g0_typed_core_is_wellformed
      boundary_g0_typed_packet_is_wellformed
      boundary_g0_typed_packet_has_exact_source_encoding
      boundary_g0_source_bytes_decode_to_the_typed_packet
      boundary_g0_packet_is_the_typed_source_packet
      the_same_signed_source_bytes_have_a_typed_packet
      the_source_packet_has_the_arithmetic_carriers
      source_positive_and_overflow_branches_are_reached
      keeping_both_go_guards_reuses_the_generic_tail
      removing_either_overflow_guard_reaches_the_success_tail
      the_unchanged_operand_and_binding_continuation_really_accepts
      the_old_clock_skew_vector_masks_removal_of_the_latest_guard})
  then () else error "Unexpected oracle in exact-byte boundary G-0"
\<close>

end
