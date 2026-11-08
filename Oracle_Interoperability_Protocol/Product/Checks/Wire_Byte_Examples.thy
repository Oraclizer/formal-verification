theory Wire_Byte_Examples
  imports "../Wire_Admission"
begin

definition wire_case_body :: wire_body where
  "wire_case_body = \<lparr>wire_opcode = 1, wire_words = [1,0,1,17], wire_blobs = [], wire_deadline = Deadline_Absent\<rparr>"

definition wire_case_core :: wire_core where
  "wire_case_core = \<lparr>wire_version = 6, wire_purpose = 1, wire_deployment = 7, wire_source_domain = 0,
    wire_target_domain = 2, wire_principal = 7, wire_key_number = 9, wire_authority_epoch = 9,
    wire_sent_seconds = 100, wire_ttl_seconds = 5, wire_uuid = [0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15],
    wire_message_family = Wire_Query, wire_primary_code = 1, wire_secondary_code = Some 77,
    wire_signature_scheme = 1, wire_operation_body = wire_case_body,
    wire_atomicity = 3, wire_priority = 3, wire_route_scope = 1\<rparr>"

definition wire_case_exact_core_bytes :: wire_bytes where
  "wire_case_exact_core_bytes = [8,6,16,1,25,7,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,41,2,0,0,0,0,0,0,0,49,7,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,4,104,1,112,77,120,1,154,1,38,8,1,17,1,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0]"

definition wire_case_packet :: wire_packet where
  "wire_case_packet = \<lparr>packet_core = wire_case_core, packet_signature = replicate 64 0\<rparr>"

definition wire_case_profile :: negotiated_wire_profile where
  "wire_case_profile = \<lparr>negotiated_version = 6, negotiated_families = {Wire_Query},
    negotiated_atomicities = {3}, negotiated_schemes = {1}\<rparr>"

definition wire_case_boundary :: "nat \<Rightarrow> wire_boundary" where
  "wire_case_boundary now = \<lparr>boundary_profile = wire_case_profile, boundary_deployment = 7, boundary_source = 0,
    boundary_target = 2, boundary_principal = 7, boundary_key = 9, boundary_epoch = 9, boundary_route_scope = 1,
    boundary_now = now, boundary_asset_ttl_floor = 2, boundary_future_skew = 5, boundary_max_frame = 1024,
    boundary_version_floor = 5, boundary_critical_allowed = False, boundary_threshold_supported = False\<rparr>"

lemma concrete_protobuf_query_has_the_exact_canonical_core:
  "encode_wire_core wire_case_core = wire_case_exact_core_bytes"
  by (simp add: wire_case_exact_core_bytes_def wire_case_core_def wire_case_body_def encode_wire_core_def
      encode_wire_body_def core_fields_def body_fields_def secondary_field_def put_proto_fields_def
      make_proto_tag_def put_wire_varint.simps small_number_eight_octets)

lemma concrete_protobuf_query_has_the_exact_signing_preimage:
  "envelope_signing_bytes wire_case_core = [79,73,80,0,69,78,86,69,76,79,80,69,0,0,0,0,159,8,6,16,1,25,7,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,41,2,0,0,0,0,0,0,0,49,7,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,4,104,1,112,77,120,1,154,1,38,8,1,17,1,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0]"
  by (simp add: envelope_signing_bytes_def concrete_protobuf_query_has_the_exact_canonical_core
      wire_case_exact_core_bytes_def small_number_four_octets Let_def)

lemma wire_case_body_is_wellformed: "wire_body_wellformed wire_case_body"
  by (simp add: wire_body_wellformed_def wire_case_body_def body_fields_def)

lemma wire_case_core_is_wellformed: "wire_core_wellformed wire_case_core"
proof -
  have body_bytes: "wire_octets (encode_wire_body wire_case_body)"
    unfolding encode_wire_body_def
    by (rule encoded_wire_fields_are_octets) (use wire_case_body_is_wellformed in \<open>simp add: wire_body_wellformed_def\<close>)
  show ?thesis using wire_case_body_is_wellformed body_bytes
    by (simp add: wire_core_wellformed_def wire_case_core_def core_fields_def wire_case_body_def
        secondary_field_def wire_octets_def)
qed

lemma wire_case_packet_is_wellformed: "wire_packet_wellformed wire_case_packet"
proof -
  have below: "length (encode_wire_core wire_case_core) < 256^4"
    by (simp add: concrete_protobuf_query_has_the_exact_canonical_core wire_case_exact_core_bytes_def)
  have scheme: "wire_signature_scheme wire_case_core = 1" by (simp add: wire_case_core_def)
  show ?thesis using wire_case_core_is_wellformed below scheme
    by (simp add: wire_packet_wellformed_def wire_case_packet_def wire_octets_def)
qed

lemma wire_case_packet_parses: "decode_wire_packet (encode_wire_packet wire_case_packet) = Some wire_case_packet"
  by (rule the_exact_wire_message_decodes_from_its_canonical_bytes[OF wire_case_packet_is_wellformed])

lemma wire_case_frame_fits:
  "length (encode_wire_packet wire_case_packet) \<le> boundary_max_frame (wire_case_boundary now)"
  by (simp add: encode_wire_packet_def packet_fields_def put_proto_fields_def wire_case_packet_def
      concrete_protobuf_query_has_the_exact_canonical_core wire_case_exact_core_bytes_def make_proto_tag_def
      wire_case_boundary_def put_wire_varint.simps)

lemma canonical_query_is_eligible_at_its_exact_expiry:
  "wire_gate (\<lambda>_ _ _. True) (\<lambda>_. True) (\<lambda>_ _. True)
    (wire_case_boundary 105) (encode_wire_packet wire_case_packet) = Gate_Admitted wire_case_packet"
  using wire_case_frame_fits[of 105] wire_case_packet_parses
  by (simp add: wire_gate_def wire_case_boundary_def wire_case_profile_def wire_case_packet_def
      wire_case_core_def wire_expiry_def effective_wire_ttl_def current_wire_scope_def Let_def)

lemma canonical_query_expired_one_second_later:
  "wire_gate (\<lambda>_ _ _. True) (\<lambda>_. True) (\<lambda>_ _. True)
    (wire_case_boundary 106) (encode_wire_packet wire_case_packet) = Gate_Refused Wire_TTL_Expired"
  using wire_case_frame_fits[of 106] wire_case_packet_parses
  by (simp add: wire_gate_def wire_case_boundary_def wire_case_profile_def wire_case_packet_def
      wire_case_core_def wire_expiry_def effective_wire_ttl_def current_wire_scope_def Let_def)

lemma overlong_protobuf_tag_is_not_a_canonical_alias:
  "read_canonical_proto_fields [136,0,6] = None"
  by (simp add: read_canonical_proto_fields_def take_proto_field_def put_proto_fields_def make_proto_tag_def
      put_wire_varint.simps Let_def)

definition wire_case_offer where
  "wire_case_offer sender receiver versions = \<lparr>offer_deployment = 7, offer_sender = sender,
    offer_receiver = receiver, offer_challenge = 41, offer_expires = 200,
    offered_versions = versions, offered_families = {Wire_Query}, offered_atomicities = {3}, offered_schemes = {1}\<rparr>"

lemma an_authenticated_legacy_only_peer_negotiates_an_explicit_compatibility_profile:
  "authenticated_wire_negotiation (\<lambda>_. True) (\<lambda>_ _ _. True) 7 0 2 41 5 100
    (wire_case_offer 0 2 {5,6}) (wire_case_offer 2 0 {5}) =
    Some (wire_case_profile\<lparr>negotiated_version := 5\<rparr>)"
  by (simp add: authenticated_wire_negotiation_def selected_wire_version_def wire_case_offer_def
      wire_case_profile_def Let_def)

lemma the_same_authenticated_offer_negotiates_current_when_both_support_it:
  "authenticated_wire_negotiation (\<lambda>_. True) (\<lambda>_ _ _. True) 7 0 2 41 5 100
    (wire_case_offer 0 2 {5,6}) (wire_case_offer 2 0 {5,6}) = Some wire_case_profile"
  by (simp add: authenticated_wire_negotiation_def selected_wire_version_def wire_case_offer_def
      wire_case_profile_def Let_def)

lemma two_competing_body_members_are_rejected:
  "parse_core_body_tail 4 [Proto_Varint 15 1, Proto_Bytes 19 body, Proto_Bytes 20 other,
    Proto_Varint 23 3, Proto_Varint 24 3, Proto_Fixed64 25 1] = None"
  by (simp add: parse_core_body_tail_def Let_def)

lemma a_forged_first_arrival_cannot_reserve_the_real_uuid:
  "receive_canonical_wire (\<lambda>_ _ _. False) (\<lambda>_. True) (\<lambda>_ _. True)
    (wire_case_boundary 105) (encode_wire_packet wire_case_packet) cache =
    (cache, Wire_Rejected Invalid_Wire_Signature)"
  using wire_case_frame_fits[of 105] wire_case_packet_parses
  by (simp add: receive_canonical_wire_def wire_gate_def wire_case_boundary_def wire_case_profile_def
      wire_case_packet_def wire_case_core_def wire_expiry_def effective_wire_ttl_def current_wire_scope_def Let_def)

lemma a_valid_arrival_follows_a_bad_signature_without_a_poisoned_uuid:
  "let bad = receive_canonical_wire (\<lambda>_ _ _. False) (\<lambda>_. True) (\<lambda>_ _. True)
         (wire_case_boundary 105) (encode_wire_packet wire_case_packet) (\<lambda>_. None);
       good = receive_canonical_wire (\<lambda>_ _ _. True) (\<lambda>_. True) (\<lambda>_ _. True)
         (wire_case_boundary 105) (encode_wire_packet wire_case_packet) (fst bad)
   in snd good = Wire_First wire_case_packet"
proof -
  have bad: "fst (receive_canonical_wire (\<lambda>_ _ _. False) (\<lambda>_. True) (\<lambda>_ _. True)
    (wire_case_boundary 105) (encode_wire_packet wire_case_packet) (\<lambda>_. None)) = (\<lambda>_. None)"
    by (simp only: a_forged_first_arrival_cannot_reserve_the_real_uuid fst_conv)
  show ?thesis unfolding Let_def bad
    by (simp add: receive_canonical_wire_def canonical_query_is_eligible_at_its_exact_expiry Let_def)
qed

end
