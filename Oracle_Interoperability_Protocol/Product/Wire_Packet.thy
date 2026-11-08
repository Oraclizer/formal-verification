theory Wire_Packet
  imports Wire_Core
begin

lemma concatenated_octets_are_checked_componentwise [simp]:
  "wire_octets (a @ b) = (wire_octets a \<and> wire_octets b)"
  by (auto simp: wire_octets_def)

lemma encoded_wire_fields_are_octets:
  assumes "\<forall>field \<in> set items. wellformed_proto_field field"
  shows "wire_octets (put_proto_fields items)"
proof -
  have each: "wellformed_proto_field field \<Longrightarrow> wire_octets (put_proto_field field)" for field
    by (cases field) (simp_all add: shortest_varint_is_an_octet_word)
  show ?thesis using assms each
    by (induction items) (auto simp: put_proto_fields_def wire_octets_def)
qed

record wire_packet =
  packet_core :: wire_core
  packet_signature :: wire_bytes

definition packet_fields where
  "packet_fields packet =
    [Proto_Bytes 1 (encode_wire_core (packet_core packet)), Proto_Bytes 2 (packet_signature packet)]"

definition wire_packet_wellformed where
  "wire_packet_wellformed packet \<longleftrightarrow>
    wire_core_wellformed (packet_core packet) \<and> wire_octets (packet_signature packet) \<and>
    length (encode_wire_core (packet_core packet)) < 256^4 \<and>
    (if wire_signature_scheme (packet_core packet) = 1 then length (packet_signature packet) = 64
     else packet_signature packet \<noteq> [])"

definition encode_wire_packet where
  "encode_wire_packet packet = put_proto_fields (packet_fields packet)"

definition decode_wire_packet where
  "decode_wire_packet bytes =
    (case read_canonical_proto_fields bytes of Some [Proto_Bytes core_tag body, Proto_Bytes signature_tag signature] \<Rightarrow>
       if core_tag = 1 \<and> signature_tag = 2 then
         (case decode_wire_core body of None \<Rightarrow> None | Some core \<Rightarrow>
           let packet = \<lparr>packet_core = core, packet_signature = signature\<rparr> in
             if wire_packet_wellformed packet \<and> encode_wire_packet packet = bytes then Some packet else None)
       else None
     | _ \<Rightarrow> None)"

theorem the_exact_wire_message_decodes_from_its_canonical_bytes:
  assumes "wire_packet_wellformed packet"
  shows "decode_wire_packet (encode_wire_packet packet) = Some packet"
proof -
  have core: "wire_core_wellformed (packet_core packet)"
    using assms by (simp add: wire_packet_wellformed_def)
  have octets: "wire_octets (encode_wire_core (packet_core packet))"
    unfolding encode_wire_core_def
    by (rule encoded_wire_fields_are_octets) (use core in \<open>simp add: wire_core_wellformed_def\<close>)
  have items: "read_canonical_proto_fields (encode_wire_packet packet) = Some (packet_fields packet)"
    unfolding encode_wire_packet_def
    by (rule the_canonical_proto_codec_roundtrips_wellformed_fields)
      (use assms octets in \<open>simp add: wire_packet_wellformed_def packet_fields_def\<close>)
  show ?thesis using items assms wellformed_canonical_core_has_a_two_way_encoding[OF core]
    by (cases packet) (simp add: decode_wire_packet_def packet_fields_def Let_def)
qed

theorem every_accepted_wire_message_has_exactly_the_received_bytes:
  assumes "decode_wire_packet bytes = Some packet"
  shows "encode_wire_packet packet = bytes \<and> wire_packet_wellformed packet"
  using assms by (auto simp: decode_wire_packet_def Let_def split: option.splits list.splits proto_field.splits if_splits)

definition envelope_signing_bytes where
  "envelope_signing_bytes core =
    (let encoded = encode_wire_core core in
      [79,73,80,0,69,78,86,69,76,79,80,69,0] @ rev (put_le_octets 4 (length encoded)) @ encoded)"

definition secondary_for_product where
  "secondary_for_product known core =
    (case wire_secondary_code core of None \<Rightarrow> None | Some code \<Rightarrow> if code \<in> known then Some code else None)"

lemma unknown_secondary_values_have_no_authority_effect:
  "wire_secondary_code core = Some code \<Longrightarrow> code \<notin> known \<Longrightarrow> secondary_for_product known core = None"
  by (simp add: secondary_for_product_def)

lemma distinct_secondary_wire_values_have_distinct_original_encodings:
  fixes first second :: wire_core
  assumes "wire_core_wellformed first" "wire_core_wellformed second"
    "wire_secondary_code first \<noteq> wire_secondary_code second"
  shows "encode_wire_core first \<noteq> encode_wire_core second"
proof
  assume same: "encode_wire_core first = encode_wire_core second"
  have first_decoded: "decode_wire_core (encode_wire_core first) = Some first"
    by (rule wellformed_canonical_core_has_a_two_way_encoding[OF assms(1)])
  have second_decoded: "decode_wire_core (encode_wire_core second) = Some second"
    by (rule wellformed_canonical_core_has_a_two_way_encoding[OF assms(2)])
  have decoded_equal: "decode_wire_core (encode_wire_core first) = decode_wire_core (encode_wire_core second)"
    by (rule arg_cong[OF same])
  have same_value: "first = second"
    using decoded_equal by (simp only: first_decoded second_decoded option.inject)
  have "wire_secondary_code first = wire_secondary_code second"
    by (rule arg_cong[OF same_value])
  with assms(3) show False by contradiction
qed

end
