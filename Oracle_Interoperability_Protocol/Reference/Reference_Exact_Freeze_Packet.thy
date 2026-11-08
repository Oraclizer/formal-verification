theory Reference_Exact_Freeze_Packet
  imports "OIP_Product.Wire_Ordinary_Operands"
begin

definition guard_freeze_body :: wire_body where
  "guard_freeze_body = \<lparr>wire_opcode = 6,
    wire_words = [42, 42, 2, 12, 9, 0, 17, 17, 7, 2, 3, 5, 3, 4, 0],
    wire_blobs = [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]],
    wire_deadline = Deadline_Absent\<rparr>"

definition guard_freeze_core :: wire_core where
  "guard_freeze_core = \<lparr>wire_version = 6,
    wire_purpose = 1,
    wire_deployment = 7,
    wire_source_domain = 0,
    wire_target_domain = 2,
    wire_principal = 7,
    wire_key_number = 9,
    wire_authority_epoch = 9,
    wire_sent_seconds = 1793986673,
    wire_ttl_seconds = 180,
    wire_uuid = [42,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15],
    wire_message_family = Wire_State_Sync,
    wire_primary_code = 1,
    wire_secondary_code = Some 77,
    wire_signature_scheme = 1,
    wire_operation_body = guard_freeze_body,
    wire_atomicity = 3,
    wire_priority = 3,
    wire_route_scope = 1\<rparr>"

definition guard_freeze_signature :: wire_bytes where
  "guard_freeze_signature = [50,110,240,30,71,196,176,121,178,216,105,146,145,11,78,31,19,183,75,75,157,253,184,85,186,91,100,4,67,255,225,145,76,82,50,239,64,200,128,67,65,146,75,72,14,5,84,85,108,128,255,69,129,54,160,83,115,109,206,10,194,161,233,0]"

definition guard_freeze_core_bytes :: wire_bytes where
  "guard_freeze_core_bytes = [8,6,16,1,25,7,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,41,2,0,0,0,0,0,0,0,49,7,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,113,16,238,106,0,0,0,0,81,180,0,0,0,0,0,0,0,90,16,42,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,1,104,1,112,77,120,1,130,1,205,1,8,6,17,42,0,0,0,0,0,0,0,17,42,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,12,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,5,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,4,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,26,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,26,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0]"

definition guard_freeze_packet_bytes :: wire_bytes where
  "guard_freeze_packet_bytes = [10,199,2,8,6,16,1,25,7,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,41,2,0,0,0,0,0,0,0,49,7,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,113,16,238,106,0,0,0,0,81,180,0,0,0,0,0,0,0,90,16,42,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,1,104,1,112,77,120,1,130,1,205,1,8,6,17,42,0,0,0,0,0,0,0,17,42,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,12,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,5,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,4,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,26,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,26,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0,18,64,50,110,240,30,71,196,176,121,178,216,105,146,145,11,78,31,19,183,75,75,157,253,184,85,186,91,100,4,67,255,225,145,76,82,50,239,64,200,128,67,65,146,75,72,14,5,84,85,108,128,255,69,129,54,160,83,115,109,206,10,194,161,233,0]"

lemma guard_freeze_wide_words:
  "put_le_octets 8 1793986673 = [113,16,238,106,0,0,0,0]"
proof -
  have width: "(8::nat) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (0))))))))" by simp
  show "put_le_octets 8 1793986673 = [113,16,238,106,0,0,0,0]" unfolding width by simp_all
qed

abbreviation guard_freeze_packet where
  "guard_freeze_packet \<equiv> \<lparr>packet_core = guard_freeze_core, packet_signature = guard_freeze_signature\<rparr>"

lemma guard_freeze_exact_core_encoding:
  "encode_wire_core guard_freeze_core = guard_freeze_core_bytes"
  by (simp add: guard_freeze_core_def guard_freeze_body_def guard_freeze_core_bytes_def encode_wire_core_def
      core_fields_def secondary_field_def encode_wire_body_def body_fields_def put_proto_fields_def
      put_wire_varint.simps make_proto_tag_def small_number_eight_octets guard_freeze_wide_words)

lemma guard_freeze_decodes_from_the_full_native_envelope:
  "decode_wire_packet guard_freeze_packet_bytes = Some guard_freeze_packet"
proof -
  have body_wellformed: "wire_body_wellformed guard_freeze_body"
    by (simp add: wire_body_wellformed_def guard_freeze_body_def body_fields_def wire_octets_def)
  have octets: "wire_octets (encode_wire_body guard_freeze_body)"
    unfolding encode_wire_body_def
    by (rule encoded_wire_fields_are_octets) (use body_wellformed in \<open>simp add: wire_body_wellformed_def\<close>)
  have core_fields: "\<forall>field \<in> set (core_fields guard_freeze_core). wellformed_proto_field field"
    using octets by (simp add: guard_freeze_core_def core_fields_def secondary_field_def wire_octets_def)
  have core: "wire_core_wellformed guard_freeze_core"
    using body_wellformed core_fields by (simp add: wire_core_wellformed_def guard_freeze_core_def guard_freeze_body_def)
  have fits: "length (encode_wire_core guard_freeze_core) < 256^4"
    by (simp add: guard_freeze_exact_core_encoding guard_freeze_core_bytes_def)
  have scheme: "wire_signature_scheme guard_freeze_core = 1"
    by (simp add: guard_freeze_core_def)
  have valid: "wire_packet_wellformed guard_freeze_packet"
    using core fits scheme by (simp add: wire_packet_wellformed_def guard_freeze_signature_def wire_octets_def)
  have exact: "encode_wire_packet guard_freeze_packet = guard_freeze_packet_bytes"
    by (simp add: encode_wire_packet_def packet_fields_def put_proto_fields_def put_wire_varint.simps
        make_proto_tag_def guard_freeze_exact_core_encoding guard_freeze_signature_def
        guard_freeze_core_bytes_def guard_freeze_packet_bytes_def)
  show ?thesis unfolding exact[symmetric]
    by (rule the_exact_wire_message_decodes_from_its_canonical_bytes[OF valid])
qed

end
