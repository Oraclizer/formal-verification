theory Reference_Exact_Guard_Packets
  imports "OIP_Product.Wire_Ordinary_Operands"
begin

definition guard_debit_body :: wire_body where
  "guard_debit_body = \<lparr>wire_opcode = 1,
    wire_words = [33, 33, 2, 2, 9, 0, 17, 17, 7, 2, 3, 1, 17, 0, 17, 7, 0, 9, 1, 17, 0, 1],
    wire_blobs = [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5]],
    wire_deadline = Deadline_Absent\<rparr>"

definition guard_debit_core :: wire_core where
  "guard_debit_core = \<lparr>wire_version = 6,
    wire_purpose = 1,
    wire_deployment = 7,
    wire_source_domain = 0,
    wire_target_domain = 0,
    wire_principal = 7,
    wire_key_number = 9,
    wire_authority_epoch = 9,
    wire_sent_seconds = 100,
    wire_ttl_seconds = 5,
    wire_uuid = [2,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15],
    wire_message_family = Wire_State_Sync,
    wire_primary_code = 1,
    wire_secondary_code = Some 77,
    wire_signature_scheme = 1,
    wire_operation_body = guard_debit_body,
    wire_atomicity = 3,
    wire_priority = 3,
    wire_route_scope = 1\<rparr>"

definition guard_debit_signature :: wire_bytes where
  "guard_debit_signature = [79,233,32,106,24,176,241,30,187,67,62,246,28,91,18,58,140,58,126,43,162,3,194,103,58,173,238,117,165,104,63,114,72,193,111,62,116,253,120,66,21,143,252,149,17,108,235,80,65,229,212,226,133,75,3,87,126,159,248,119,144,115,11,3]"

definition guard_debit_core_bytes :: wire_bytes where
  "guard_debit_core_bytes = [8,6,16,1,25,7,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,41,0,0,0,0,0,0,0,0,49,7,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,2,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,1,104,1,112,77,120,1,130,1,234,1,8,1,17,33,0,0,0,0,0,0,0,17,33,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,26,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0]"

definition guard_debit_packet_bytes :: wire_bytes where
  "guard_debit_packet_bytes = [10,228,2,8,6,16,1,25,7,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,41,0,0,0,0,0,0,0,0,49,7,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,2,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,1,104,1,112,77,120,1,130,1,234,1,8,1,17,33,0,0,0,0,0,0,0,17,33,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,26,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0,18,64,79,233,32,106,24,176,241,30,187,67,62,246,28,91,18,58,140,58,126,43,162,3,194,103,58,173,238,117,165,104,63,114,72,193,111,62,116,253,120,66,21,143,252,149,17,108,235,80,65,229,212,226,133,75,3,87,126,159,248,119,144,115,11,3]"

abbreviation guard_debit_packet where
  "guard_debit_packet \<equiv> \<lparr>packet_core = guard_debit_core, packet_signature = guard_debit_signature\<rparr>"

lemma guard_debit_exact_core_encoding:
  "encode_wire_core guard_debit_core = guard_debit_core_bytes"
  by (simp add: guard_debit_core_def guard_debit_body_def guard_debit_core_bytes_def encode_wire_core_def
      core_fields_def secondary_field_def encode_wire_body_def body_fields_def put_proto_fields_def
      put_wire_varint.simps make_proto_tag_def small_number_eight_octets)

lemma guard_debit_decodes_from_the_full_native_envelope:
  "decode_wire_packet guard_debit_packet_bytes = Some guard_debit_packet"
proof -
  have body_wellformed: "wire_body_wellformed guard_debit_body"
    by (simp add: wire_body_wellformed_def guard_debit_body_def body_fields_def wire_octets_def)
  have octets: "wire_octets (encode_wire_body guard_debit_body)"
    unfolding encode_wire_body_def
    by (rule encoded_wire_fields_are_octets) (use body_wellformed in \<open>simp add: wire_body_wellformed_def\<close>)
  have core_fields: "\<forall>field \<in> set (core_fields guard_debit_core). wellformed_proto_field field"
    using octets by (simp add: guard_debit_core_def core_fields_def secondary_field_def wire_octets_def)
  have core: "wire_core_wellformed guard_debit_core"
    using body_wellformed core_fields by (simp add: wire_core_wellformed_def guard_debit_core_def guard_debit_body_def)
  have fits: "length (encode_wire_core guard_debit_core) < 256^4"
    by (simp add: guard_debit_exact_core_encoding guard_debit_core_bytes_def)
  have scheme: "wire_signature_scheme guard_debit_core = 1"
    by (simp add: guard_debit_core_def)
  have valid: "wire_packet_wellformed guard_debit_packet"
    using core fits scheme by (simp add: wire_packet_wellformed_def guard_debit_signature_def wire_octets_def)
  have exact: "encode_wire_packet guard_debit_packet = guard_debit_packet_bytes"
    by (simp add: encode_wire_packet_def packet_fields_def put_proto_fields_def put_wire_varint.simps
        make_proto_tag_def guard_debit_exact_core_encoding guard_debit_signature_def
        guard_debit_core_bytes_def guard_debit_packet_bytes_def)
  show ?thesis unfolding exact[symmetric]
    by (rule the_exact_wire_message_decodes_from_its_canonical_bytes[OF valid])
qed

definition guard_ack_left_body :: wire_body where
  "guard_ack_left_body = \<lparr>wire_opcode = 1,
    wire_words = [0, 17, 3, 99, 17, 7, 2, 3, 9, 1],
    wire_blobs = [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5]],
    wire_deadline = Deadline_Absent\<rparr>"

definition guard_ack_left_core :: wire_core where
  "guard_ack_left_core = \<lparr>wire_version = 6,
    wire_purpose = 1,
    wire_deployment = 7,
    wire_source_domain = 99,
    wire_target_domain = 2,
    wire_principal = 99,
    wire_key_number = 9,
    wire_authority_epoch = 9,
    wire_sent_seconds = 100,
    wire_ttl_seconds = 5,
    wire_uuid = [50,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15],
    wire_message_family = Wire_Ack,
    wire_primary_code = 1,
    wire_secondary_code = Some 77,
    wire_signature_scheme = 1,
    wire_operation_body = guard_ack_left_body,
    wire_atomicity = 3,
    wire_priority = 3,
    wire_route_scope = 1\<rparr>"

definition guard_ack_left_signature :: wire_bytes where
  "guard_ack_left_signature = [95,121,38,10,248,18,52,120,3,21,99,66,56,249,217,126,83,138,176,220,218,224,140,184,89,79,166,136,73,195,42,125,56,80,215,228,60,37,165,82,146,68,87,2,101,178,67,170,163,126,61,142,162,175,7,214,167,217,226,77,73,173,36,4]"

definition guard_ack_left_core_bytes :: wire_bytes where
  "guard_ack_left_core_bytes = [8,6,16,1,25,7,0,0,0,0,0,0,0,33,99,0,0,0,0,0,0,0,41,2,0,0,0,0,0,0,0,49,99,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,50,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,5,104,1,112,77,120,1,162,1,126,8,1,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,99,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,26,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0]"

definition guard_ack_left_packet_bytes :: wire_bytes where
  "guard_ack_left_packet_bytes = [10,247,1,8,6,16,1,25,7,0,0,0,0,0,0,0,33,99,0,0,0,0,0,0,0,41,2,0,0,0,0,0,0,0,49,99,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,50,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,5,104,1,112,77,120,1,162,1,126,8,1,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,99,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,26,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0,18,64,95,121,38,10,248,18,52,120,3,21,99,66,56,249,217,126,83,138,176,220,218,224,140,184,89,79,166,136,73,195,42,125,56,80,215,228,60,37,165,82,146,68,87,2,101,178,67,170,163,126,61,142,162,175,7,214,167,217,226,77,73,173,36,4]"

abbreviation guard_ack_left_packet where
  "guard_ack_left_packet \<equiv> \<lparr>packet_core = guard_ack_left_core, packet_signature = guard_ack_left_signature\<rparr>"

lemma guard_ack_left_exact_core_encoding:
  "encode_wire_core guard_ack_left_core = guard_ack_left_core_bytes"
  by (simp add: guard_ack_left_core_def guard_ack_left_body_def guard_ack_left_core_bytes_def encode_wire_core_def
      core_fields_def secondary_field_def encode_wire_body_def body_fields_def put_proto_fields_def
      put_wire_varint.simps make_proto_tag_def small_number_eight_octets)

lemma guard_ack_left_decodes_from_the_full_native_envelope:
  "decode_wire_packet guard_ack_left_packet_bytes = Some guard_ack_left_packet"
proof -
  have body_wellformed: "wire_body_wellformed guard_ack_left_body"
    by (simp add: wire_body_wellformed_def guard_ack_left_body_def body_fields_def wire_octets_def)
  have octets: "wire_octets (encode_wire_body guard_ack_left_body)"
    unfolding encode_wire_body_def
    by (rule encoded_wire_fields_are_octets) (use body_wellformed in \<open>simp add: wire_body_wellformed_def\<close>)
  have core_fields: "\<forall>field \<in> set (core_fields guard_ack_left_core). wellformed_proto_field field"
    using octets by (simp add: guard_ack_left_core_def core_fields_def secondary_field_def wire_octets_def)
  have core: "wire_core_wellformed guard_ack_left_core"
    using body_wellformed core_fields by (simp add: wire_core_wellformed_def guard_ack_left_core_def guard_ack_left_body_def)
  have fits: "length (encode_wire_core guard_ack_left_core) < 256^4"
    by (simp add: guard_ack_left_exact_core_encoding guard_ack_left_core_bytes_def)
  have scheme: "wire_signature_scheme guard_ack_left_core = 1"
    by (simp add: guard_ack_left_core_def)
  have valid: "wire_packet_wellformed guard_ack_left_packet"
    using core fits scheme by (simp add: wire_packet_wellformed_def guard_ack_left_signature_def wire_octets_def)
  have exact: "encode_wire_packet guard_ack_left_packet = guard_ack_left_packet_bytes"
    by (simp add: encode_wire_packet_def packet_fields_def put_proto_fields_def put_wire_varint.simps
        make_proto_tag_def guard_ack_left_exact_core_encoding guard_ack_left_signature_def
        guard_ack_left_core_bytes_def guard_ack_left_packet_bytes_def)
  show ?thesis unfolding exact[symmetric]
    by (rule the_exact_wire_message_decodes_from_its_canonical_bytes[OF valid])
qed

definition guard_ack_right_body :: wire_body where
  "guard_ack_right_body = \<lparr>wire_opcode = 1,
    wire_words = [0, 17, 3, 99, 17, 7, 2, 3, 9, 1],
    wire_blobs = [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5]],
    wire_deadline = Deadline_Absent\<rparr>"

definition guard_ack_right_core :: wire_core where
  "guard_ack_right_core = \<lparr>wire_version = 6,
    wire_purpose = 1,
    wire_deployment = 7,
    wire_source_domain = 99,
    wire_target_domain = 2,
    wire_principal = 99,
    wire_key_number = 9,
    wire_authority_epoch = 9,
    wire_sent_seconds = 100,
    wire_ttl_seconds = 5,
    wire_uuid = [51,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15],
    wire_message_family = Wire_Ack,
    wire_primary_code = 1,
    wire_secondary_code = Some 77,
    wire_signature_scheme = 1,
    wire_operation_body = guard_ack_right_body,
    wire_atomicity = 3,
    wire_priority = 3,
    wire_route_scope = 1\<rparr>"

definition guard_ack_right_signature :: wire_bytes where
  "guard_ack_right_signature = [88,213,0,68,2,1,216,11,245,102,229,187,160,61,12,38,251,171,16,67,209,122,167,166,144,80,158,16,193,18,33,184,113,3,87,189,29,16,22,53,39,250,144,80,1,224,104,11,109,252,48,106,237,254,77,109,174,239,254,217,243,6,12,13]"

definition guard_ack_right_core_bytes :: wire_bytes where
  "guard_ack_right_core_bytes = [8,6,16,1,25,7,0,0,0,0,0,0,0,33,99,0,0,0,0,0,0,0,41,2,0,0,0,0,0,0,0,49,99,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,51,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,5,104,1,112,77,120,1,162,1,126,8,1,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,99,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,26,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0]"

definition guard_ack_right_packet_bytes :: wire_bytes where
  "guard_ack_right_packet_bytes = [10,247,1,8,6,16,1,25,7,0,0,0,0,0,0,0,33,99,0,0,0,0,0,0,0,41,2,0,0,0,0,0,0,0,49,99,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,51,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,5,104,1,112,77,120,1,162,1,126,8,1,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,99,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,26,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0,18,64,88,213,0,68,2,1,216,11,245,102,229,187,160,61,12,38,251,171,16,67,209,122,167,166,144,80,158,16,193,18,33,184,113,3,87,189,29,16,22,53,39,250,144,80,1,224,104,11,109,252,48,106,237,254,77,109,174,239,254,217,243,6,12,13]"

abbreviation guard_ack_right_packet where
  "guard_ack_right_packet \<equiv> \<lparr>packet_core = guard_ack_right_core, packet_signature = guard_ack_right_signature\<rparr>"

lemma guard_ack_right_exact_core_encoding:
  "encode_wire_core guard_ack_right_core = guard_ack_right_core_bytes"
  by (simp add: guard_ack_right_core_def guard_ack_right_body_def guard_ack_right_core_bytes_def encode_wire_core_def
      core_fields_def secondary_field_def encode_wire_body_def body_fields_def put_proto_fields_def
      put_wire_varint.simps make_proto_tag_def small_number_eight_octets)

lemma guard_ack_right_decodes_from_the_full_native_envelope:
  "decode_wire_packet guard_ack_right_packet_bytes = Some guard_ack_right_packet"
proof -
  have body_wellformed: "wire_body_wellformed guard_ack_right_body"
    by (simp add: wire_body_wellformed_def guard_ack_right_body_def body_fields_def wire_octets_def)
  have octets: "wire_octets (encode_wire_body guard_ack_right_body)"
    unfolding encode_wire_body_def
    by (rule encoded_wire_fields_are_octets) (use body_wellformed in \<open>simp add: wire_body_wellformed_def\<close>)
  have core_fields: "\<forall>field \<in> set (core_fields guard_ack_right_core). wellformed_proto_field field"
    using octets by (simp add: guard_ack_right_core_def core_fields_def secondary_field_def wire_octets_def)
  have core: "wire_core_wellformed guard_ack_right_core"
    using body_wellformed core_fields by (simp add: wire_core_wellformed_def guard_ack_right_core_def guard_ack_right_body_def)
  have fits: "length (encode_wire_core guard_ack_right_core) < 256^4"
    by (simp add: guard_ack_right_exact_core_encoding guard_ack_right_core_bytes_def)
  have scheme: "wire_signature_scheme guard_ack_right_core = 1"
    by (simp add: guard_ack_right_core_def)
  have valid: "wire_packet_wellformed guard_ack_right_packet"
    using core fits scheme by (simp add: wire_packet_wellformed_def guard_ack_right_signature_def wire_octets_def)
  have exact: "encode_wire_packet guard_ack_right_packet = guard_ack_right_packet_bytes"
    by (simp add: encode_wire_packet_def packet_fields_def put_proto_fields_def put_wire_varint.simps
        make_proto_tag_def guard_ack_right_exact_core_encoding guard_ack_right_signature_def
        guard_ack_right_core_bytes_def guard_ack_right_packet_bytes_def)
  show ?thesis unfolding exact[symmetric]
    by (rule the_exact_wire_message_decodes_from_its_canonical_bytes[OF valid])
qed

end
