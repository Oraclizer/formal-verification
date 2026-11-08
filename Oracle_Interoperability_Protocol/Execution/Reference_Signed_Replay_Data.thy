theory Reference_Signed_Replay_Data
  imports "OIP_Product.Wire_Product_Read"
begin

definition replay_first_core :: wire_core where
  "replay_first_core = \<lparr>wire_version = 6,
    wire_purpose = 1,
    wire_deployment = 7,
    wire_source_domain = 0,
    wire_target_domain = 2,
    wire_principal = 7,
    wire_key_number = 9,
    wire_authority_epoch = 9,
    wire_sent_seconds = 100,
    wire_ttl_seconds = 5,
    wire_uuid = [0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15],
    wire_message_family = Wire_Query,
    wire_primary_code = 1,
    wire_secondary_code = Some 77,
    wire_signature_scheme = 1,
    wire_operation_body = \<lparr>wire_opcode = 1,
    wire_words = [1,0,1,17],
    wire_blobs = [],
    wire_deadline = Deadline_Absent\<rparr>,
    wire_atomicity = 3,
    wire_priority = 3,
    wire_route_scope = 1\<rparr>"

definition replay_first_core_bytes :: wire_bytes where
  "replay_first_core_bytes = [8,6,16,1,25,7,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,41,2,0,0,0,0,0,0,0,49,7,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,4,104,1,112,77,120,1,154,1,38,8,1,17,1,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0]"

definition replay_first_signature :: wire_bytes where
  "replay_first_signature = [198,143,128,230,126,144,111,201,85,75,165,84,14,75,220,234,39,144,18,66,62,21,243,41,160,6,115,82,122,85,152,195,95,166,83,27,64,50,23,201,134,23,1,94,192,182,141,217,39,22,84,145,22,30,206,143,248,43,245,210,120,37,6,8]"

definition replay_first_bytes :: wire_bytes where
  "replay_first_bytes = [10,159,1,8,6,16,1,25,7,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,41,2,0,0,0,0,0,0,0,49,7,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,4,104,1,112,77,120,1,154,1,38,8,1,17,1,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0,18,64,198,143,128,230,126,144,111,201,85,75,165,84,14,75,220,234,39,144,18,66,62,21,243,41,160,6,115,82,122,85,152,195,95,166,83,27,64,50,23,201,134,23,1,94,192,182,141,217,39,22,84,145,22,30,206,143,248,43,245,210,120,37,6,8]"

abbreviation replay_first_packet where
  "replay_first_packet \<equiv> \<lparr>packet_core = replay_first_core, packet_signature = replay_first_signature\<rparr>"

lemma replay_first_encodes_the_exact_core:
  "encode_wire_core replay_first_core = replay_first_core_bytes"
  by (simp add: replay_first_core_def replay_first_core_bytes_def encode_wire_core_def core_fields_def secondary_field_def
      encode_wire_body_def body_fields_def put_proto_fields_def put_wire_varint.simps make_proto_tag_def small_number_eight_octets)

lemma replay_first_decodes_the_exact_signed_packet:
  "decode_wire_packet replay_first_bytes = Some replay_first_packet"
proof -
  have body: "wire_body_wellformed (wire_operation_body replay_first_core)"
    by (simp add: replay_first_core_def wire_body_wellformed_def body_fields_def)
  have octets: "wire_octets (encode_wire_body (wire_operation_body replay_first_core))"
    unfolding encode_wire_body_def
    by (rule encoded_wire_fields_are_octets) (use body in \<open>simp add: wire_body_wellformed_def\<close>)
  have valid: "wire_core_wellformed replay_first_core"
    using body octets by (simp add: wire_core_wellformed_def replay_first_core_def core_fields_def secondary_field_def wire_octets_def)
  have scheme: "wire_signature_scheme replay_first_core = 1" by (simp add: replay_first_core_def)
  have size: "length (encode_wire_core replay_first_core) < 256^4"
    by (simp add: replay_first_encodes_the_exact_core replay_first_core_bytes_def)
  have packet: "wire_packet_wellformed replay_first_packet"
    using valid scheme size by (simp add: wire_packet_wellformed_def replay_first_signature_def wire_octets_def)
  have encodes: "encode_wire_packet replay_first_packet = replay_first_bytes"
    by (simp add: encode_wire_packet_def packet_fields_def replay_first_encodes_the_exact_core replay_first_core_bytes_def
       replay_first_signature_def replay_first_bytes_def put_proto_fields_def put_wire_varint.simps make_proto_tag_def)
  show ?thesis unfolding encodes[symmetric] by (rule the_exact_wire_message_decodes_from_its_canonical_bytes[OF packet])
qed

definition replay_changed_core :: wire_core where
  "replay_changed_core = \<lparr>wire_version = 6,
    wire_purpose = 1,
    wire_deployment = 7,
    wire_source_domain = 0,
    wire_target_domain = 2,
    wire_principal = 7,
    wire_key_number = 9,
    wire_authority_epoch = 9,
    wire_sent_seconds = 100,
    wire_ttl_seconds = 5,
    wire_uuid = [0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15],
    wire_message_family = Wire_Query,
    wire_primary_code = 1,
    wire_secondary_code = Some 77,
    wire_signature_scheme = 1,
    wire_operation_body = \<lparr>wire_opcode = 1,
    wire_words = [1,0,1,18],
    wire_blobs = [],
    wire_deadline = Deadline_Absent\<rparr>,
    wire_atomicity = 3,
    wire_priority = 3,
    wire_route_scope = 1\<rparr>"

definition replay_changed_core_bytes :: wire_bytes where
  "replay_changed_core_bytes = [8,6,16,1,25,7,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,41,2,0,0,0,0,0,0,0,49,7,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,4,104,1,112,77,120,1,154,1,38,8,1,17,1,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,18,0,0,0,0,0,0,0,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0]"

definition replay_changed_signature :: wire_bytes where
  "replay_changed_signature = [5,223,55,54,209,231,212,163,19,58,180,25,65,202,133,95,163,79,146,235,5,211,82,58,184,30,232,226,98,252,201,202,12,31,129,124,20,113,129,25,177,205,63,84,255,217,74,197,179,222,132,81,141,183,33,199,93,27,134,76,157,39,224,3]"

definition replay_changed_bytes :: wire_bytes where
  "replay_changed_bytes = [10,159,1,8,6,16,1,25,7,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,41,2,0,0,0,0,0,0,0,49,7,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,4,104,1,112,77,120,1,154,1,38,8,1,17,1,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,18,0,0,0,0,0,0,0,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0,18,64,5,223,55,54,209,231,212,163,19,58,180,25,65,202,133,95,163,79,146,235,5,211,82,58,184,30,232,226,98,252,201,202,12,31,129,124,20,113,129,25,177,205,63,84,255,217,74,197,179,222,132,81,141,183,33,199,93,27,134,76,157,39,224,3]"

abbreviation replay_changed_packet where
  "replay_changed_packet \<equiv> \<lparr>packet_core = replay_changed_core, packet_signature = replay_changed_signature\<rparr>"

lemma replay_changed_encodes_the_exact_core:
  "encode_wire_core replay_changed_core = replay_changed_core_bytes"
  by (simp add: replay_changed_core_def replay_changed_core_bytes_def encode_wire_core_def core_fields_def secondary_field_def
      encode_wire_body_def body_fields_def put_proto_fields_def put_wire_varint.simps make_proto_tag_def small_number_eight_octets)

lemma replay_changed_decodes_the_exact_signed_packet:
  "decode_wire_packet replay_changed_bytes = Some replay_changed_packet"
proof -
  have body: "wire_body_wellformed (wire_operation_body replay_changed_core)"
    by (simp add: replay_changed_core_def wire_body_wellformed_def body_fields_def)
  have octets: "wire_octets (encode_wire_body (wire_operation_body replay_changed_core))"
    unfolding encode_wire_body_def
    by (rule encoded_wire_fields_are_octets) (use body in \<open>simp add: wire_body_wellformed_def\<close>)
  have valid: "wire_core_wellformed replay_changed_core"
    using body octets by (simp add: wire_core_wellformed_def replay_changed_core_def core_fields_def secondary_field_def wire_octets_def)
  have scheme: "wire_signature_scheme replay_changed_core = 1" by (simp add: replay_changed_core_def)
  have size: "length (encode_wire_core replay_changed_core) < 256^4"
    by (simp add: replay_changed_encodes_the_exact_core replay_changed_core_bytes_def)
  have packet: "wire_packet_wellformed replay_changed_packet"
    using valid scheme size by (simp add: wire_packet_wellformed_def replay_changed_signature_def wire_octets_def)
  have encodes: "encode_wire_packet replay_changed_packet = replay_changed_bytes"
    by (simp add: encode_wire_packet_def packet_fields_def replay_changed_encodes_the_exact_core replay_changed_core_bytes_def
       replay_changed_signature_def replay_changed_bytes_def put_proto_fields_def put_wire_varint.simps make_proto_tag_def)
  show ?thesis unfolding encodes[symmetric] by (rule the_exact_wire_message_decodes_from_its_canonical_bytes[OF packet])
qed

end
