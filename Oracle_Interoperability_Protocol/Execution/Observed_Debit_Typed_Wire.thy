theory Observed_Debit_Typed_Wire
  imports "OIP_Product.Wire_Debit_Bridge"
begin

definition debit_fixture_amount :: wire_bytes where
  "debit_fixture_amount = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5]"

definition debit_fixture_body :: wire_body where
  "debit_fixture_body = \<lparr>wire_opcode = 1,
     wire_words = [33,33,2,2,9,0,17,17,7,2,3,1,17,0,17,7,0,9,1,17,0,0],
     wire_blobs = [debit_fixture_amount], wire_deadline = Deadline_Absent\<rparr>"

definition debit_fixture_core :: wire_core where
  "debit_fixture_core = \<lparr>wire_version = 6, wire_purpose = 1, wire_deployment = 7,
    wire_source_domain = 0, wire_target_domain = 0, wire_principal = 7, wire_key_number = 9,
    wire_authority_epoch = 9, wire_sent_seconds = 100, wire_ttl_seconds = 5,
    wire_uuid = [2,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15], wire_message_family = Wire_State_Sync,
    wire_primary_code = 1, wire_secondary_code = Some 77, wire_signature_scheme = 1,
    wire_operation_body = debit_fixture_body, wire_atomicity = 3, wire_priority = 3, wire_route_scope = 1\<rparr>"

definition debit_fixture_signature :: wire_bytes where
  "debit_fixture_signature = [60,43,189,110,10,111,227,63,91,21,72,26,160,235,248,249,136,1,47,179,251,94,240,157,255,247,192,140,188,186,211,164,217,106,41,39,197,5,27,120,226,245,26,189,212,103,216,155,162,184,149,196,74,20,179,217,37,166,125,102,237,12,105,15]"

definition actual_debit_core_bytes :: wire_bytes where
  "actual_debit_core_bytes = [8,6,16,1,25,7,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,41,0,0,0,0,0,0,0,0,49,7,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,2,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,1,104,1,112,77,120,1,130,1,234,1,8,1,17,33,0,0,0,0,0,0,0,17,33,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,26,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0]"

definition actual_debit_packet_bytes :: wire_bytes where
  "actual_debit_packet_bytes = [10,228,2,8,6,16,1,25,7,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,41,0,0,0,0,0,0,0,0,49,7,0,0,0,0,0,0,0,57,9,0,0,0,0,0,0,0,65,9,0,0,0,0,0,0,0,73,100,0,0,0,0,0,0,0,81,5,0,0,0,0,0,0,0,90,16,2,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15,96,1,104,1,112,77,120,1,130,1,234,1,8,1,17,33,0,0,0,0,0,0,0,17,33,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,2,0,0,0,0,0,0,0,17,3,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,7,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,9,0,0,0,0,0,0,0,17,1,0,0,0,0,0,0,0,17,17,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,26,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,184,1,3,192,1,3,201,1,1,0,0,0,0,0,0,0,18,64,60,43,189,110,10,111,227,63,91,21,72,26,160,235,248,249,136,1,47,179,251,94,240,157,255,247,192,140,188,186,211,164,217,106,41,39,197,5,27,120,226,245,26,189,212,103,216,155,162,184,149,196,74,20,179,217,37,166,125,102,237,12,105,15]"

lemma debit_fixture_core_encoding:
  "encode_wire_core debit_fixture_core = actual_debit_core_bytes"
  by (simp add: debit_fixture_core_def debit_fixture_body_def debit_fixture_amount_def
      actual_debit_core_bytes_def encode_wire_core_def core_fields_def secondary_field_def
      encode_wire_body_def body_fields_def put_proto_fields_def put_wire_varint.simps
      make_proto_tag_def small_number_eight_octets)

lemma debit_fixture_body_wellformed: "wire_body_wellformed debit_fixture_body"
  by (simp add: wire_body_wellformed_def debit_fixture_body_def debit_fixture_amount_def
      body_fields_def wire_octets_def)

lemma debit_fixture_core_wellformed: "wire_core_wellformed debit_fixture_core"
proof -
  have body: "wire_octets (encode_wire_body debit_fixture_body)"
    unfolding encode_wire_body_def
    by (rule encoded_wire_fields_are_octets) (use debit_fixture_body_wellformed in \<open>simp add: wire_body_wellformed_def\<close>)
  have fields: "\<forall>field \<in> set (core_fields debit_fixture_core). wellformed_proto_field field"
    using body
    by (simp add: debit_fixture_core_def core_fields_def secondary_field_def wire_octets_def)
  have operation: "wire_opcode debit_fixture_body = 1" by (simp add: debit_fixture_body_def)
  show ?thesis using fields
    by (simp add: wire_core_wellformed_def debit_fixture_core_def
        debit_fixture_body_wellformed operation)
qed

lemma debit_fixture_packet_decodes:
  "decode_wire_packet actual_debit_packet_bytes =
    Some \<lparr>packet_core = debit_fixture_core, packet_signature = debit_fixture_signature\<rparr>"
proof -
  let ?packet = "\<lparr>packet_core = debit_fixture_core, packet_signature = debit_fixture_signature\<rparr>"
  have fits: "length (encode_wire_core debit_fixture_core) < 256^4"
    by (simp add: debit_fixture_core_encoding actual_debit_core_bytes_def)
  have scheme: "wire_signature_scheme debit_fixture_core = 1" by (simp add: debit_fixture_core_def)
  have valid: "wire_packet_wellformed ?packet"
    using debit_fixture_core_wellformed fits scheme
    by (simp add: wire_packet_wellformed_def debit_fixture_signature_def wire_octets_def)
  have exact: "encode_wire_packet ?packet = actual_debit_packet_bytes"
    by (simp add: encode_wire_packet_def packet_fields_def put_proto_fields_def put_wire_varint.simps
        make_proto_tag_def debit_fixture_core_encoding debit_fixture_signature_def
        actual_debit_core_bytes_def actual_debit_packet_bytes_def)
  show ?thesis unfolding exact[symmetric]
    by (rule the_exact_wire_message_decodes_from_its_canonical_bytes[OF valid])
qed

lemma debit_fixture_operands:
  obtains native where "decode_native_call_prefix debit_fixture_core = Some native"
    "native_reference native = 33" "native_id native = (7,33)" "native_session native = 2"
    "native_cut native = \<lparr>cut_authority_epoch = 9, cut_revision = 2\<rparr>"
    "native_origin_epoch native = 9" "native_origin native = (0,17)" "native_asset native = 17"
    "native_funding_owner native = 7" "native_destination native = 2" "native_recipient native = 3"
    "native_amount native = 5" "native_proof_bytes native = []"
    "decode_ordinary_operands debit_fixture_core native = Some
      (Some \<lparr>credential_token = \<lparr>token_asset = 17, token_owner = 7, token_generation = 0\<rparr>,
        credential_epoch = 9, credential_origin = (0,17)\<rparr>, [(17,0)], Wire_Debit 0)"
proof -
  let ?native = "\<lparr>native_reference = 33, native_id = (7,33), native_session = 2,
    native_cut = \<lparr>cut_authority_epoch = 9, cut_revision = 2\<rparr>, native_origin_epoch = 9,
    native_origin = (0,17), native_asset = 17, native_funding_owner = 7, native_destination = 2,
    native_recipient = 3, native_amount = 5, native_tail_words = [1,17,0,17,7,0,9,1,17,0,0],
    native_proof_bytes = []\<rparr>"
  have decoded: "decode_native_call_prefix debit_fixture_core = Some ?native"
    by (simp add: debit_fixture_core_def debit_fixture_body_def debit_fixture_amount_def
        decode_native_call_prefix_def wire_octets_def Let_def)
  show thesis by (rule that[OF decoded])
    (simp_all add: debit_fixture_core_def debit_fixture_body_def decode_ordinary_operands_def
        decode_wire_credential_prefix_def decode_ordinary_tail_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms debit_fixture_core_encoding
    debit_fixture_packet_decodes debit_fixture_operands})
  then () else error "Unexpected oracle in the exact signed Debit codec"
\<close>

end
