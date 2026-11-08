theory Wire_Core
  imports Wire_Body
begin

datatype wire_family =
    Wire_State_Sync | Wire_Regulatory | Wire_Lock | Wire_Query | Wire_Ack | Wire_Heartbeat | Wire_Governance

fun family_number :: "wire_family \<Rightarrow> nat" where
  "family_number Wire_State_Sync = 1"
| "family_number Wire_Regulatory = 2"
| "family_number Wire_Lock = 3"
| "family_number Wire_Query = 4"
| "family_number Wire_Ack = 5"
| "family_number Wire_Heartbeat = 6"
| "family_number Wire_Governance = 7"

definition family_at_number where
  "family_at_number number = List.find (\<lambda>family. family_number family = number)
    [Wire_State_Sync, Wire_Regulatory, Wire_Lock, Wire_Query, Wire_Ack, Wire_Heartbeat, Wire_Governance]"

lemma family_discriminator_roundtrip [simp]:
  "family_at_number (family_number family) = Some family"
  by (cases family) (simp_all add: family_at_number_def)

fun valid_family_opcode :: "wire_family \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_family_opcode Wire_State_Sync operation = (operation \<in> {1..6})"
| "valid_family_opcode Wire_Regulatory operation = (operation \<in> {1..3})"
| "valid_family_opcode Wire_Lock operation = (operation \<in> {1..8})"
| "valid_family_opcode Wire_Query operation = (operation \<in> {1..8})"
| "valid_family_opcode Wire_Ack operation = (operation \<in> {1,2})"
| "valid_family_opcode Wire_Heartbeat operation = (operation \<in> {1,2})"
| "valid_family_opcode Wire_Governance operation = (operation \<in> {1,2})"

record wire_core =
  wire_version :: nat
  wire_purpose :: nat
  wire_deployment :: nat
  wire_source_domain :: nat
  wire_target_domain :: nat
  wire_principal :: nat
  wire_key_number :: nat
  wire_authority_epoch :: nat
  wire_sent_seconds :: nat
  wire_ttl_seconds :: nat
  wire_uuid :: wire_bytes
  wire_message_family :: wire_family
  wire_primary_code :: nat
  wire_secondary_code :: "nat option"
  wire_signature_scheme :: nat
  wire_operation_body :: wire_body
  wire_atomicity :: nat
  wire_priority :: nat
  wire_route_scope :: nat

definition secondary_field where
  "secondary_field value = (case value of None \<Rightarrow> [] | Some code \<Rightarrow> [Proto_Varint 14 code])"

definition core_fields where
  "core_fields core =
    [Proto_Varint 1 (wire_version core), Proto_Varint 2 (wire_purpose core),
     Proto_Fixed64 3 (wire_deployment core), Proto_Fixed64 4 (wire_source_domain core),
     Proto_Fixed64 5 (wire_target_domain core), Proto_Fixed64 6 (wire_principal core),
     Proto_Fixed64 7 (wire_key_number core), Proto_Fixed64 8 (wire_authority_epoch core),
     Proto_Fixed64 9 (wire_sent_seconds core), Proto_Fixed64 10 (wire_ttl_seconds core),
     Proto_Bytes 11 (wire_uuid core), Proto_Varint 12 (family_number (wire_message_family core)),
     Proto_Varint 13 (wire_primary_code core)] @ secondary_field (wire_secondary_code core) @
    [Proto_Varint 15 (wire_signature_scheme core),
     Proto_Bytes (15 + family_number (wire_message_family core)) (encode_wire_body (wire_operation_body core)),
     Proto_Varint 23 (wire_atomicity core), Proto_Varint 24 (wire_priority core), Proto_Fixed64 25 (wire_route_scope core)]"

fun parse_secondary_field where
  "parse_secondary_field (Proto_Varint tag code # tail) =
    (if tag = 14 then (Some code, tail) else (None, Proto_Varint tag code # tail))"
| "parse_secondary_field items = (None, items)"

definition parse_core_body_tail where
  "parse_core_body_tail kind items =
    (let (secondary, remainder) = parse_secondary_field items in
       case remainder of [Proto_Varint scheme_tag scheme, Proto_Bytes body_tag raw,
                         Proto_Varint atomicity_tag atomicity, Proto_Varint priority_tag priority, Proto_Fixed64 scope_tag scope] \<Rightarrow>
          if scheme_tag = 15 \<and> body_tag = 15 + kind \<and> scheme \<in> {1,2} \<and>
             atomicity_tag = 23 \<and> priority_tag = 24 \<and> scope_tag = 25 then
            (case (family_at_number kind, decode_wire_body raw) of
               (Some family, Some body) \<Rightarrow> if valid_family_opcode family (wire_opcode body)
                   then Some (secondary, scheme, family, body, atomicity, priority, scope) else None
             | _ \<Rightarrow> None)
          else None
        | _ \<Rightarrow> None)"

fun expect_proto_varint where
  "expect_proto_varint expected (Proto_Varint tag value) = (if tag = expected then Some value else None)"
| "expect_proto_varint expected item = None"

fun expect_proto_fixed64 where
  "expect_proto_fixed64 expected (Proto_Fixed64 tag value) = (if tag = expected then Some value else None)"
| "expect_proto_fixed64 expected item = None"

fun expect_proto_bytes where
  "expect_proto_bytes expected (Proto_Bytes tag value) = (if tag = expected then Some value else None)"
| "expect_proto_bytes expected item = None"

definition parse_core_fields where
  "parse_core_fields items =
    (if length items < 13 then None else
      Option.bind (expect_proto_varint 1 (items ! 0)) (\<lambda>version.
       Option.bind (expect_proto_varint 2 (items ! 1)) (\<lambda>purpose.
        Option.bind (expect_proto_fixed64 3 (items ! 2)) (\<lambda>deployment.
         Option.bind (expect_proto_fixed64 4 (items ! 3)) (\<lambda>source.
          Option.bind (expect_proto_fixed64 5 (items ! 4)) (\<lambda>target.
           Option.bind (expect_proto_fixed64 6 (items ! 5)) (\<lambda>who.
            Option.bind (expect_proto_fixed64 7 (items ! 6)) (\<lambda>key.
             Option.bind (expect_proto_fixed64 8 (items ! 7)) (\<lambda>epoch.
              Option.bind (expect_proto_fixed64 9 (items ! 8)) (\<lambda>sent.
               Option.bind (expect_proto_fixed64 10 (items ! 9)) (\<lambda>ttl.
                Option.bind (expect_proto_bytes 11 (items ! 10)) (\<lambda>uuid.
                 Option.bind (expect_proto_varint 12 (items ! 11)) (\<lambda>kind.
                  Option.bind (expect_proto_varint 13 (items ! 12)) (\<lambda>primary.
        map_option (\<lambda>(secondary,scheme,family,body,atomicity,priority,scope).
          \<lparr>wire_version = version, wire_purpose = purpose, wire_deployment = deployment, wire_source_domain = source,
            wire_target_domain = target, wire_principal = who, wire_key_number = key, wire_authority_epoch = epoch,
            wire_sent_seconds = sent, wire_ttl_seconds = ttl, wire_uuid = uuid, wire_message_family = family,
            wire_primary_code = primary, wire_secondary_code = secondary, wire_signature_scheme = scheme, wire_operation_body = body,
            wire_atomicity = atomicity, wire_priority = priority, wire_route_scope = scope\<rparr>)
          (parse_core_body_tail kind (drop 13 items))))))))))))))))"

definition wire_core_wellformed where
  "wire_core_wellformed core \<longleftrightarrow>
    length (wire_uuid core) = 16 \<and> wire_uuid core ! 6 div 16 = 4 \<and> wire_uuid core ! 8 div 64 = 2 \<and>
    wire_primary_code core \<in> {1..5} \<and> wire_signature_scheme core \<in> {1,2} \<and>
    wire_atomicity core \<in> {1..3} \<and> wire_priority core \<le> 4 \<and> (wire_priority core = 0 \<longrightarrow> wire_atomicity core = 3) \<and>
    valid_family_opcode (wire_message_family core) (wire_opcode (wire_operation_body core)) \<and>
    wire_body_wellformed (wire_operation_body core) \<and> (\<forall>field \<in> set (core_fields core). wellformed_proto_field field)"

definition encode_wire_core where
  "encode_wire_core core = put_proto_fields (core_fields core)"

definition decode_wire_core where
  "decode_wire_core bytes =
    (case read_canonical_proto_fields bytes of None \<Rightarrow> None | Some items \<Rightarrow>
      case parse_core_fields items of None \<Rightarrow> None | Some core \<Rightarrow>
        if wire_core_wellformed core \<and> encode_wire_core core = bytes then Some core else None)"

lemma core_body_tail_roundtrip:
  assumes "wire_signature_scheme core \<in> {1,2}"
    "valid_family_opcode (wire_message_family core) (wire_opcode (wire_operation_body core))"
    "wire_body_wellformed (wire_operation_body core)"
  shows "parse_core_body_tail (family_number (wire_message_family core))
    (secondary_field (wire_secondary_code core) @
      [Proto_Varint 15 (wire_signature_scheme core),
       Proto_Bytes (15 + family_number (wire_message_family core)) (encode_wire_body (wire_operation_body core)),
       Proto_Varint 23 (wire_atomicity core), Proto_Varint 24 (wire_priority core), Proto_Fixed64 25 (wire_route_scope core)]) =
    Some (wire_secondary_code core, wire_signature_scheme core, wire_message_family core, wire_operation_body core,
      wire_atomicity core, wire_priority core, wire_route_scope core)"
  using assms by (cases "wire_secondary_code core")
    (simp_all add: parse_core_body_tail_def secondary_field_def Let_def wellformed_wire_body_roundtrip)

lemma typed_core_shape_roundtrip:
  assumes "wire_core_wellformed core"
  shows "parse_core_fields (core_fields core) = Some core"
proof -
  have suffix: "parse_core_body_tail (family_number (wire_message_family core))
    (secondary_field (wire_secondary_code core) @
      [Proto_Varint 15 (wire_signature_scheme core),
       Proto_Bytes (15 + family_number (wire_message_family core)) (encode_wire_body (wire_operation_body core)),
       Proto_Varint 23 (wire_atomicity core), Proto_Varint 24 (wire_priority core), Proto_Fixed64 25 (wire_route_scope core)]) =
    Some (wire_secondary_code core, wire_signature_scheme core, wire_message_family core, wire_operation_body core,
      wire_atomicity core, wire_priority core, wire_route_scope core)"
    by (rule core_body_tail_roundtrip) (use assms in \<open>simp_all add: wire_core_wellformed_def\<close>)
  show ?thesis using assms suffix
    by (cases core) (simp add: parse_core_fields_def core_fields_def wire_core_wellformed_def)
qed

theorem wellformed_canonical_core_has_a_two_way_encoding:
  "wire_core_wellformed core \<Longrightarrow> decode_wire_core (encode_wire_core core) = Some core"
proof -
  assume valid: "wire_core_wellformed core"
  have bytes: "read_canonical_proto_fields (encode_wire_core core) = Some (core_fields core)"
    unfolding encode_wire_core_def
    by (rule the_canonical_proto_codec_roundtrips_wellformed_fields) (use valid in \<open>simp add: wire_core_wellformed_def\<close>)
  show ?thesis using valid bytes typed_core_shape_roundtrip[OF valid] by (simp add: decode_wire_core_def)
qed

lemma accepted_core_bytes_preserve_all_original_fields:
  assumes "decode_wire_core bytes = Some core"
  shows "wire_core_wellformed core \<and> encode_wire_core core = bytes"
  using assms by (auto simp: decode_wire_core_def split: option.splits if_splits)

end
