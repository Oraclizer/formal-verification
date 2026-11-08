theory Wire_Code_Encoder
  imports Wire_Code_Reencoding
begin

text \<open>
  Numeric values below are the natural-number projections of Rust u64
  values and octet vectors.  The machine-domain condition is kept explicit.
  Generated-message presence is represented by option fields, including
  the invalid present-false deadline that has no semantic wire counterpart.
\<close>

function code_varint_loop :: "nat \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes" where
  "code_varint_loop number out =
    (if number < 128 then out @ [number]
     else code_varint_loop (number div 128) (out @ [128 + number mod 128]))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(number,out). number)")
    (auto intro: a_continued_varint_division_decreases)

declare code_varint_loop.simps [simp del]

lemma appending_varint_bytes_is_the_canonical_numeric_encoding:
  "code_varint_loop number out = out @ put_wire_varint number"
proof (induction number arbitrary: out rule: less_induct)
  case (less number)
  show ?case
  proof (cases "number < 128")
    case True
    then show ?thesis
      by (simp add: code_varint_loop.simps[of number] put_wire_varint.simps[of number])
  next
    case False
    have smaller: "number div 128 < number"
      by (rule a_continued_varint_division_decreases[OF False])
    show ?thesis using False less.IH[OF smaller]
      by (simp add: code_varint_loop.simps[of number] put_wire_varint.simps[of number])
  qed
qed

definition code_field_varint where
  "code_field_varint tag value = code_varint_loop (8 * tag) [] @ code_varint_loop value []"

definition code_field_fixed64 where
  "code_field_fixed64 tag value = code_varint_loop (8 * tag + 1) [] @ put_le_octets 8 value"

definition code_field_bytes where
  "code_field_bytes tag bytes = code_varint_loop (8 * tag + 2) [] @
    code_varint_loop (length bytes) [] @ bytes"

lemma source_field_emitters_are_the_model_field_emitters:
  "code_field_varint tag value = put_proto_field (Proto_Varint tag value)"
  "code_field_fixed64 tag value = put_proto_field (Proto_Fixed64 tag value)"
  "code_field_bytes tag bytes = put_proto_field (Proto_Bytes tag bytes)"
  by (simp_all add: code_field_varint_def code_field_fixed64_def code_field_bytes_def
    appending_varint_bytes_is_the_canonical_numeric_encoding make_proto_tag_def
    mult.commute add.commute)

fun code_deadline_bytes where
  "code_deadline_bytes Deadline_Absent = []"
| "code_deadline_bytes Deadline_Indefinite = code_field_varint 4 1"
| "code_deadline_bytes (Deadline_At seconds) = code_field_fixed64 5 seconds"

lemma source_deadline_emission_is_the_model_emission:
  "code_deadline_bytes deadline = put_proto_fields (deadline_fields deadline)"
  by (cases deadline)
    (simp_all add: source_field_emitters_are_the_model_field_emitters put_proto_fields_def)

lemma source_fixed64_emitter_is_the_model_function:
  "code_field_fixed64 tag = put_proto_field \<circ> Proto_Fixed64 tag"
  by (rule ext) (simp add: source_field_emitters_are_the_model_field_emitters)

lemma source_bytes_emitter_is_the_model_function:
  "code_field_bytes tag = put_proto_field \<circ> Proto_Bytes tag"
  by (rule ext) (simp add: source_field_emitters_are_the_model_field_emitters)

definition code_body_bytes where
  "code_body_bytes body = code_field_varint 1 (wire_opcode body) @
    concat (map (code_field_fixed64 2) (wire_words body)) @
    concat (map (code_field_bytes 3) (wire_blobs body)) @
    code_deadline_bytes (wire_deadline body)"

lemma the_source_operation_emitter_has_the_exact_model_bytes:
  "code_body_bytes body = encode_wire_body body"
  by (simp add: code_body_bytes_def encode_wire_body_def body_fields_def put_proto_fields_def
    source_field_emitters_are_the_model_field_emitters source_deadline_emission_is_the_model_emission
    source_fixed64_emitter_is_the_model_function source_bytes_emitter_is_the_model_function)

datatype code_source_deadline = Code_Indefinite bool | Code_Finite nat

record code_source_operation =
  source_opcode :: "nat option"
  source_words :: "nat list"
  source_blobs :: "wire_bytes list"
  source_deadline :: "code_source_deadline option"

fun code_project_deadline where
  "code_project_deadline None = Some Deadline_Absent"
| "code_project_deadline (Some (Code_Indefinite True)) = Some Deadline_Indefinite"
| "code_project_deadline (Some (Code_Indefinite False)) = None"
| "code_project_deadline (Some (Code_Finite seconds)) = Some (Deadline_At seconds)"

definition code_project_operation where
  "code_project_operation source =
    (case source_opcode source of None \<Rightarrow> None | Some operation \<Rightarrow>
      map_option (\<lambda>deadline. \<lparr>wire_opcode = operation, wire_words = source_words source,
        wire_blobs = source_blobs source, wire_deadline = deadline\<rparr>)
        (code_project_deadline (source_deadline source)))"

definition code_source_encode_operation where
  "code_source_encode_operation source =
    (case source_opcode source of None \<Rightarrow> None | Some operation \<Rightarrow>
      let prefix = code_field_varint 1 operation @
        concat (map (code_field_fixed64 2) (source_words source)) @
        concat (map (code_field_bytes 3) (source_blobs source))
      in case source_deadline source of None \<Rightarrow> Some prefix
       | Some (Code_Indefinite valid) \<Rightarrow>
           if valid then Some (prefix @ code_field_varint 4 1) else None
       | Some (Code_Finite seconds) \<Rightarrow> Some (prefix @ code_field_fixed64 5 seconds))"

theorem generated_operation_presence_and_deadline_are_preserved_exactly:
  "code_source_encode_operation source =
    map_option encode_wire_body (code_project_operation source)"
proof (cases "source_opcode source")
  case None
  then show ?thesis by (simp add: code_source_encode_operation_def code_project_operation_def)
next
  case (Some operation)
  then have opcode: "source_opcode source = Some operation" .
  show ?thesis
  proof (cases "source_deadline source")
    case None
    then show ?thesis using opcode
      by (simp add: code_source_encode_operation_def code_project_operation_def code_body_bytes_def
        the_source_operation_emitter_has_the_exact_model_bytes[symmetric] Let_def)
  next
    case (Some deadline)
    then have ending: "source_deadline source = Some deadline" .
    show ?thesis
    proof (cases deadline)
      case (Code_Indefinite valid)
      then show ?thesis using opcode ending
        by (cases valid)
          (simp_all add: code_source_encode_operation_def code_project_operation_def code_body_bytes_def
            the_source_operation_emitter_has_the_exact_model_bytes[symmetric] Let_def)
    next
      case (Code_Finite seconds)
      then show ?thesis using opcode ending
        by (simp add: code_source_encode_operation_def code_project_operation_def code_body_bytes_def
          the_source_operation_emitter_has_the_exact_model_bytes[symmetric] Let_def)
    qed
  qed
qed

lemma a_present_false_deadline_has_no_accepted_encoding:
  "source_deadline source = Some (Code_Indefinite False) \<Longrightarrow>
    code_source_encode_operation source = None"
  by (cases "source_opcode source") (simp_all add: code_source_encode_operation_def Let_def)

definition code_core_shape_allowed where
  "code_core_shape_allowed core \<longleftrightarrow>
    length (wire_uuid core) = 16 \<and> wire_uuid core ! 6 div 16 = 4 \<and> wire_uuid core ! 8 div 64 = 2 \<and>
    wire_primary_code core \<in> {1..5} \<and> wire_signature_scheme core \<in> {1,2} \<and>
    wire_atomicity core \<in> {1..3} \<and> wire_priority core \<le> 4 \<and>
    (wire_priority core = 0 \<longrightarrow> wire_atomicity core = 3) \<and>
    valid_family_opcode (wire_message_family core) (wire_opcode (wire_operation_body core))"

definition code_core_machine_domain where
  "code_core_machine_domain core \<longleftrightarrow>
    wire_body_wellformed (wire_operation_body core) \<and>
    (\<forall>field \<in> set (core_fields core). wellformed_proto_field field)"

lemma source_shape_and_machine_domain_are_exactly_model_wellformedness:
  "code_core_shape_allowed core \<and> code_core_machine_domain core \<longleftrightarrow>
    wire_core_wellformed core"
  by (simp add: code_core_shape_allowed_def code_core_machine_domain_def wire_core_wellformed_def)

definition code_core_bytes where
  "code_core_bytes core =
    code_field_varint 1 (wire_version core) @ code_field_varint 2 (wire_purpose core) @
    concat (map (\<lambda>(tag,value). code_field_fixed64 tag value)
      [(3,wire_deployment core),(4,wire_source_domain core),(5,wire_target_domain core),
       (6,wire_principal core),(7,wire_key_number core),(8,wire_authority_epoch core),
       (9,wire_sent_seconds core),(10,wire_ttl_seconds core)]) @
    code_field_bytes 11 (wire_uuid core) @
    code_field_varint 12 (family_number (wire_message_family core)) @
    code_field_varint 13 (wire_primary_code core) @
    (case wire_secondary_code core of None \<Rightarrow> [] | Some secondary \<Rightarrow> code_field_varint 14 secondary) @
    code_field_varint 15 (wire_signature_scheme core) @
    code_field_bytes (15 + family_number (wire_message_family core)) (code_body_bytes (wire_operation_body core)) @
    code_field_varint 23 (wire_atomicity core) @ code_field_varint 24 (wire_priority core) @
    code_field_fixed64 25 (wire_route_scope core)"

theorem the_source_core_field_sequence_is_the_exact_model_sequence:
  "code_core_bytes core = encode_wire_core core"
  by (cases "wire_secondary_code core")
    (simp_all add: code_core_bytes_def encode_wire_core_def core_fields_def secondary_field_def
      put_proto_fields_def source_field_emitters_are_the_model_field_emitters
      the_source_operation_emitter_has_the_exact_model_bytes)

definition code_encode_core where
  "code_encode_core core =
    (if code_core_shape_allowed core then Some (code_core_bytes core) else None)"

definition code_typed_encode_core where
  "code_typed_encode_core core =
    (if code_core_machine_domain core then code_encode_core core else None)"

lemma the_typed_source_encoder_is_the_checked_canonical_encoder:
  "code_typed_encode_core core =
    (if wire_core_wellformed core then Some (encode_wire_core core) else None)"
  by (auto simp: code_typed_encode_core_def code_encode_core_def
    the_source_core_field_sequence_is_the_exact_model_sequence
    source_shape_and_machine_domain_are_exactly_model_wellformedness[symmetric]
    split: if_splits)

theorem the_typed_source_core_encoder_discharges_the_reencoding_obligation:
  "code_core_encoder_sound code_typed_encode_core"
  by (auto simp: code_core_encoder_sound_def code_typed_encode_core_def code_encode_core_def
    the_source_core_field_sequence_is_the_exact_model_sequence
    source_shape_and_machine_domain_are_exactly_model_wellformedness[symmetric])

definition code_packet_bytes where
  "code_packet_bytes packet = code_field_bytes 1 (code_core_bytes (packet_core packet)) @
    code_field_bytes 2 (packet_signature packet)"

theorem the_source_packet_field_sequence_is_the_exact_model_sequence:
  "code_packet_bytes packet = encode_wire_packet packet"
  by (simp add: code_packet_bytes_def encode_wire_packet_def packet_fields_def put_proto_fields_def
    source_field_emitters_are_the_model_field_emitters
    the_source_core_field_sequence_is_the_exact_model_sequence)

definition code_encode_packet where
  "code_encode_packet packet =
    (if (wire_signature_scheme (packet_core packet) = 1 \<and> length (packet_signature packet) \<noteq> 64) \<or>
        (wire_signature_scheme (packet_core packet) = 2 \<and> packet_signature packet = [])
     then None
     else case code_typed_encode_core (packet_core packet) of None \<Rightarrow> None | Some core_bytes \<Rightarrow>
       if length core_bytes \<ge> 2^32 \<or> \<not> wire_octets (packet_signature packet)
       then None else Some (code_packet_bytes packet))"

theorem the_typed_source_packet_encoder_discharges_the_reencoding_obligation:
  "code_packet_encoder_sound code_encode_packet"
  unfolding code_packet_encoder_sound_def
proof (intro allI impI)
  fix packet bytes
  assume encoded: "code_encode_packet packet = Some bytes"
  obtain core_bytes where core_encoded: "code_typed_encode_core (packet_core packet) = Some core_bytes"
    and limit: "length core_bytes < 2^32"
    and octets: "wire_octets (packet_signature packet)"
    and single: "wire_signature_scheme (packet_core packet) = 1 \<longrightarrow> length (packet_signature packet) = 64"
    and threshold: "wire_signature_scheme (packet_core packet) = 2 \<longrightarrow> packet_signature packet \<noteq> []"
    and bytes: "code_packet_bytes packet = bytes"
    using encoded
    by (auto simp: code_encode_packet_def split: option.splits if_splits)
  have core: "wire_core_wellformed (packet_core packet) \<and> encode_wire_core (packet_core packet) = core_bytes"
    by (rule the_typed_source_core_encoder_discharges_the_reencoding_obligation[
      unfolded code_core_encoder_sound_def, rule_format, OF core_encoded])
  have scheme: "wire_signature_scheme (packet_core packet) \<in> {1,2}"
    using core by (simp add: wire_core_wellformed_def)
  have packet: "wire_packet_wellformed packet"
    using core limit octets single threshold scheme
    by (auto simp: wire_packet_wellformed_def)
  have exact: "encode_wire_packet packet = bytes"
    using bytes by (simp only: the_source_packet_field_sequence_is_the_exact_model_sequence)
  show "wire_packet_wellformed packet \<and> encode_wire_packet packet = bytes"
    by (rule conjI[OF packet exact])
qed

theorem a_generated_core_accepted_by_the_typed_source_encoder_has_the_model_value:
  assumes "code_reencoding_decode shape parse code_typed_encode_core bytes = Some core"
  shows "decode_wire_core bytes = Some core" "encode_wire_core core = bytes"
  using every_checked_core_is_the_model_decoding_of_the_received_bytes[OF
    the_typed_source_core_encoder_discharges_the_reencoding_obligation assms] by auto

theorem a_generated_packet_accepted_by_the_typed_source_encoder_has_the_model_value:
  assumes "code_reencoding_decode shape parse code_encode_packet bytes = Some packet"
  shows "decode_wire_packet bytes = Some packet" "encode_wire_packet packet = bytes"
  using every_checked_packet_is_the_model_decoding_of_the_received_bytes[OF
    the_typed_source_packet_encoder_discharges_the_reencoding_obligation assms] by auto

end
