theory Wire_Body
  imports Wire_Fields
begin

datatype wire_deadline = Deadline_Absent | Deadline_Indefinite | Deadline_At nat

record wire_body =
  wire_opcode :: nat
  wire_words :: "nat list"
  wire_blobs :: "wire_bytes list"
  wire_deadline :: wire_deadline

fun deadline_fields where
  "deadline_fields Deadline_Absent = []"
| "deadline_fields Deadline_Indefinite = [Proto_Varint 4 1]"
| "deadline_fields (Deadline_At seconds) = [Proto_Fixed64 5 seconds]"

fun parse_deadline_fields where
  "parse_deadline_fields [] = Some Deadline_Absent"
| "parse_deadline_fields [Proto_Varint tag value] = (if tag = 4 \<and> value = 1 then Some Deadline_Indefinite else None)"
| "parse_deadline_fields [Proto_Fixed64 tag seconds] = (if tag = 5 then Some (Deadline_At seconds) else None)"
| "parse_deadline_fields items = None"

definition body_fields where
  "body_fields body =
    Proto_Varint 1 (wire_opcode body) # (map (Proto_Fixed64 2) (wire_words body) @
      map (Proto_Bytes 3) (wire_blobs body) @ deadline_fields (wire_deadline body))"

fun consume_body_words where
  "consume_body_words (Proto_Fixed64 tag value # rest) =
    (if tag = 2 then let (values, tail) = consume_body_words rest in (value # values, tail)
     else ([], Proto_Fixed64 tag value # rest))"
| "consume_body_words items = ([], items)"

fun consume_body_blobs where
  "consume_body_blobs (Proto_Bytes tag bytes # rest) =
    (if tag = 3 then let (values, tail) = consume_body_blobs rest in (bytes # values, tail)
     else ([], Proto_Bytes tag bytes # rest))"
| "consume_body_blobs items = ([], items)"

fun parse_body_fields where
  "parse_body_fields (Proto_Varint tag operation # tail) =
    (if tag = 1 then let (words, remainder) = consume_body_words tail;
         (blobs, ending) = consume_body_blobs remainder
     in map_option (\<lambda>deadline. \<lparr>wire_opcode = operation, wire_words = words, wire_blobs = blobs, wire_deadline = deadline\<rparr>)
          (parse_deadline_fields ending) else None)"
| "parse_body_fields items = None"

lemma consume_words_stops_at_the_next_typed_field:
  "consume_body_words (map (Proto_Fixed64 2) words @ map (Proto_Bytes 3) blobs @ deadline_fields deadline) =
    (words, map (Proto_Bytes 3) blobs @ deadline_fields deadline)"
proof (induction words)
  case Nil
  then show ?case by (cases blobs; cases deadline) simp_all
next
  case (Cons word words)
  then show ?case by simp
qed

lemma consume_blobs_stops_at_the_exact_optional_deadline:
  "consume_body_blobs (map (Proto_Bytes 3) blobs @ deadline_fields deadline) =
    (blobs, deadline_fields deadline)"
proof (induction blobs)
  case Nil
  then show ?case by (cases deadline) simp_all
next
  case (Cons blob blobs)
  then show ?case by simp
qed

lemma exact_deadline_roundtrip [simp]:
  "parse_deadline_fields (deadline_fields deadline) = Some deadline"
  by (cases deadline) simp_all

lemma body_shape_parser_reads_the_exact_semantic_fields:
  "parse_body_fields (body_fields body) = Some body"
  by (cases body)
    (simp add: body_fields_def Let_def consume_words_stops_at_the_next_typed_field consume_blobs_stops_at_the_exact_optional_deadline)

definition encode_wire_body where
  "encode_wire_body body = put_proto_fields (body_fields body)"

definition decode_wire_body where
  "decode_wire_body bytes =
    (case read_canonical_proto_fields bytes of None \<Rightarrow> None
      | Some items \<Rightarrow> case parse_body_fields items of None \<Rightarrow> None
        | Some body \<Rightarrow> if encode_wire_body body = bytes then Some body else None)"

definition wire_body_wellformed where
  "wire_body_wellformed body \<longleftrightarrow> (\<forall>field \<in> set (body_fields body). wellformed_proto_field field)"

lemma wellformed_wire_body_roundtrip:
  assumes "wire_body_wellformed body"
  shows "decode_wire_body (encode_wire_body body) = Some body"
  using the_canonical_proto_codec_roundtrips_wellformed_fields assms
  by (simp add: decode_wire_body_def encode_wire_body_def wire_body_wellformed_def body_shape_parser_reads_the_exact_semantic_fields)

lemma accepted_body_bytes_are_exact:
  assumes "decode_wire_body bytes = Some body"
  shows "encode_wire_body body = bytes"
  using assms by (auto simp: decode_wire_body_def split: option.splits if_splits)

end
