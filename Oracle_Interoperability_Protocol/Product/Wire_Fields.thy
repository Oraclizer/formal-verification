theory Wire_Fields
  imports Wire_Integers
begin

datatype proto_field =
    Proto_Varint nat nat
  | Proto_Fixed64 nat nat
  | Proto_Bytes nat wire_bytes

definition make_proto_tag :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "make_proto_tag number kind = kind + number * 8"

lemma make_proto_tag_components [simp]:
  "kind < 8 \<Longrightarrow> make_proto_tag number kind div 8 = number"
  "kind < 8 \<Longrightarrow> make_proto_tag number kind mod 8 = kind"
  by (simp_all add: make_proto_tag_def)

fun put_proto_field where
  "put_proto_field (Proto_Varint number value) =
    put_wire_varint (make_proto_tag number 0) @ put_wire_varint value"
| "put_proto_field (Proto_Fixed64 number value) =
    put_wire_varint (make_proto_tag number 1) @ put_le_octets 8 value"
| "put_proto_field (Proto_Bytes number bytes) =
    put_wire_varint (make_proto_tag number 2) @ put_wire_varint (length bytes) @ bytes"

fun wellformed_proto_field where
  "wellformed_proto_field (Proto_Varint number value) = (0 < number \<and> number < 2^29 \<and> value < 2^64)"
| "wellformed_proto_field (Proto_Fixed64 number value) = (0 < number \<and> number < 2^29 \<and> value < 256^8)"
| "wellformed_proto_field (Proto_Bytes number bytes) = (0 < number \<and> number < 2^29 \<and> wire_octets bytes)"

definition take_proto_field where
  "take_proto_field bytes =
    (case take_wire_varint bytes of None \<Rightarrow> None
     | Some (tag, tail) \<Rightarrow> let number = tag div 8; kind = tag mod 8 in
       if number = 0 \<or> number \<ge> 2^29 then None
       else if kind = 0 then
         (case take_wire_varint tail of None \<Rightarrow> None
          | Some (value, rest) \<Rightarrow> if value < 2^64 then Some (Proto_Varint number value, rest) else None)
       else if kind = 1 then
         if length tail \<ge> 8 \<and> wire_octets (take 8 tail)
         then Some (Proto_Fixed64 number (get_le_octets (take 8 tail)), drop 8 tail) else None
       else if kind = 2 then
         (case take_wire_varint tail of None \<Rightarrow> None
          | Some (count, rest) \<Rightarrow> if count \<le> length rest \<and> wire_octets (take count rest)
            then Some (Proto_Bytes number (take count rest), drop count rest) else None)
       else None)"

lemma canonical_proto_field_reads_with_its_exact_suffix:
  assumes "wellformed_proto_field field"
  shows "take_proto_field (put_proto_field field @ tail) = Some (field, tail)"
  using assms
  by (cases field)
    (simp_all add: take_proto_field_def the_shortest_varint_is_read_with_its_exact_suffix append_assoc
      Let_def get_le_octets_reads_every_representable_word)

fun take_proto_fields where
  "take_proto_fields 0 bytes = (if bytes = [] then Some [] else None)"
| "take_proto_fields (Suc fuel) bytes = (if bytes = [] then Some [] else
     case take_proto_field bytes of None \<Rightarrow> None
     | Some (field, rest) \<Rightarrow> map_option (Cons field) (take_proto_fields fuel rest))"

definition put_proto_fields where
  "put_proto_fields fields = concat (map put_proto_field fields)"

lemma wire_varint_never_empty:
  "put_wire_varint n \<noteq> []"
  by (subst put_wire_varint.simps) simp

lemma proto_field_never_empty:
  "put_proto_field field \<noteq> []"
  by (cases field) (simp_all add: wire_varint_never_empty)

lemma canonical_fields_are_read_with_sufficient_fuel:
  assumes "\<forall>field \<in> set fields. wellformed_proto_field field" "length fields \<le> fuel"
  shows "take_proto_fields fuel (put_proto_fields fields) = Some fields"
  using assms
proof (induction fields arbitrary: fuel)
  case Nil
  then show ?case by (cases fuel) (simp_all add: put_proto_fields_def)
next
  case (Cons field fields)
  then obtain rest where fuel: "fuel = Suc rest" "length fields \<le> rest" by (cases fuel) auto
  have parsed: "take_proto_fields rest (put_proto_fields fields) = Some fields"
    by (rule Cons.IH) (use Cons.prems(1) fuel(2) in auto)
  have head: "take_proto_field (put_proto_field field @ put_proto_fields fields) =
    Some (field, put_proto_fields fields)"
    by (rule canonical_proto_field_reads_with_its_exact_suffix) (use Cons.prems(1) in simp)
  show ?case using head parsed fuel proto_field_never_empty[of field]
    by (simp add: put_proto_fields_def)
qed

lemma encoded_fields_supply_enough_parser_fuel:
  "length fields \<le> length (put_proto_fields fields)"
proof (induction fields)
  case Nil
  then show ?case by (simp add: put_proto_fields_def)
next
  case (Cons field fields)
  have positive: "0 < length (put_proto_field field)"
    using proto_field_never_empty[of field] by simp
  show ?case using Cons.IH positive by (simp add: put_proto_fields_def; arith)
qed

definition read_canonical_proto_fields where
  "read_canonical_proto_fields bytes =
    (case take_proto_fields (length bytes) bytes of None \<Rightarrow> None
     | Some fields \<Rightarrow> if put_proto_fields fields = bytes then Some fields else None)"

lemma the_canonical_proto_codec_roundtrips_wellformed_fields:
  assumes "\<forall>field \<in> set fields. wellformed_proto_field field"
  shows "read_canonical_proto_fields (put_proto_fields fields) = Some fields"
  using canonical_fields_are_read_with_sufficient_fuel[OF assms encoded_fields_supply_enough_parser_fuel]
  by (simp add: read_canonical_proto_fields_def)

lemma each_accepted_proto_word_has_exactly_its_canonical_bytes:
  assumes "read_canonical_proto_fields bytes = Some fields"
  shows "put_proto_fields fields = bytes"
  using assms by (auto simp: read_canonical_proto_fields_def split: option.splits if_splits)

end
