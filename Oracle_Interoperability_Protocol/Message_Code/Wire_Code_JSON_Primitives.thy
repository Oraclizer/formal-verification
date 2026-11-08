theory Wire_Code_JSON_Primitives
  imports Wire_Code_Operands_Ack
begin

definition code_json_ascii :: "string \<Rightarrow> wire_bytes" where
  "code_json_ascii text = map (of_char :: char \<Rightarrow> nat) text"

definition code_json_expect :: "wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes option" where
  "code_json_expect token bytes =
    (if take (length token) bytes = token then Some (drop (length token) bytes) else None)"

definition code_json_open_key :: "string \<Rightarrow> wire_bytes" where
  "code_json_open_key name = [123,34] @ code_json_ascii name @ [34,58]"

definition code_json_next_key :: "string \<Rightarrow> wire_bytes" where
  "code_json_next_key name = [44,34] @ code_json_ascii name @ [34,58]"

fun code_json_digits :: "nat \<Rightarrow> wire_bytes \<Rightarrow> (nat \<times> wire_bytes) option" where
  "code_json_digits value [] = Some (value,[])"
| "code_json_digits value (byte # tail) =
    (if 48 \<le> byte \<and> byte \<le> 57 then
       let next = 10 * value + (byte - 48) in
       if next < 2^64 then code_json_digits next tail else None
     else Some (value,byte # tail))"

definition code_json_u64 :: "wire_bytes \<Rightarrow> (nat \<times> wire_bytes) option" where
  "code_json_u64 bytes =
    (case bytes of [] \<Rightarrow> None | byte # tail \<Rightarrow>
      if byte = 48 then Some (0,tail)
      else if 49 \<le> byte \<and> byte \<le> 57 then code_json_digits (byte - 48) tail else None)"

lemma decimal_source_accumulation_keeps_the_u64_bound:
  assumes "initial < 2^64" "code_json_digits initial bytes = Some (value,rest)"
  shows "value < 2^64"
  using assms
  by (induction bytes arbitrary: initial) (auto simp: Let_def split: if_splits)

lemma a_governance_json_integer_cannot_be_truncated:
  assumes "code_json_u64 bytes = Some (value,rest)"
  shows "value < 2^64"
proof (cases bytes)
  case Nil
  then show ?thesis using assms by (simp add: code_json_u64_def)
next
  case (Cons byte tail)
  show ?thesis
  proof (cases "byte = 48")
    case True
    then show ?thesis using assms Cons by (simp add: code_json_u64_def)
  next
    case False
    have digit: "49 \<le> byte" "byte \<le> 57"
      and parsed: "code_json_digits (byte - 48) tail = Some (value,rest)"
      using assms Cons False by (auto simp: code_json_u64_def split: if_splits)
    have small: "byte - 48 \<le> 9" using digit(2) by arith
    have large: "(9::nat) < 2^64" by simp
    have initial: "byte - 48 < 2^64" by (rule le_less_trans[OF small large])
    show ?thesis
      by (rule decimal_source_accumulation_keeps_the_u64_bound[OF initial parsed])
  qed
qed

fun code_json_enum_from :: "nat \<Rightarrow> string list \<Rightarrow> wire_bytes \<Rightarrow> (nat \<times> wire_bytes) option" where
  "code_json_enum_from index [] bytes = None"
| "code_json_enum_from index (name # names) bytes =
    (case code_json_expect ([34] @ code_json_ascii name @ [34]) bytes of
       Some rest \<Rightarrow> Some (index,rest)
     | None \<Rightarrow> code_json_enum_from (Suc index) names bytes)"

definition code_json_enum :: "string list \<Rightarrow> wire_bytes \<Rightarrow> (nat \<times> wire_bytes) option" where
  "code_json_enum names bytes = code_json_enum_from 0 names bytes"

fun code_json_elements ::
  "nat \<Rightarrow> (wire_bytes \<Rightarrow> ('a \<times> wire_bytes) option) \<Rightarrow> wire_bytes \<Rightarrow> ('a list \<times> wire_bytes) option" where
  "code_json_elements 0 parse bytes = None"
| "code_json_elements (Suc fuel) parse bytes =
    (case parse bytes of None \<Rightarrow> None | Some (value,tail) \<Rightarrow>
      (case tail of [] \<Rightarrow> None | separator # rest \<Rightarrow>
        if separator = 93 then Some ([value],rest)
        else if separator = 44 then
          map_option (\<lambda>(values,ending). (value # values,ending)) (code_json_elements fuel parse rest)
        else None))"

definition code_json_array :: "(wire_bytes \<Rightarrow> ('a \<times> wire_bytes) option) \<Rightarrow> wire_bytes \<Rightarrow> ('a list \<times> wire_bytes) option" where
  "code_json_array parse bytes =
    (case bytes of [] \<Rightarrow> None | opening # tail \<Rightarrow>
      if opening \<noteq> 91 then None
      else case tail of [] \<Rightarrow> code_json_elements (length bytes) parse tail
       | first # rest \<Rightarrow> if first = 93 then Some ([],rest)
         else code_json_elements (length bytes) parse tail)"

definition code_json_complete :: "(wire_bytes \<Rightarrow> ('a \<times> wire_bytes) option) \<Rightarrow> wire_bytes \<Rightarrow> 'a option" where
  "code_json_complete parse bytes =
    (case parse bytes of Some (value,[]) \<Rightarrow> Some value | _ \<Rightarrow> None)"

definition code_json_pair :: "(wire_bytes \<Rightarrow> ('a \<times> wire_bytes) option) \<Rightarrow> (wire_bytes \<Rightarrow> ('b \<times> wire_bytes) option) \<Rightarrow> wire_bytes \<Rightarrow> (('a \<times> 'b) \<times> wire_bytes) option" where
  "code_json_pair left right bytes =
    Option.bind (code_json_expect [91] bytes) (\<lambda>first.
      Option.bind (left first) (\<lambda>(a,second).
        Option.bind (code_json_expect [44] second) (\<lambda>third.
          Option.bind (right third) (\<lambda>(b,fourth).
            map_option (\<lambda>rest. ((a,b),rest)) (code_json_expect [93] fourth)))))"

definition code_json_triple :: "(wire_bytes \<Rightarrow> ('a \<times> wire_bytes) option) \<Rightarrow> (wire_bytes \<Rightarrow> ('b \<times> wire_bytes) option) \<Rightarrow> (wire_bytes \<Rightarrow> ('c \<times> wire_bytes) option) \<Rightarrow> wire_bytes \<Rightarrow> (('a \<times> 'b \<times> 'c) \<times> wire_bytes) option" where
  "code_json_triple first second third bytes =
    Option.bind (code_json_expect [91] bytes) (\<lambda>r0.
      Option.bind (first r0) (\<lambda>(a,r1).
        Option.bind (code_json_expect [44] r1) (\<lambda>r2.
          Option.bind (second r2) (\<lambda>(b,r3).
            Option.bind (code_json_expect [44] r3) (\<lambda>r4.
              Option.bind (third r4) (\<lambda>(c,r5).
                map_option (\<lambda>rest. ((a,b,c),rest)) (code_json_expect [93] r5)))))))"

definition code_json_lex3 :: "(nat \<times> nat \<times> nat) \<Rightarrow> (nat \<times> nat \<times> nat) \<Rightarrow> bool" where
  "code_json_lex3 first second \<longleftrightarrow>
    (case (first,second) of ((a,b,c),(x,y,z)) \<Rightarrow>
      a < x \<or> (a = x \<and> (b < y \<or> (b = y \<and> c < z))))"

definition code_json_strict_list :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> (wire_bytes \<Rightarrow> ('a \<times> wire_bytes) option) \<Rightarrow> wire_bytes \<Rightarrow> ('a list \<times> wire_bytes) option" where
  "code_json_strict_list relation parse bytes =
    Option.bind (code_json_array parse bytes) (\<lambda>(values,rest).
      if sorted_wrt relation values then Some (values,rest) else None)"

end
