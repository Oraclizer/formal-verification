theory Wire_Integers
  imports Main
begin

section \<open>Protobuf numeric prefixes and exact fixed-width words\<close>

type_synonym wire_bytes = "nat list"

definition wire_octets where
  "wire_octets bytes \<longleftrightarrow> (\<forall>b \<in> set bytes. b < 256)"

lemma a_continued_varint_division_decreases:
  fixes n :: nat
  assumes "\<not> n < 128"
  shows "n div 128 < n"
proof -
  have positive: "0 < n" using assms by arith
  show ?thesis by (rule div_less_dividend) (simp, rule positive)
qed

function put_wire_varint :: "nat \<Rightarrow> wire_bytes" where
  "put_wire_varint n =
    (if n < 128 then [n] else (128 + n mod 128) # put_wire_varint (n div 128))"
  by pat_completeness auto
termination
proof (relation "measure id")
  show "wf (measure id)" by simp
  fix n :: nat
  assume large: "\<not> n < 128"
  have "n div 128 < n" by (rule a_continued_varint_division_decreases[OF large])
  then show "(n div 128, n) \<in> measure id" by simp
qed

declare put_wire_varint.simps [simp del]

fun take_wire_varint :: "wire_bytes \<Rightarrow> (nat \<times> wire_bytes) option" where
  "take_wire_varint [] = None"
| "take_wire_varint (byte # tail) =
    (if byte < 128 then Some (byte, tail)
     else if byte < 256 then map_option (\<lambda>(n, rest). (byte - 128 + 128 * n, rest)) (take_wire_varint tail)
     else None)"

lemma the_shortest_varint_is_read_with_its_exact_suffix:
  "take_wire_varint (put_wire_varint n @ tail) = Some (n, tail)"
proof (induction n arbitrary: tail rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 128")
    case True
    then show ?thesis by (simp add: put_wire_varint.simps[of n])
  next
    case False
    have smaller: "n div 128 < n" by (rule a_continued_varint_division_decreases[OF False])
    have octet: "n mod 128 < 128" by simp
    then have upper: "128 + n mod 128 < 256" by arith
    have reconstruct: "n mod 128 + 128 * (n div 128) = n"
      using div_mult_mod_eq[of n 128] by (simp add: mult.commute add.commute)
    show ?thesis using False upper less.IH[OF smaller, of tail] reconstruct
      by (simp add: put_wire_varint.simps[of n])
  qed
qed

lemma shortest_varint_is_an_octet_word:
  "wire_octets (put_wire_varint n)"
proof (induction n rule: less_induct)
  case (less n)
  then show ?case
  proof (cases "n < 128")
    case True
    then show ?thesis by (simp add: put_wire_varint.simps[of n] wire_octets_def)
  next
    case False
    have smaller: "n div 128 < n" by (rule a_continued_varint_division_decreases[OF False])
    have octet: "n mod 128 < 128" by simp
    then have upper: "128 + n mod 128 < 256" by arith
    show ?thesis using less.IH[OF smaller] False upper
      by (simp add: put_wire_varint.simps[of n] wire_octets_def)
  qed
qed

fun put_le_octets :: "nat \<Rightarrow> nat \<Rightarrow> wire_bytes" where
  "put_le_octets 0 n = []"
| "put_le_octets (Suc width) n = (n mod 256) # put_le_octets width (n div 256)"

fun get_le_octets :: "wire_bytes \<Rightarrow> nat" where
  "get_le_octets [] = 0"
| "get_le_octets (byte # tail) = byte + 256 * get_le_octets tail"

lemma put_le_octets_has_exact_width [simp]:
  "length (put_le_octets width n) = width"
  by (induction width arbitrary: n) simp_all

lemma put_le_octets_are_valid_bytes [simp]:
  "wire_octets (put_le_octets width n)"
  by (induction width arbitrary: n) (simp_all add: wire_octets_def)

lemma get_le_octets_reads_every_representable_word:
  assumes "n < 256 ^ width"
  shows "get_le_octets (put_le_octets width n) = n"
  using assms
proof (induction width arbitrary: n)
  case 0
  then show ?case by (simp; arith)
next
  case (Suc width)
  have high: "n div 256 < 256 ^ width" using Suc.prems
    by (simp add: div_less_iff_less_mult mult.commute)
  have reconstruct: "n mod 256 + 256 * (n div 256) = n"
    using div_mult_mod_eq[of n 256] by (simp add: mult.commute add.commute)
  show ?case using Suc.IH[OF high] reconstruct by simp
qed

lemma zero_le_octets_are_zero:
  "put_le_octets width 0 = replicate width 0"
  by (induction width) simp_all

lemma small_number_one_octet_then_zeroes:
  assumes "n < 256"
  shows "put_le_octets (Suc width) n = n # replicate width 0"
  using assms by (simp add: zero_le_octets_are_zero)

lemma small_number_eight_octets:
  assumes "n < 256"
  shows "put_le_octets 8 n = [n,0,0,0,0,0,0,0]"
proof -
  have width: "(8::nat) = Suc 7" by simp
  have "put_le_octets 8 n = n # replicate 7 0"
    unfolding width by (rule small_number_one_octet_then_zeroes[OF assms])
  also have "... = [n,0,0,0,0,0,0,0]" by (simp add: numeral_eq_Suc)
  finally show ?thesis .
qed

lemma small_number_four_octets:
  assumes "n < 256"
  shows "put_le_octets 4 n = [n,0,0,0]"
proof -
  have width: "(4::nat) = Suc 3" by simp
  have "put_le_octets 4 n = n # replicate 3 0"
    unfolding width by (rule small_number_one_octet_then_zeroes[OF assms])
  also have "... = [n,0,0,0]" by (simp add: numeral_eq_Suc)
  finally show ?thesis .
qed

end
