theory Wire_Code_Varint_Read
  imports Wire_Code_Encoder
begin

text \<open>
  The source loop runs at most ten iterations.  Clearing the continuation
  bit is represented by subtracting 128 from a continued octet.  The ninth
  zero-based iteration may carry only the final u64 bit, and a zero final
  octet after an earlier octet is a non-shortest encoding.
\<close>

fun code_take_varint_from ::
  "nat \<Rightarrow> nat \<Rightarrow> wire_bytes \<Rightarrow> (nat \<times> wire_bytes) option" where
  "code_take_varint_from 0 index input = None"
| "code_take_varint_from (Suc fuel) index [] = None"
| "code_take_varint_from (Suc fuel) index (byte # tail) =
    (if byte \<ge> 256 \<or> (index = 9 \<and> byte > 1) then None
     else if byte < 128 then
       (if index > 0 \<and> byte = 0 then None else Some (byte,tail))
     else map_option (\<lambda>(number,rest). (byte - 128 + 128 * number,rest))
       (code_take_varint_from fuel (Suc index) tail))"

definition code_take_varint where
  "code_take_varint bytes = code_take_varint_from 10 0 bytes"

lemma the_bounded_source_varint_reader_preserves_the_model_value:
  assumes "code_take_varint_from fuel index bytes = Some (number,rest)"
  shows "take_wire_varint bytes = Some (number,rest)"
  using assms
proof (induction fuel arbitrary: index bytes number rest)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases bytes)
    case Nil
    then show ?thesis using Suc.prems by simp
  next
    case (Cons byte tail)
    have bound: "byte < 256"
      using Suc.prems Cons by (auto split: if_splits)
    show ?thesis
    proof (cases "byte < 128")
      case True
      then show ?thesis using Suc.prems Cons bound by (auto split: if_splits)
    next
      case False
      obtain high where sub: "code_take_varint_from fuel (Suc index) tail = Some (high,rest)"
        and value_eq: "number = byte - 128 + 128 * high"
        using Suc.prems Cons False bound
        by (cases "code_take_varint_from fuel (Suc index) tail")
          (auto split: prod.splits if_splits)
      have model: "take_wire_varint tail = Some (high,rest)"
        by (rule Suc.IH[OF sub])
      show ?thesis using Cons False bound model value_eq by simp
    qed
  qed
qed

lemma the_source_varint_reader_preserves_the_model_value:
  "code_take_varint bytes = Some result \<Longrightarrow> take_wire_varint bytes = Some result"
  using the_bounded_source_varint_reader_preserves_the_model_value
  by (cases result) (auto simp: code_take_varint_def)

lemma the_bounded_reader_accepts_every_canonical_remaining_u64_prefix:
  assumes position: "index + fuel = 10"
    and bound: "number < 2^(64 - 7 * index)"
    and positive: "index = 0 \<or> number > 0"
  shows "code_take_varint_from fuel index (put_wire_varint number @ tail) = Some (number,tail)"
  using position bound positive
proof (induction fuel arbitrary: index number tail)
  case 0
  then show ?case by auto
next
  case (Suc fuel)
  have index_le: "index \<le> 9" using Suc.prems(1) by arith
  show ?case
  proof (cases "number < 128")
    case True
    have last: "index = 9 \<Longrightarrow> number \<le> 1"
    proof -
      assume "index = 9"
      with Suc.prems(2) have "number < 2" by simp
      then show "number \<le> 1" by arith
    qed
    have nonzero: "index > 0 \<Longrightarrow> number \<noteq> 0"
      using Suc.prems(3) by auto
    show ?thesis using True last nonzero
      by (auto simp: put_wire_varint.simps[of number])
  next
    case False
    have earlier: "index \<le> 8"
    proof (rule ccontr)
      assume "\<not> index \<le> 8"
      with index_le have "index = 9" by arith
      with Suc.prems(2) False show False by (simp; arith)
    qed
    have exponent: "64 - 7 * index = (64 - 7 * Suc index) + 7"
      using earlier by arith
    have power: "2^(64 - 7 * index) = 2^(64 - 7 * Suc index) * (128::nat)"
      by (subst exponent) (simp add: power_add)
    have quotient_bound: "number div 128 < 2^(64 - 7 * Suc index)"
      using Suc.prems(2) power
      by (simp add: div_less_iff_less_mult)
    have monotone: "128 div 128 \<le> number div 128"
      by (rule div_le_mono) (use False in arith)
    have quotient_positive: "number div 128 > 0" using monotone by simp
    have next_position: "Suc index + fuel = 10" using Suc.prems(1) by arith
    have read_tail: "code_take_varint_from fuel (Suc index) (put_wire_varint (number div 128) @ tail) =
        Some (number div 128,tail)"
      by (rule Suc.IH[OF next_position quotient_bound]) (use quotient_positive in simp)
    have reconstruct: "number mod 128 + 128 * (number div 128) = number"
      using div_mult_mod_eq[of number 128]
      by (simp add: mult.commute add.commute)
    have not_last: "index \<noteq> 9" using earlier by arith
    have octet: "128 + number mod 128 < 256" by simp
    show ?thesis using False not_last octet read_tail reconstruct
      by (simp add: put_wire_varint.simps[of number])
  qed
qed

theorem the_source_reader_accepts_every_canonical_u64_prefix:
  assumes "number < 2^64"
  shows "code_take_varint (put_wire_varint number @ tail) = Some (number,tail)"
  unfolding code_take_varint_def
  by (rule the_bounded_reader_accepts_every_canonical_remaining_u64_prefix)
    (use assms in simp_all)

lemma the_source_reader_refuses_a_nonshortest_zero_suffix:
  "code_take_varint [128,0] = None"
  "take_wire_varint [128,0] = Some (0,[])"
  by code_simp+

lemma the_source_reader_refuses_an_overflowing_tenth_octet:
  "code_take_varint (replicate 9 128 @ [2]) = None"
  by code_simp

end
