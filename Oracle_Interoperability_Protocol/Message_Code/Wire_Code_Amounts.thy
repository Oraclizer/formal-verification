theory Wire_Code_Amounts
  imports Wire_Code_Encoder "OIP_Product.Wire_Amounts"
begin

lemma source_fixed_word_concatenation_value:
  "get_le_octets (left @ right) =
    get_le_octets left + 256 ^ length left * get_le_octets right"
  by (induction left) (simp_all add: power_Suc algebra_simps)

lemma source_zero_octets_have_zero_value [simp]:
  "get_le_octets (replicate count 0) = 0"
  by (induction count) simp_all

lemma source_octet_value_is_within_its_width:
  assumes "wire_octets bytes"
  shows "get_le_octets bytes < 256 ^ length bytes"
  using assms
proof (induction bytes)
  case Nil
  then show ?case by simp
next
  case (Cons byte tail)
  have low: "byte < 256" and tail: "wire_octets tail"
    using Cons.prems by (simp_all add: wire_octets_def)
  have high: "get_le_octets tail < 256 ^ length tail"
    by (rule Cons.IH[OF tail])
  show ?case using low high by (simp add: power_Suc; arith)
qed

lemma source_fixed_width_splits_at_the_exact_high_quotient:
  "put_le_octets (low + high) number = put_le_octets low number @
    put_le_octets high (number div 256 ^ low)"
proof (induction low arbitrary: number)
  case 0
  then show ?case by simp
next
  case (Suc low)
  have quotient: "(number div 256) div 256 ^ low = number div 256 ^ Suc low"
  proof -
    have "(number div 256) div 256 ^ low = number div (256 * 256 ^ low)"
      by (rule div_mult2_eq[symmetric])
    also have "... = number div 256 ^ Suc low" by (simp add: power_Suc mult.commute)
    finally show ?thesis .
  qed
  show ?case by (simp add: Suc.IH quotient)
qed

lemma source_zero_high_amount_octets_preserve_the_full_model_value:
  assumes "take 24 bytes = replicate 24 0"
  shows "get_le_octets (rev bytes) = get_le_octets (rev (drop 24 bytes))"
proof -
  have split: "bytes = replicate 24 0 @ drop 24 bytes"
    using assms append_take_drop_id[of 24 bytes] by simp
  show ?thesis
    by (subst split) (simp add: source_fixed_word_concatenation_value)
qed

lemma source_zero_high_amount_octets_iff_model_value_fits_u64:
  assumes width: "length bytes = 32" and octets: "wire_octets bytes"
  shows "take 24 bytes = replicate 24 0 \<longleftrightarrow> get_le_octets (rev bytes) < 2^64"
proof
  assume zeros: "take 24 bytes = replicate 24 0"
  have tail_octets: "wire_octets (rev (drop 24 bytes))"
    using octets by (auto simp: wire_octets_def dest: in_set_dropD)
  have tail_width: "length (rev (drop 24 bytes)) = 8" using width by simp
  show "get_le_octets (rev bytes) < 2^64"
    using source_octet_value_is_within_its_width[OF tail_octets] tail_width
      source_zero_high_amount_octets_preserve_the_full_model_value[OF zeros]
    by simp
next
  assume bound: "get_le_octets (rev bytes) < 2^64"
  let ?number = "get_le_octets (rev bytes)"
  have reverse_octets: "wire_octets (rev bytes)" using octets by (simp add: wire_octets_def)
  have recovered: "put_le_octets 32 ?number = rev bytes"
    using octet_word_is_preserved_in_the_reconstructed_fixed_width_value[OF reverse_octets] width by simp
  have high_zero: "?number div 256^8 = 0"
    by (rule div_less) (use bound in simp)
  have split: "put_le_octets 32 ?number = put_le_octets 8 ?number @ replicate 24 0"
    using source_fixed_width_splits_at_the_exact_high_quotient[of 8 24 ?number] high_zero
    by (simp add: zero_le_octets_are_zero)
  have exact: "bytes = replicate 24 0 @ rev (put_le_octets 8 ?number)"
    using recovered split by (metis rev_append rev_replicate rev_rev_ident)
  have "take 24 bytes = take 24 (replicate 24 0 @ rev (put_le_octets 8 ?number))"
    by (rule arg_cong[OF exact])
  also have "... = replicate 24 0" by simp
  finally show "take 24 bytes = replicate 24 0" .
qed

definition code_product_amount where
  "code_product_amount bytes =
    (if length bytes \<noteq> 32 \<or> \<not> wire_octets bytes \<or> take 24 bytes \<noteq> replicate 24 0
     then None else Some (get_le_octets (rev (drop 24 bytes))))"

theorem the_source_amount_check_is_exactly_the_model_value_and_u64_limit:
  "code_product_amount bytes =
    (if length bytes = 32 \<and> wire_octets bytes \<and> get_le_octets (rev bytes) < 2^64
     then Some (get_le_octets (rev bytes)) else None)"
proof (cases "length bytes = 32 \<and> wire_octets bytes")
  case False
  then show ?thesis by (auto simp: code_product_amount_def)
next
  case True
  then have width: "length bytes = 32" and octets: "wire_octets bytes" by auto
  have criterion: "take 24 bytes = replicate 24 0 \<longleftrightarrow> get_le_octets (rev bytes) < 2^64"
    by (rule source_zero_high_amount_octets_iff_model_value_fits_u64[OF width octets])
  show ?thesis
  proof (cases "take 24 bytes = replicate 24 0")
    case True
    have exact: "get_le_octets (rev bytes) = get_le_octets (rev (drop 24 bytes))"
      by (rule source_zero_high_amount_octets_preserve_the_full_model_value[OF True])
    show ?thesis using width octets criterion True exact by (simp add: code_product_amount_def)
  next
    case False
    show ?thesis using width octets criterion False by (simp add: code_product_amount_def)
  qed
qed

lemma source_twenty_four_zero_octets:
  "replicate 24 (0::nat) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]"
  by (simp add: numeral_eq_Suc)

lemma a_source_amount_has_no_high_byte_truncation:
  "code_product_amount bytes = Some value \<Longrightarrow>
    length bytes = 32 \<and> value = get_le_octets (rev bytes) \<and> value < 2^64"
  by (simp add: the_source_amount_check_is_exactly_the_model_value_and_u64_limit split: if_splits)

end
