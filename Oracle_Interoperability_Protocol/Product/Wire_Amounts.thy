theory Wire_Amounts
  imports Wire_Ordinary_Operands
begin

lemma octet_word_is_preserved_in_the_reconstructed_fixed_width_value:
  assumes "wire_octets bytes"
  shows "put_le_octets (length bytes) (get_le_octets bytes) = bytes"
  using assms
proof (induction bytes)
  case Nil
  then show ?case by simp
next
  case (Cons byte tail)
  have high: "wire_octets tail" and low: "byte < 256"
    using Cons.prems by (simp_all add: wire_octets_def)
  have rem: "(byte + 256 * get_le_octets tail) mod 256 = byte"
    using low by (simp add: mult.commute)
  have div: "(byte + 256 * get_le_octets tail) div 256 = get_le_octets tail"
    using low by (simp add: mult.commute)
  show ?case using Cons.IH[OF high] low by (simp add: rem div)
qed

lemma exact_32_octet_unsigned_amount_has_no_accepted_alias:
  assumes "length left = 32" "length right = 32" "wire_octets left" "wire_octets right"
    "get_le_octets (rev left) = get_le_octets (rev right)"
  shows "left = right"
proof -
  have left_octets: "wire_octets (rev left)" and right_octets: "wire_octets (rev right)"
    using assms(3,4) by (simp_all add: wire_octets_def)
  have same: "rev left = rev right"
    using octet_word_is_preserved_in_the_reconstructed_fixed_width_value[OF left_octets]
      octet_word_is_preserved_in_the_reconstructed_fixed_width_value[OF right_octets] assms(1,2,5)
    by simp
  then show ?thesis by simp
qed

end
