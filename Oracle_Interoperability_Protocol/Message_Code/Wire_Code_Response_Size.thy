theory Wire_Code_Response_Size
  imports Wire_Code_Response_Status
begin

lemma code_short_varint_length:
  "number < 128 \<Longrightarrow> length (put_wire_varint number) = 1"
  by (simp add: put_wire_varint.simps[of number])

lemma code_two_octet_varint_length:
  assumes "128 \<le> number" "number < 128^2"
  shows "length (put_wire_varint number) = 2"
proof -
  have quotient: "number div 128 < 128"
    using assms(2) by (simp add: div_less_iff_less_mult power2_eq_square)
  show ?thesis using assms(1) quotient
    by (simp add: put_wire_varint.simps[of number] code_short_varint_length)
qed

lemma code_varint_length_is_monotone:
  assumes "smaller \<le> larger"
  shows "length (put_wire_varint smaller) \<le> length (put_wire_varint larger)"
  using assms
proof (induction larger arbitrary: smaller rule: less_induct)
  case (less larger)
  show ?case
  proof (cases "larger < 128")
    case True
    have "smaller < 128" using less.prems True by arith
    then show ?thesis using True by (simp add: code_short_varint_length)
  next
    case large: False
    show ?thesis
    proof (cases "smaller < 128")
      case True
      have at_least_one: "1 \<le> length (put_wire_varint larger)"
        using wire_varint_never_empty[of larger]
        by (cases "put_wire_varint larger") simp_all
      have one: "length (put_wire_varint smaller) = 1"
        by (rule code_short_varint_length[OF True])
      show ?thesis unfolding one by (rule at_least_one)
    next
      case small: False
      have decrease: "larger div 128 < larger"
        by (rule a_continued_varint_division_decreases[OF large])
      have quotient: "smaller div 128 \<le> larger div 128"
        by (rule div_le_mono[OF less.prems])
      have tail: "length (put_wire_varint (smaller div 128)) \<le>
          length (put_wire_varint (larger div 128))"
        by (rule less.IH[OF decrease quotient])
      show ?thesis using large small tail
        by (simp add: put_wire_varint.simps[of smaller] put_wire_varint.simps[of larger])
    qed
  qed
qed

lemma code_fixed_response_words_have_value_independent_width:
  "length (concat (map (code_field_fixed64 2) words)) = 9 * length words"
  by (induction words)
    (simp_all add: code_field_fixed64_def appending_varint_bytes_is_the_canonical_numeric_encoding
      code_short_varint_length)

definition code_response_body_bytes where
  "code_response_body_bytes words original =
    code_field_varint 1 2 @ concat (map (code_field_fixed64 2) words) @ code_field_bytes 3 original"

definition code_response_body_length where
  "code_response_body_length count original_length =
    3 + 9 * count + length (put_wire_varint original_length) + original_length"

lemma the_source_response_body_length_depends_only_on_word_count_and_original_length:
  "length (code_response_body_bytes words original) =
    code_response_body_length (length words) (length original)"
  by (simp add: code_response_body_bytes_def code_response_body_length_def
    code_field_varint_def code_field_bytes_def appending_varint_bytes_is_the_canonical_numeric_encoding
    code_short_varint_length code_fixed_response_words_have_value_independent_width)

definition code_response_core where
  "code_response_core outer atomicity words original =
    outer\<lparr>wire_version := 6,wire_purpose := 1,wire_message_family := Wire_Ack,
      wire_primary_code := 1,wire_secondary_code := None,wire_signature_scheme := 1,
      wire_atomicity := atomicity,wire_priority := 3,
      wire_operation_body := \<lparr>wire_opcode = 2,wire_words = words,wire_blobs = [original],
        wire_deadline = Deadline_Absent\<rparr>\<rparr>"

definition code_response_core_length where
  "code_response_core_length count original_length =
    (let body = code_response_body_length count original_length
     in 118 + length (put_wire_varint body) + body)"

lemma source_response_body_is_the_actual_operation_body:
  "code_body_bytes (wire_operation_body (code_response_core outer atomicity words original)) =
    code_response_body_bytes words original"
  by (simp add: code_response_core_def code_body_bytes_def code_response_body_bytes_def)

lemma source_fixed_response_header_has_constant_width:
  assumes uuid: "length (wire_uuid outer) = 16" and atomicity: "atomicity < 128"
  shows "length (code_core_bytes (code_response_core outer atomicity words original)) =
    code_response_core_length (length words) (length original)"
proof -
  have argument: "Suc (Suc (Suc (9 * length words +
      (length (put_wire_varint (length original)) + length original)))) =
    3 + 9 * length words + length (put_wire_varint (length original)) + length original"
    by arith
  show ?thesis using uuid atomicity
    apply (simp add: code_core_bytes_def code_response_core_def
      code_response_core_length_def code_response_body_length_def code_body_bytes_def
      code_field_varint_def code_field_fixed64_def code_field_bytes_def
      appending_varint_bytes_is_the_canonical_numeric_encoding
      code_short_varint_length code_two_octet_varint_length
      code_fixed_response_words_have_value_independent_width Let_def)
    apply (rule arg_cong[where f="\<lambda>number. length (put_wire_varint number)"])
    apply (rule argument)
    done
qed

definition code_response_packet_bytes where
  "code_response_packet_bytes outer atomicity words original signature =
    code_field_bytes 1 (code_core_bytes (code_response_core outer atomicity words original)) @
    code_field_bytes 2 signature"

definition code_response_packet_length where
  "code_response_packet_length count original_length =
    (let core = code_response_core_length count original_length
     in 67 + length (put_wire_varint core) + core)"

lemma the_source_response_packet_length_ignores_fixed_field_values:
  assumes "length (wire_uuid outer) = 16" "atomicity < 128" "length signature = 64"
  shows "length (code_response_packet_bytes outer atomicity words original signature) =
    code_response_packet_length (length words) (length original)"
  using assms source_fixed_response_header_has_constant_width[OF assms(1,2), of words original]
  by (simp add: code_response_packet_bytes_def code_response_packet_length_def
    code_field_bytes_def appending_varint_bytes_is_the_canonical_numeric_encoding code_short_varint_length Let_def)

lemma the_source_response_length_is_monotone_in_its_word_count:
  assumes "smaller \<le> larger"
  shows "code_response_packet_length smaller original_length \<le>
    code_response_packet_length larger original_length"
proof -
  have body: "code_response_body_length smaller original_length \<le>
      code_response_body_length larger original_length"
    using assms by (simp add: code_response_body_length_def)
  have body_prefix: "length (put_wire_varint (code_response_body_length smaller original_length)) \<le>
      length (put_wire_varint (code_response_body_length larger original_length))"
    by (rule code_varint_length_is_monotone[OF body])
  have core: "code_response_core_length smaller original_length \<le>
      code_response_core_length larger original_length"
    using body body_prefix by (simp add: code_response_core_length_def Let_def)
  have core_prefix: "length (put_wire_varint (code_response_core_length smaller original_length)) \<le>
      length (put_wire_varint (code_response_core_length larger original_length))"
    by (rule code_varint_length_is_monotone[OF core])
  show ?thesis using core core_prefix by (simp add: code_response_packet_length_def Let_def)
qed

theorem measuring_six_response_words_bounds_every_valid_source_response:
  assumes uuid: "length (wire_uuid outer) = 16" and atomicity: "atomicity < 128"
    and signature: "length signature = 64"
    and words: "code_response_words call_id kind number position = Some actual_words"
  shows "length (code_response_packet_bytes outer atomicity actual_words original signature) \<le>
    code_response_packet_length 6 (length original)"
proof -
  have count: "length actual_words \<le> 6"
    by (rule source_response_words_have_the_existing_model_word_sequence(2)[OF words])
  show ?thesis
    using the_source_response_packet_length_ignores_fixed_field_values[OF uuid atomicity signature,
      of actual_words original]
      the_source_response_length_is_monotone_in_its_word_count[OF count, of "length original"]
    by simp
qed

lemma the_six_word_placeholder_measures_the_bound_exactly:
  assumes "length (wire_uuid outer) = 16" "atomicity < 128" "length signature = 64"
  shows "length (code_response_packet_bytes outer atomicity (replicate 6 0) original signature) =
    code_response_packet_length 6 (length original)"
  using the_source_response_packet_length_ignores_fixed_field_values[OF assms, of "replicate 6 0" original]
  by simp

end
