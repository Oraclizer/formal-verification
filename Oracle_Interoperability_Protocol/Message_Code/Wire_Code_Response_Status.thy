theory Wire_Code_Response_Status
  imports Wire_Code_Admission "OIP_Reference_Profile.Reference_Response_Correlation"
begin

definition code_known_response_number where
  "code_known_response_number number \<longleftrightarrow>
    number \<in> reference_result_codes Recorded_Result True \<union>
      reference_result_codes Recorded_Result False \<union>
      reference_result_codes Delivery_Refusal False \<union>
      reference_result_codes Validation_Refusal False"

datatype code_response_status =
    Code_Known_Response reference_response_kind nat
  | Code_Unknown_Response reference_response_kind nat

definition code_decode_response_status where
  "code_decode_response_status kind number committed =
    (if code_known_response_number number then
       if number \<in> reference_result_codes kind committed
       then Some (Code_Known_Response kind number) else None
     else if kind \<noteq> Recorded_Result \<and> committed then None
     else Some (Code_Unknown_Response kind number))"

definition code_decode_raw_response_status where
  "code_decode_raw_response_status kind number committed =
    Option.bind (response_kind_at kind) (\<lambda>category. code_decode_response_status category number committed)"

lemma an_unknown_number_is_accepted_only_as_its_declared_category:
  assumes "\<not> code_known_response_number number"
  shows "code_decode_response_status kind number committed =
    (if kind = Recorded_Result \<or> \<not> committed then Some (Code_Unknown_Response kind number) else None)"
  using assms by (auto simp: code_decode_response_status_def)

lemma unknown_delivery_or_validation_statuses_cannot_carry_a_commit:
  assumes "\<not> code_known_response_number number" "kind \<noteq> Recorded_Result"
  shows "code_decode_response_status kind number True = None"
  using assms by (simp add: code_decode_response_status_def)

lemma a_known_status_keeps_the_existing_kind_and_commit_table:
  assumes "code_known_response_number number"
  shows "code_decode_response_status kind number committed = Some (Code_Known_Response kind number)
    \<longleftrightarrow> number \<in> reference_result_codes kind committed"
  using assms by (simp add: code_decode_response_status_def)

lemma a_noncategory_word_has_no_status_interpretation:
  assumes "kind \<notin> {1,2,3}"
  shows "code_decode_raw_response_status kind number committed = None"
  using assms by (auto simp: code_decode_raw_response_status_def response_kind_at_def)

definition code_response_call_shape where
  "code_response_call_shape family operation \<longleftrightarrow>
    (family = Wire_State_Sync \<and> operation \<in> {1..6}) \<or>
    (family = Wire_Regulatory \<and> operation \<in> {1..3}) \<or>
    (family = Wire_Lock \<and> operation \<in> {1..8})"

definition code_response_compatible where
  "code_response_compatible family operation kind number committed \<longleftrightarrow>
    (if code_known_response_number number
     then reference_response_compatible family operation kind number committed
     else code_response_call_shape family operation \<and> (kind = Recorded_Result \<or> \<not> committed))"

lemma every_old_compatible_result_is_a_known_number:
  "reference_response_compatible family operation kind number committed \<Longrightarrow>
    code_known_response_number number"
  by (cases kind; cases committed)
    (auto simp: reference_response_compatible_def code_known_response_number_def reference_result_codes_def)

lemma the_extended_receiver_preserves_the_complete_old_compatibility_relation:
  "reference_response_compatible family operation kind number committed \<Longrightarrow>
    code_response_compatible family operation kind number committed"
  using every_old_compatible_result_is_a_known_number
  by (simp add: code_response_compatible_def)

lemma a_known_number_has_exactly_the_old_compatibility_relation:
  "code_known_response_number number \<Longrightarrow>
    code_response_compatible family operation kind number committed =
      reference_response_compatible family operation kind number committed"
  by (simp add: code_response_compatible_def)

definition code_correlate_reference_response where
  "code_correlate_reference_response original packet =
    (let core = packet_core packet; body = wire_operation_body core in
     case response_result_words (wire_words body) of None \<Rightarrow> None
      | Some (call_id,kind,number,position) \<Rightarrow>
        if wire_message_family core = Wire_Ack \<and>
          body = reference_response_body call_id kind number position original \<and>
          reference_response_header_matches core original call_id \<and>
          reference_response_position_matches original kind position \<and>
          code_response_compatible (wire_message_family original) (wire_opcode (wire_operation_body original))
            kind number (position \<noteq> None)
        then Some (call_id,kind,number,position) else None)"

theorem every_existing_native_response_correlation_survives_the_status_extension:
  assumes "correlate_reference_response original packet = Some result"
  shows "code_correlate_reference_response original packet = Some result"
proof -
  obtain call_id kind number position where result: "result = (call_id,kind,number,position)"
    by (cases result rule: prod_cases4) auto
  have parts: "response_result_words (wire_words (wire_operation_body (packet_core packet))) = Some (call_id,kind,number,position) \<and>
      wire_message_family (packet_core packet) = Wire_Ack \<and>
      wire_operation_body (packet_core packet) = reference_response_body call_id kind number position original \<and>
      reference_response_header_matches (packet_core packet) original call_id \<and>
      reference_response_position_matches original kind position \<and>
      reference_response_compatible (wire_message_family original) (wire_opcode (wire_operation_body original)) kind number (position \<noteq> None)"
    using assms result by (auto simp: correlate_reference_response_def Let_def
      split: option.splits prod.splits if_splits)
  have compatible: "reference_response_compatible (wire_message_family original)
      (wire_opcode (wire_operation_body original)) kind number (position \<noteq> None)"
    using parts by simp
  have extended: "code_response_compatible (wire_message_family original)
      (wire_opcode (wire_operation_body original)) kind number (position \<noteq> None)"
    by (rule the_extended_receiver_preserves_the_complete_old_compatibility_relation[OF compatible])
  show ?thesis using parts extended result
    by (simp add: code_correlate_reference_response_def Let_def
      the_reference_response_words_recover_the_typed_result)
qed

theorem the_status_extension_keeps_the_exact_original_header_and_commit_binding:
  assumes "code_correlate_reference_response original packet = Some (call_id,kind,number,position)"
  shows "wire_blobs (wire_operation_body (packet_core packet)) = [encode_wire_core original]"
    "reference_response_header_matches (packet_core packet) original call_id"
    "reference_response_position_matches original kind position"
    "position \<noteq> None \<longrightarrow> kind = Recorded_Result"
proof -
  have parts: "wire_operation_body (packet_core packet) = reference_response_body call_id kind number position original \<and>
      reference_response_header_matches (packet_core packet) original call_id \<and>
      reference_response_position_matches original kind position"
    using assms by (auto simp: code_correlate_reference_response_def Let_def
      split: option.splits prod.splits if_splits)
  have body: "wire_operation_body (packet_core packet) = reference_response_body call_id kind number position original"
    using parts by simp
  show "wire_blobs (wire_operation_body (packet_core packet)) = [encode_wire_core original]"
    by (simp add: body reference_response_body_def)
  show "reference_response_header_matches (packet_core packet) original call_id" using parts by simp
  show "reference_response_position_matches original kind position" using parts by simp
  have position: "reference_response_position_matches original kind position" using parts by simp
  have "position = None \<or> kind = Recorded_Result"
    using position unfolding reference_response_position_matches_def by (rule conjunct1)
  then show "position \<noteq> None \<longrightarrow> kind = Recorded_Result" by auto
qed

definition code_response_words where
  "code_response_words call_id kind number position =
    (if number \<in> reference_result_codes kind (position \<noteq> None)
     then Some ([fst call_id,snd call_id,reference_response_kind_number kind,number] @
        (case position of None \<Rightarrow> [0] | Some revision \<Rightarrow> [1,revision]))
     else None)"

lemma source_response_words_have_the_existing_model_word_sequence:
  assumes "code_response_words call_id kind number position = Some words"
  shows "words = wire_words (reference_response_body call_id kind number position original)"
    "length words \<le> 6"
proof -
  have exact: "words = [fst call_id,snd call_id,reference_response_kind_number kind,number] @
      (case position of None \<Rightarrow> [0] | Some revision \<Rightarrow> [1,revision])"
    using assms by (auto simp: code_response_words_def split: if_splits)
  show "words = wire_words (reference_response_body call_id kind number position original)"
    by (simp add: exact reference_response_body_def)
  show "length words \<le> 6" using exact by (cases position) simp_all
qed

lemma source_response_generation_cannot_emit_an_unknown_result_code:
  "\<not> code_known_response_number number \<Longrightarrow>
    code_response_words call_id kind number position = None"
  by (cases kind; cases "position \<noteq> None")
    (auto simp: code_response_words_def code_known_response_number_def reference_result_codes_def)

end
