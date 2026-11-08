theory Reference_Response_Codes
  imports Reference_Response_Model
begin

definition reference_result_codes where
  "reference_result_codes kind committed = (case kind of
     Recorded_Result \<Rightarrow> if committed then {10..28} else {1..4} \<union> {30..38}
   | Delivery_Refusal \<Rightarrow> if committed then {} else {50..56}
   | Validation_Refusal \<Rightarrow> if committed then {} else {70..77})"

definition reference_result_targets :: "nat \<Rightarrow> (wire_family \<times> nat) set" where
  "reference_result_targets code =
    (if code = 10 then {(Wire_Lock,1)}
     else if code = 11 then {(Wire_Lock,2)}
     else if code \<in> {4,12} then {(Wire_State_Sync,1)}
     else if code = 13 then {(Wire_Lock,3),(Wire_Lock,4)}
     else if code = 14 then {(Wire_Lock,5)}
     else if code = 15 then {(Wire_Lock,8)}
     else if code \<in> {16,21,23} then {(Wire_State_Sync,2)}
     else if code \<in> {17,24} then {(Wire_State_Sync,3)}
     else if code = 18 then {(Wire_Lock,6)}
     else if code \<in> {19,25} then {(Wire_State_Sync,4)}
     else if code = 20 then {(Wire_Lock,7)}
     else if code = 22 then {(Wire_State_Sync,5)}
     else if code = 26 then {(Wire_Regulatory,1)}
     else if code = 27 then {(Wire_Regulatory,2)}
     else if code = 28 then {(Wire_State_Sync,6),(Wire_Regulatory,3)}
     else if code \<in> {30..38} then {(Wire_Regulatory,1),(Wire_Regulatory,2)}
     else {})"

definition reference_response_compatible where
  "reference_response_compatible family opcode kind code committed \<longleftrightarrow>
    code \<in> reference_result_codes kind committed \<and>
    ((family, opcode) \<in> reference_result_targets code \<or>
     ((kind \<noteq> Recorded_Result \<or> code \<in> {1,2,3}) \<and>
       ((family = Wire_State_Sync \<and> opcode \<in> {1..6}) \<or>
        (family = Wire_Regulatory \<and> opcode \<in> {1..3}) \<or>
        (family = Wire_Lock \<and> opcode \<in> {1..8}))))"

definition encode_guarded_reference_response where
  "encode_guarded_reference_response outer original call_id kind code position signature =
    (if reference_response_compatible (wire_message_family original) (wire_opcode (wire_operation_body original))
          kind code (position \<noteq> None)
     then encode_reference_response outer original call_id kind code position signature else None)"

lemma reference_debit_accepts_its_committed_result_and_original_rejection:
  "reference_response_compatible Wire_State_Sync 1 Recorded_Result 12 True"
  "reference_response_compatible Wire_State_Sync 1 Recorded_Result 4 False"
  "\<not> reference_response_compatible Wire_State_Sync 1 Recorded_Result 12 False"
  "\<not> reference_response_compatible Wire_State_Sync 2 Recorded_Result 12 True"
  by (simp_all add: reference_response_compatible_def reference_result_codes_def reference_result_targets_def)

lemma a_recorded_result_with_a_commit_requires_the_compatible_product_operation:
  assumes "reference_response_compatible family opcode Recorded_Result code True"
  shows "(family, opcode) \<in> reference_result_targets code"
  using assms by (auto simp: reference_response_compatible_def reference_result_codes_def)

lemma a_delivery_or_validation_refusal_cannot_carry_a_commit:
  assumes "reference_response_compatible family opcode kind code True"
  shows "kind = Recorded_Result"
  using assms by (cases kind) (simp_all add: reference_response_compatible_def reference_result_codes_def)

theorem an_encoded_reference_result_has_the_exact_original_and_a_compatible_code:
  assumes encoded: "encode_guarded_reference_response outer original call_id kind code position signature = Some bytes"
  obtains packet where "decode_wire_packet bytes = Some packet"
    "encode_wire_packet packet = bytes"
    "wire_blobs (wire_operation_body (packet_core packet)) = [encode_wire_core original]"
    "reference_response_compatible (wire_message_family original) (wire_opcode (wire_operation_body original))
      kind code (position \<noteq> None)"
proof -
  have compatible: "reference_response_compatible (wire_message_family original) (wire_opcode (wire_operation_body original))
    kind code (position \<noteq> None)"
    and raw: "encode_reference_response outer original call_id kind code position signature = Some bytes"
    using encoded by (auto simp: encode_guarded_reference_response_def split: if_splits)
  obtain packet where decoded: "decode_wire_packet bytes = Some packet"
    and exact: "encode_wire_packet packet = bytes"
    and bound: "wire_blobs (wire_operation_body (packet_core packet)) = [encode_wire_core original]"
    using outbound_reference_bytes_decode_to_the_exact_bound_response[OF raw] by blast
  show thesis by (rule that[OF decoded exact bound compatible])
qed

lemma an_incompatible_response_code_cannot_be_serialized_by_the_product:
  assumes "\<not> reference_response_compatible (wire_message_family original) (wire_opcode (wire_operation_body original))
    kind code (position \<noteq> None)"
  shows "encode_guarded_reference_response outer original call_id kind code position signature = None"
  using assms by (simp add: encode_guarded_reference_response_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms reference_debit_accepts_its_committed_result_and_original_rejection
      a_recorded_result_with_a_commit_requires_the_compatible_product_operation
      a_delivery_or_validation_refusal_cannot_carry_a_commit
      an_encoded_reference_result_has_the_exact_original_and_a_compatible_code
      an_incompatible_response_code_cannot_be_serialized_by_the_product})
  then () else error "Unexpected oracle in reference response code correspondence"
\<close>

end
