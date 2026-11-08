theory Wire_Code_Typed_Summary_Codegen
  imports Wire_Code_Typed_Summary_ABI
begin

declare [[code drop: code_typed_operand_ir]]

lemma code_typed_operand_ir_integer_code [code]:
  "code_typed_operand_ir oip_binder_depth oip_binder_core =
    (if oip_binder_depth = 0 then None else (case code_decode_operand_tree oip_binder_depth oip_binder_core of
       Code_Tree_Refused oip_binder_reason \<Rightarrow> None | Code_Tree_Pending \<Rightarrow> None
     | Code_Tree_Ready oip_binder_classified \<Rightarrow>
       (let oip_binder_body = wire_operation_body oip_binder_core; oip_binder_family = wire_message_family oip_binder_core; oip_binder_operation = wire_opcode oip_binder_body in
        if (oip_binder_family = Wire_State_Sync \<and> oip_binder_operation = 6) \<or> (oip_binder_family = Wire_Regulatory \<and> oip_binder_operation = 3)
        then code_typed_spend_ir oip_binder_core
        else if oip_binder_family \<in> {Wire_State_Sync,Wire_Lock} then code_typed_ordinary_ir oip_binder_core
        else if oip_binder_family = Wire_Regulatory then code_typed_legal_ir oip_binder_core
        else if oip_binder_family = Wire_Query then
          (if oip_binder_operation = 8 then
             (case (wire_words oip_binder_body,wire_blobs oip_binder_body) of ([oip_binder_session],[oip_binder_raw]) \<Rightarrow>
               Option.bind (decode_wire_core oip_binder_raw) (\<lambda>oip_binder_original.
                 map_option (\<lambda>oip_binder_typed. code_ir_node 15 [code_ir_scalar oip_binder_session,
                   code_ir_bytes (encode_wire_core oip_binder_original),oip_binder_typed]) (code_typed_operand_ir (oip_binder_depth - 1) oip_binder_original))
              | _ \<Rightarrow> None)
           else map_option code_ir_parsed_query (code_decode_query_nonreceipt oip_binder_core))
        else if oip_binder_family = Wire_Ack then
          (if oip_binder_operation = 2 then
             (case wire_blobs oip_binder_body of [oip_binder_raw] \<Rightarrow>
               Option.bind (decode_wire_core oip_binder_raw) (\<lambda>oip_binder_original.
                 Option.bind (code_typed_operand_ir (oip_binder_depth - 1) oip_binder_original) (\<lambda>oip_binder_typed.
                   map_option (\<lambda>(oip_binder_call_id,oip_binder_kind,oip_binder_number,oip_binder_position).
                     code_ir_node 16 [code_ir_pair oip_binder_call_id,
                       code_ir_scalar (case oip_binder_kind of Recorded_Result \<Rightarrow> 1 | Delivery_Refusal \<Rightarrow> 2 | Validation_Refusal \<Rightarrow> 3),
                       code_ir_scalar oip_binder_number,code_ir_option code_ir_scalar oip_binder_position,
                       code_ir_bytes (encode_wire_core oip_binder_original),oip_binder_typed])
                     (response_result_words (wire_words oip_binder_body))))
              | _ \<Rightarrow> None)
           else map_option code_ir_ack (code_decode_settlement_ack oip_binder_core))
        else if oip_binder_family = Wire_Heartbeat then
          Option.bind (code_decode_heartbeat oip_binder_core) (code_ir_heartbeat oip_binder_core)
        else if oip_binder_family = Wire_Governance then map_option code_ir_governance (code_decode_governance oip_binder_core)
        else None)))"
proof (cases oip_binder_depth)
  case 0
  then show ?thesis by simp
next
  case (Suc oip_codegen_predecessor)
  show ?thesis
    unfolding Suc diff_Suc_1
    by (simp only: code_typed_operand_ir.simps Suc_not_Zero if_False)
qed

text \<open>
  Only the new helper receives a variable-only nat code equation. Its
  equality to the logical recursion is proved from the original helper
  equations. No old datatype, decoder, code equation or carrier is changed.
\<close>

end
