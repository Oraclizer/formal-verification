theory Wire_Code_Typed_Decode
  imports Wire_Code_Typed_Metadata_Values
begin

fun code_typed_operand_ir :: "nat \<Rightarrow> wire_core \<Rightarrow> nat list option" where
  "code_typed_operand_ir 0 oip_binder_core = None"
| "code_typed_operand_ir (Suc oip_binder_fuel) oip_binder_core =
    (case code_decode_operand_tree (Suc oip_binder_fuel) oip_binder_core of
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
                   code_ir_bytes (encode_wire_core oip_binder_original),oip_binder_typed]) (code_typed_operand_ir oip_binder_fuel oip_binder_original))
              | _ \<Rightarrow> None)
           else map_option code_ir_parsed_query (code_decode_query_nonreceipt oip_binder_core))
        else if oip_binder_family = Wire_Ack then
          (if oip_binder_operation = 2 then
             (case wire_blobs oip_binder_body of [oip_binder_raw] \<Rightarrow>
               Option.bind (decode_wire_core oip_binder_raw) (\<lambda>oip_binder_original.
                 Option.bind (code_typed_operand_ir oip_binder_fuel oip_binder_original) (\<lambda>oip_binder_typed.
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
        else None))"

lemma a_typed_observation_cannot_bypass_a_refused_existing_decoder:
  assumes "code_decode_operand_tree oip_binder_depth oip_binder_core = Code_Tree_Refused oip_binder_reason"
  shows "code_typed_operand_ir oip_binder_depth oip_binder_core = None"
  using assms by (cases oip_binder_depth) simp_all

lemma an_accepted_ordinary_observation_reuses_the_actual_ordinary_decoder:
  assumes ready: "code_decode_operand_tree (Suc oip_binder_fuel) oip_binder_core = Code_Tree_Ready oip_binder_classified"
    and oip_binder_family: "wire_message_family oip_binder_core = Wire_Lock"
  shows "code_typed_operand_ir (Suc oip_binder_fuel) oip_binder_core = code_typed_ordinary_ir oip_binder_core"
  using ready oip_binder_family by simp

lemma an_accepted_legal_observation_reuses_the_actual_legal_decoder:
  assumes ready: "code_decode_operand_tree (Suc oip_binder_fuel) oip_binder_core = Code_Tree_Ready oip_binder_classified"
    and oip_binder_family: "wire_message_family oip_binder_core = Wire_Regulatory"
    and oip_binder_operation: "wire_opcode (wire_operation_body oip_binder_core) \<noteq> 3"
  shows "code_typed_operand_ir (Suc oip_binder_fuel) oip_binder_core = code_typed_legal_ir oip_binder_core"
  using ready oip_binder_family oip_binder_operation by simp

lemma an_accepted_nonreceipt_read_observation_reuses_the_actual_query_decoder:
  assumes ready: "code_decode_operand_tree (Suc oip_binder_fuel) oip_binder_core = Code_Tree_Ready oip_binder_classified"
    and oip_binder_family: "wire_message_family oip_binder_core = Wire_Query"
    and oip_binder_operation: "wire_opcode (wire_operation_body oip_binder_core) \<noteq> 8"
  shows "code_typed_operand_ir (Suc oip_binder_fuel) oip_binder_core =
    map_option code_ir_parsed_query (code_decode_query_nonreceipt oip_binder_core)"
  using ready oip_binder_family oip_binder_operation by simp

lemma an_accepted_ack_observation_reuses_the_actual_native_ack_decoder:
  assumes ready: "code_decode_operand_tree (Suc oip_binder_fuel) oip_binder_core = Code_Tree_Ready oip_binder_classified"
    and oip_binder_family: "wire_message_family oip_binder_core = Wire_Ack"
    and oip_binder_operation: "wire_opcode (wire_operation_body oip_binder_core) \<noteq> 2"
  shows "code_typed_operand_ir (Suc oip_binder_fuel) oip_binder_core =
    map_option code_ir_ack (parse_native_scheduled_ack oip_binder_core)"
  using ready oip_binder_family oip_binder_operation
  by (simp add: the_source_settlement_ack_parser_has_the_existing_exact_product_value)

text \<open>
  code_decode_operand_tree retains the pre-existing acceptance/refusal and
  recursive error ordering. Each successful branch then consumes its rich
  typed decoder, rather than its Code_Nested_Other/Response classification.
  Recursive original bytes come from reencoding a decoded Core and are
  accompanied by the recursively computed typed summary. Native tail words
  are never the output. A missing typed result is explicit None, never true.
\<close>

end
