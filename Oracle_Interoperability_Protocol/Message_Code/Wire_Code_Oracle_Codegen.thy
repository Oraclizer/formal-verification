theory Wire_Code_Oracle_Codegen
  imports Wire_Code_Oracle_Contract "HOL-Library.Code_Target_Nat"
begin

text \<open>
  Code_Target_Nat represents nat by target integers. Only generated code
  equations are replaced here; all original logical definitions and simp
  theorems remain intact. Every replacement has a variable-only nat LHS
  and is proved from the original equations in the kernel.
\<close>

declare [[code drop: code_take_varint_from]]

lemma code_take_varint_from_integer_code [code]:
  "code_take_varint_from fuel index input =
    (if fuel = 0 then None else
      case input of [] \<Rightarrow> None | byte # tail \<Rightarrow>
        if byte \<ge> 256 \<or> (index = 9 \<and> byte > 1) then None
        else if byte < 128 then
          (if index > 0 \<and> byte = 0 then None else Some (byte,tail))
        else map_option (\<lambda>(number,rest). (byte - 128 + 128 * number,rest))
          (code_take_varint_from (fuel - 1) (index + 1) tail))"
  by (cases fuel; cases input) simp_all

declare [[code drop: code_json_elements]]

lemma code_json_elements_integer_code [code]:
  "code_json_elements fuel parse bytes =
    (if fuel = 0 then None else
      case parse bytes of None \<Rightarrow> None | Some (parsed_item,tail) \<Rightarrow>
        (case tail of [] \<Rightarrow> None | separator # rest \<Rightarrow>
          if separator = 93 then Some ([parsed_item],rest)
          else if separator = 44 then
            map_option (\<lambda>(values,ending). (parsed_item # values,ending))
              (code_json_elements (fuel - 1) parse rest)
          else None))"
proof (cases fuel)
  case 0
  then show ?thesis by simp
next
  case (Suc predecessor)
  show ?thesis unfolding Suc diff_Suc_1 by simp
qed

declare [[code drop: code_decode_operand_tree]]

lemma code_decode_operand_tree_integer_code [code]:
  "code_decode_operand_tree fuel core =
    (if fuel = 0 then Code_Tree_Refused Invalid_Wire_Format else
    (let body = wire_operation_body core; family = wire_message_family core; operation = wire_opcode body in
     if (family = Wire_State_Sync \<and> operation = 6) \<or> (family = Wire_Regulatory \<and> operation = 3)
     then code_spend_tree core
     else if family \<in> {Wire_State_Sync,Wire_Lock} then code_ordinary_tree core
     else if family = Wire_Regulatory then code_legal_tree core
     else if family = Wire_Query then
       (if operation = 8 then
         (case (wire_words body,wire_blobs body) of ([session],[original_bytes]) \<Rightarrow>
           if wire_deadline body \<noteq> Deadline_Absent \<or> (fuel - 1) = 0 then Code_Tree_Refused Invalid_Wire_Format
           else (case decode_wire_core original_bytes of None \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format
             | Some original \<Rightarrow> code_receipt_tree_finish original (code_decode_operand_tree (fuel - 1) original))
          | _ \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format)
        else case code_decode_query_nonreceipt core of None \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format
          | Some query \<Rightarrow> Code_Tree_Ready Code_Nested_Other)
     else if family = Wire_Ack then
       (if operation = 2 then
         (if wire_deadline body \<noteq> Deadline_Absent then Code_Tree_Refused Invalid_Wire_Format
          else case wire_blobs body of [original_bytes] \<Rightarrow>
            (case decode_wire_core original_bytes of None \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format
             | Some original \<Rightarrow> code_response_tree_after_nested core original (code_decode_operand_tree (fuel - 1) original))
           | _ \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format)
        else case code_decode_settlement_ack core of None \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format
          | Some ack \<Rightarrow> Code_Tree_Ready Code_Nested_Other)
     else if family = Wire_Heartbeat then
       (case code_decode_heartbeat core of None \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format
        | Some heartbeat \<Rightarrow> Code_Tree_Ready Code_Nested_Other)
     else if family = Wire_Governance then
       (case code_decode_governance core of None \<Rightarrow> Code_Tree_Refused Invalid_Wire_Format
        | Some governance \<Rightarrow> Code_Tree_Ready Code_Nested_Other)
     else Code_Tree_Refused Invalid_Wire_Format))"
proof (cases fuel)
  case 0
  then show ?thesis by simp
next
  case (Suc predecessor)
  show ?thesis unfolding Suc diff_Suc_1 by simp
qed

declare [[code drop: put_le_octets]]

lemma put_le_octets_integer_code [code]:
  "put_le_octets width number =
    (if width = 0 then [] else number mod 256 # put_le_octets (width - 1) (number div 256))"
  by (cases width) simp_all

declare [[code drop: take_proto_fields]]

lemma take_proto_fields_integer_code [code]:
  "take_proto_fields fuel bytes =
    (if bytes = [] then Some [] else if fuel = 0 then None else
      case take_proto_field bytes of None \<Rightarrow> None | Some (field,rest) \<Rightarrow>
        map_option (Cons field) (take_proto_fields (fuel - 1) rest))"
proof (cases fuel)
  case 0
  then show ?thesis by simp
next
  case (Suc predecessor)
  show ?thesis unfolding Suc diff_Suc_1 by simp
qed

declare [[code drop: read_wire_versions]]

lemma read_wire_versions_integer_code [code]:
  "read_wire_versions count args =
    (if count = 0 then Some ([],args) else
      case args of asset # version # remaining \<Rightarrow>
        map_option (\<lambda>(versions,tail). ((asset,version) # versions,tail))
          (read_wire_versions (count - 1) remaining)
      | _ \<Rightarrow> None)"
proof (cases count)
  case 0
  then show ?thesis by simp
next
  case (Suc predecessor)
  show ?thesis unfolding Suc diff_Suc_1 by simp
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    code_take_varint_from_integer_code
    code_json_elements_integer_code
    code_decode_operand_tree_integer_code
    put_le_octets_integer_code
    take_proto_fields_integer_code
    read_wire_versions_integer_code})
  then () else error "Unexpected oracle in certified integer code equations"
\<close>

end
