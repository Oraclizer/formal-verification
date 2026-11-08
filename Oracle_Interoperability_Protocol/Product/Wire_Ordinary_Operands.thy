theory Wire_Ordinary_Operands
  imports Wire_Service_Window
begin

datatype ordinary_wire_command =
    Wire_Reserve nat | Wire_Dispatch nat | Wire_Debit nat
  | Wire_Cancel nat | Wire_Fence nat | Wire_Preempt nat | Wire_Timeout nat
  | Wire_Record_Terminal nat nat | Wire_Deliver nat
  | Wire_Refund nat nat | Wire_Reconcile nat nat | Wire_Write nat nat | Wire_Publish

definition decode_ordinary_tail :: "wire_family \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> ordinary_wire_command option" where
  "decode_ordinary_tail family operation args =
    (case family of
       Wire_State_Sync \<Rightarrow> (case args of
         [arg] \<Rightarrow> if operation = 1 then Some (Wire_Debit arg)
                  else if operation = 3 then Some (Wire_Deliver arg) else None
       | [first, second] \<Rightarrow> if operation = 2 \<and> first \<in> {1,2} then Some (Wire_Record_Terminal first second)
                           else if operation = 4 then Some (Wire_Refund first second) else None
       | [] \<Rightarrow> if operation = 5 then Some Wire_Publish else None
       | _ \<Rightarrow> None)
     | Wire_Lock \<Rightarrow> (case args of
         [arg] \<Rightarrow> if operation = 1 then Some (Wire_Reserve arg)
                  else if operation = 2 then Some (Wire_Dispatch arg)
                  else if operation = 3 then Some (Wire_Cancel arg)
                  else if operation = 4 then Some (Wire_Fence arg)
                  else if operation = 5 then Some (Wire_Preempt arg)
                  else if operation = 8 then Some (Wire_Timeout arg) else None
       | [first, second] \<Rightarrow> if operation = 6 then Some (Wire_Reconcile first second)
                           else if operation = 7 then Some (Wire_Write first second) else None
       | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)"

fun read_wire_versions where
  "read_wire_versions 0 args = Some ([], args)"
| "read_wire_versions (Suc count) args =
    (case args of asset # version # remaining \<Rightarrow>
       map_option (\<lambda>(versions, tail). ((asset, version) # versions, tail)) (read_wire_versions count remaining)
     | _ \<Rightarrow> None)"

definition decode_wire_credential_prefix where
  "decode_wire_credential_prefix args =
    (case args of [] \<Rightarrow> None | presence # tail \<Rightarrow>
      if presence = 0 then Some (None, tail)
      else if presence = 1 \<and> length tail \<ge> 6 then
        Some (Some \<lparr>credential_token = \<lparr>token_asset = tail ! 0, token_owner = tail ! 3, token_generation = tail ! 4\<rparr>,
          credential_epoch = tail ! 5, credential_origin = (tail ! 1, tail ! 2)\<rparr>, drop 6 tail)
      else None)"

definition decode_ordinary_operands where
  "decode_ordinary_operands core native =
    (case decode_wire_credential_prefix (native_tail_words native) of None \<Rightarrow> None
     | Some (credential, rest) \<Rightarrow> (case rest of [] \<Rightarrow> None | count # tail \<Rightarrow>
       case read_wire_versions count tail of None \<Rightarrow> None | Some (versions, args) \<Rightarrow>
         if sorted_wrt (<) (map fst versions) then
           map_option (\<lambda>command. (credential, versions, command))
             (decode_ordinary_tail (wire_message_family core) (wire_opcode (wire_operation_body core)) args)
         else None))"

lemma exact_debit_operands_consume_the_decoded_generation:
  assumes "wire_message_family core = Wire_State_Sync"
    "wire_opcode (wire_operation_body core) = 1"
    "native_tail_words native = [1,17,0,17,7,0,9,1,17,0,generation]"
  shows "decode_ordinary_operands core native = Some
    (Some \<lparr>credential_token = \<lparr>token_asset = 17, token_owner = 7, token_generation = 0\<rparr>,
      credential_epoch = 9, credential_origin = (0,17)\<rparr>, [(17,0)], Wire_Debit generation)"
  using assms by (simp add: decode_ordinary_operands_def decode_wire_credential_prefix_def decode_ordinary_tail_def)

lemma exact_op_rejects_missing_or_extra_debit_generation:
  "decode_ordinary_tail Wire_State_Sync 1 [] = None"
  "decode_ordinary_tail Wire_State_Sync 1 [a,b] = None"
  by (simp_all add: decode_ordinary_tail_def)

end
