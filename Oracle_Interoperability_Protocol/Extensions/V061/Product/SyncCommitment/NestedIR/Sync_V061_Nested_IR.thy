theory Sync_V061_Nested_IR
  imports "OIP_Sync_V061_Position_Transport.Sync_V061_Transport_IR"
    "OIP_Sync_V061_Position_Ack.Sync_V061_Ack_Link_Draft"
begin

definition sync_single_original where
  "sync_single_original core =
    (case wire_blobs (wire_operation_body core) of [raw] \<Rightarrow> sync_decode_core raw | _ \<Rightarrow> None)"

definition sync_direct_added_original where
  "sync_direct_added_original core \<longleftrightarrow>
    (case sync_single_original core of None \<Rightarrow> False | Some original \<Rightarrow> sync_added_operation original)"

definition sync_ack_has_added_original where
  "sync_ack_has_added_original core \<longleftrightarrow>
    (case sync_single_original core of None \<Rightarrow> False | Some original \<Rightarrow>
       sync_added_operation original \<or>
       (sync_operation original = (Wire_Query,8) \<and> sync_direct_added_original original))"

definition sync_receipt_operand_ir where
  "sync_receipt_operand_ir session original request =
    code_ir_node 15 [code_ir_scalar session,code_ir_bytes (encode_wire_core original),sync_call_operand_ir request]"

definition sync_query_eight_wire_ir where
  "sync_query_eight_wire_ir depth core =
    (case sync_parse_query_eight depth core of None \<Rightarrow> Inl Invalid_Wire_Format
     | Some receipt \<Rightarrow> Inr (sync_receipt_operand_ir (sync_receipt_session receipt)
          (sync_receipt_inner receipt) (sync_receipt_request receipt)))"

fun sync_response_kind_number where
  "sync_response_kind_number Recorded_Result = 1"
| "sync_response_kind_number Delivery_Refusal = 2"
| "sync_response_kind_number Validation_Refusal = 3"

definition sync_enclosed_operand_ir where
  "sync_enclosed_operand_ir original =
    (let enclosed = sync_link_enclosed original; effective = sync_link_call_core original;
         request = sync_link_request original in
     if enclosed = effective then sync_call_operand_ir request
     else sync_receipt_operand_ir (hd (wire_words (wire_operation_body enclosed))) effective request)"

definition sync_ack_operand_ir where
  "sync_ack_operand_ir view =
    code_ir_node 16 [code_ir_pair (sync_link_id view),
      code_ir_scalar (sync_response_kind_number (sync_link_kind view)),
      code_ir_scalar (sync_link_code view),code_ir_option code_ir_scalar (sync_link_commit view),
      code_ir_bytes (sync_link_exact_original view),sync_enclosed_operand_ir (sync_link_original_view view)]"

definition sync_ack_wire_ir where
  "sync_ack_wire_ir depth core =
    (case sync_link_parse_ack True depth core of Inl refusal \<Rightarrow> Inl refusal
     | Inr view \<Rightarrow> Inr (sync_ack_operand_ir view))"

definition sync_legacy_ack_new_number where
  "sync_legacy_ack_new_number depth core =
    (if depth \<le> 1 \<or> wire_deadline (wire_operation_body core) \<noteq> Deadline_Absent
     then Code_Operand_Refuse Invalid_Wire_Format
     else case sync_single_original core of None \<Rightarrow> Code_Operand_Refuse Invalid_Wire_Format
      | Some original \<Rightarrow> (case code_decode_operand_tree (depth - 1) original of
          Code_Tree_Refused refusal \<Rightarrow> Code_Operand_Refuse refusal
        | Code_Tree_Pending \<Rightarrow> Code_Operand_Pending
        | Code_Tree_Ready decoded \<Rightarrow>
            (case response_result_words (wire_words (wire_operation_body core)) of None \<Rightarrow> Code_Operand_Refuse Invalid_Wire_Format
             | Some (caller,kind,code,position) \<Rightarrow>
               if kind \<noteq> Recorded_Result \<or> (position \<noteq> None) \<noteq> (code = 29)
               then Code_Operand_Refuse Invalid_Wire_Format
               else case code_response_tree_finish core original decoded of
                 Code_Tree_Refused refusal \<Rightarrow> Code_Operand_Refuse refusal
               | Code_Tree_Pending \<Rightarrow> Code_Operand_Pending
               | Code_Tree_Ready value \<Rightarrow> Code_Operand_Refuse Invalid_Wire_Format)))"

definition sync_ack_uses_added_number where
  "sync_ack_uses_added_number core \<longleftrightarrow>
    (case response_result_words (wire_words (wire_operation_body core)) of
      Some (caller,kind,code,position) \<Rightarrow> sync_added_status code | None \<Rightarrow> False)"

definition sync_selected_nested_ir where
  "sync_selected_nested_ir depth core =
    (if sync_operation core = (Wire_Query,8) \<and> sync_direct_added_original core
     then Some (sync_query_eight_wire_ir depth core)
     else if sync_operation core = (Wire_Ack,2) \<and> sync_ack_has_added_original core
     then Some (sync_ack_wire_ir depth core)
     else None)"

definition sync_v061_full_operand_verdict where
  "sync_v061_full_operand_verdict core depth =
    (case sync_selected_nested_ir depth core of
       Some (Inl refusal) \<Rightarrow> Code_Operand_Refuse refusal
     | Some (Inr typed) \<Rightarrow> Code_Operand_Accept
     | None \<Rightarrow>
        if sync_operation core = (Wire_Ack,2) \<and> sync_ack_uses_added_number core
        then sync_legacy_ack_new_number depth core
        else sync_v061_operand_verdict core depth)"

definition sync_v061_full_operand_ir where
  "sync_v061_full_operand_ir depth core =
    (case sync_selected_nested_ir depth core of Some (Inl refusal) \<Rightarrow> None
     | Some (Inr typed) \<Rightarrow> Some typed
     | None \<Rightarrow>
        if sync_operation core = (Wire_Ack,2) \<and> sync_ack_uses_added_number core then None
        else sync_v061_operand_ir depth core)"

lemma sync_nested_typed_success_is_from_the_same_wire_parse:
  assumes "sync_selected_nested_ir depth core = Some (Inr typed)"
  shows "sync_v061_full_operand_ir depth core = Some typed"
    "sync_v061_full_operand_verdict core depth = Code_Operand_Accept"
  using assms by (simp_all add: sync_v061_full_operand_ir_def sync_v061_full_operand_verdict_def)

lemma sync_nested_typed_refusal_has_no_value:
  assumes "sync_selected_nested_ir depth core = Some (Inl refusal)"
  shows "sync_v061_full_operand_ir depth core = None"
    "sync_v061_full_operand_verdict core depth = Code_Operand_Refuse refusal"
  using assms by (simp_all add: sync_v061_full_operand_ir_def sync_v061_full_operand_verdict_def)

lemma sync_legacy_ack_cannot_borrow_an_added_sync_status:
  "sync_legacy_ack_new_number depth core \<noteq> Code_Operand_Accept"
  by (auto simp: sync_legacy_ack_new_number_def
      split: option.splits prod.splits code_operand_tree_result.splits if_splits)

definition sync_v061_nested_transport_flat where
  "sync_v061_nested_transport_flat =
    sync_transport_flat_values sync_v061_full_operand_verdict sync_v061_full_operand_ir"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_nested_typed_success_is_from_the_same_wire_parse
      sync_nested_typed_refusal_has_no_value sync_legacy_ack_cannot_borrow_an_added_sync_status})
  then () else error "Unexpected oracle in the synchronization nested typed projection"
\<close>

export_code sync_v061_nested_transport_flat
  in SML module_name OIP_Wire_Oracle_V061 file_prefix "oip_wire_values_v061_nested"

end
