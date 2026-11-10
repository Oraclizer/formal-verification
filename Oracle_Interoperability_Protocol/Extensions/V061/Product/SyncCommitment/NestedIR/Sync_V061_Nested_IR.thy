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
     | None \<Rightarrow> sync_v061_operand_verdict core depth)"

definition sync_v061_full_operand_ir where
  "sync_v061_full_operand_ir depth core =
    (case sync_selected_nested_ir depth core of Some (Inl refusal) \<Rightarrow> None
     | Some (Inr typed) \<Rightarrow> Some typed
     | None \<Rightarrow> sync_v061_operand_ir depth core)"

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

lemma sync_a_legacy_decoded_core_is_not_an_added_operation:
  assumes "decode_wire_core raw = Some core"
  shows "\<not> sync_added_operation core"
proof
  assume added: "sync_added_operation core"
  have "wire_core_wellformed core"
    using accepted_core_bytes_preserve_all_original_fields[OF assms] by blast
  with sync_added_operation_is_outside_the_previous_family[OF added] show False
    by (simp add: wire_core_wellformed_def)
qed

lemma sync_typed_ack_preserves_legacy_originals:
  assumes ack: "sync_operation core = (Wire_Ack,2)"
    and enclosed: "wire_blobs (wire_operation_body core) = [raw]"
      "decode_wire_core raw = Some original"
    and receipt: "sync_operation original = (Wire_Query,8) \<Longrightarrow>
       \<exists>inner_raw inner. wire_blobs (wire_operation_body original) = [inner_raw] \<and>
         decode_wire_core inner_raw = Some inner"
  shows "sync_v061_full_operand_verdict core depth = code_transport_operand_verdict core depth"
    "sync_v061_full_operand_ir depth core = code_typed_operand_ir depth core"
proof -
  have original: "sync_single_original core = Some original"
    using enclosed sync_preserves_every_decoded_legacy_core[OF enclosed(2)]
    by (simp add: sync_single_original_def)
  have non_sync: "\<not> sync_ack_has_added_original core"
  proof (cases "sync_operation original = (Wire_Query,8)")
    case True
    from receipt[OF True] obtain inner_raw inner where inner:
      "wire_blobs (wire_operation_body original) = [inner_raw]"
      "decode_wire_core inner_raw = Some inner" by blast
    have decoded: "sync_single_original original = Some inner"
      using inner sync_preserves_every_decoded_legacy_core[OF inner(2)]
      by (simp add: sync_single_original_def)
    show ?thesis
      using original True sync_a_legacy_decoded_core_is_not_an_added_operation[OF enclosed(2)]
        sync_a_legacy_decoded_core_is_not_an_added_operation[OF inner(2)]
      by (simp add: sync_ack_has_added_original_def sync_direct_added_original_def decoded)
  next
    case False
    with original sync_a_legacy_decoded_core_is_not_an_added_operation[OF enclosed(2)]
    show ?thesis by (simp add: sync_ack_has_added_original_def)
  qed
  have selected: "sync_selected_nested_ir depth core = None"
    using ack non_sync by (simp add: sync_selected_nested_ir_def)
  show "sync_v061_full_operand_verdict core depth = code_transport_operand_verdict core depth"
    using ack by (simp add: sync_v061_full_operand_verdict_def sync_v061_operand_verdict_def
      sync_added_operation_def selected)
  show "sync_v061_full_operand_ir depth core = code_typed_operand_ir depth core"
    using ack by (simp add: sync_v061_full_operand_ir_def sync_v061_operand_ir_def
      sync_added_operation_def selected)
qed

definition sync_v061_nested_transport_flat where
  "sync_v061_nested_transport_flat =
    sync_transport_flat_values sync_v061_full_operand_verdict sync_v061_full_operand_ir"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_nested_typed_success_is_from_the_same_wire_parse
      sync_nested_typed_refusal_has_no_value sync_a_legacy_decoded_core_is_not_an_added_operation
      sync_typed_ack_preserves_legacy_originals})
  then () else error "Unexpected oracle in the synchronization nested typed projection"
\<close>

export_code sync_v061_nested_transport_flat
  in SML module_name OIP_Wire_Oracle_V061 file_prefix "oip_wire_values_v061_nested"

end
