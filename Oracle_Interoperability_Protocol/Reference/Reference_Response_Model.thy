theory Reference_Response_Model
  imports "OIP_Product.Wire_Product_Execution"
begin

datatype reference_response_kind =
    Recorded_Result | Delivery_Refusal | Validation_Refusal

fun reference_response_kind_number where
  "reference_response_kind_number Recorded_Result = 1"
| "reference_response_kind_number Delivery_Refusal = 2"
| "reference_response_kind_number Validation_Refusal = 3"

definition reference_response_body where
  "reference_response_body call_id kind code position original =
    \<lparr>wire_opcode = 2,
       wire_words = [fst call_id, snd call_id, reference_response_kind_number kind, code] @
         (case position of None \<Rightarrow> [0] | Some revision \<Rightarrow> [1, revision]),
       wire_blobs = [encode_wire_core original], wire_deadline = Deadline_Absent\<rparr>"

definition reference_response_header_matches where
  "reference_response_header_matches outer original call_id \<longleftrightarrow>
    wire_version outer = wire_version original \<and>
    wire_deployment outer = wire_deployment original \<and>
    wire_source_domain outer = wire_target_domain original \<and>
    wire_target_domain outer = wire_source_domain original \<and>
    fst call_id = wire_principal original \<and>
    (\<exists>native. decode_native_call_prefix original = Some native \<and> native_id native = call_id)"

definition reference_response_position_matches where
  "reference_response_position_matches original kind position \<longleftrightarrow>
    (position = None \<or> kind = Recorded_Result) \<and>
    (\<forall>native revision. wire_message_family original = Wire_State_Sync \<and>
       wire_opcode (wire_operation_body original) = 1 \<and>
       decode_native_call_prefix original = Some native \<and> position = Some revision
       \<longrightarrow> revision = cut_revision (native_cut native))"

definition encode_reference_response where
  "encode_reference_response outer original call_id kind code position signature =
    (let body = reference_response_body call_id kind code position original;
         packet = \<lparr>packet_core = outer\<lparr>wire_message_family := Wire_Ack, wire_operation_body := body\<rparr>,
                     packet_signature = signature\<rparr>
     in if reference_response_header_matches outer original call_id \<and>
          reference_response_position_matches original kind position \<and> wire_packet_wellformed packet
        then Some (encode_wire_packet packet) else None)"

theorem outbound_reference_bytes_decode_to_the_exact_bound_response:
  assumes "encode_reference_response outer original call_id kind code position signature = Some bytes"
  obtains packet where "decode_wire_packet bytes = Some packet"
    "encode_wire_packet packet = bytes"
    "wire_message_family (packet_core packet) = Wire_Ack"
    "wire_operation_body (packet_core packet) = reference_response_body call_id kind code position original"
    "wire_blobs (wire_operation_body (packet_core packet)) = [encode_wire_core original]"
    "reference_response_header_matches outer original call_id"
    "reference_response_position_matches original kind position"
proof -
  let ?body = "reference_response_body call_id kind code position original"
  let ?packet = "\<lparr>packet_core = outer\<lparr>wire_message_family := Wire_Ack, wire_operation_body := ?body\<rparr>,
     packet_signature = signature\<rparr>"
  have valid: "wire_packet_wellformed ?packet" and exact: "encode_wire_packet ?packet = bytes"
    and header: "reference_response_header_matches outer original call_id"
    and position: "reference_response_position_matches original kind position"
    using assms by (auto simp: encode_reference_response_def Let_def split: if_splits)
  have parsed: "decode_wire_packet bytes = Some ?packet"
    unfolding exact[symmetric]
    by (rule the_exact_wire_message_decodes_from_its_canonical_bytes[OF valid])
  have family: "wire_message_family (packet_core ?packet) = Wire_Ack"
    and body: "wire_operation_body (packet_core ?packet) = ?body"
    and original_bytes: "wire_blobs (wire_operation_body (packet_core ?packet)) = [encode_wire_core original]"
    by (simp_all add: reference_response_body_def)
  show thesis by (rule that[OF parsed exact family body original_bytes header position])
qed

lemma a_response_for_debit_cannot_replace_the_original_commit_position:
  assumes "encode_reference_response outer original call_id kind code (Some revision) signature = Some bytes"
    "wire_message_family original = Wire_State_Sync"
    "wire_opcode (wire_operation_body original) = 1"
    "decode_native_call_prefix original = Some native"
  shows "kind = Recorded_Result" "revision = cut_revision (native_cut native)"
  using assms by (auto simp: encode_reference_response_def reference_response_position_matches_def Let_def
    split: if_splits)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms outbound_reference_bytes_decode_to_the_exact_bound_response
      a_response_for_debit_cannot_replace_the_original_commit_position})
  then () else error "Unexpected oracle in outbound reference wire"
\<close>

end
