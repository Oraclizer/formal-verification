theory Reference_Outbound_Code
  imports "OIP_Reference_Profile.Reference_Response_Correlation"
begin

definition native_response_core where
  "native_response_core outer body =
    outer\<lparr>wire_version := 6, wire_purpose := 1, wire_message_family := Wire_Ack,
      wire_primary_code := 1, wire_secondary_code := None, wire_signature_scheme := 1,
      wire_priority := 3, wire_operation_body := body\<rparr>"

definition native_response_fields where
  "native_response_fields outer body =
    [Proto_Varint 1 6, Proto_Varint 2 1, Proto_Fixed64 3 (wire_deployment outer),
     Proto_Fixed64 4 (wire_source_domain outer), Proto_Fixed64 5 (wire_target_domain outer),
     Proto_Fixed64 6 (wire_principal outer), Proto_Fixed64 7 (wire_key_number outer),
     Proto_Fixed64 8 (wire_authority_epoch outer), Proto_Fixed64 9 (wire_sent_seconds outer),
     Proto_Fixed64 10 (wire_ttl_seconds outer), Proto_Bytes 11 (wire_uuid outer),
     Proto_Varint 12 5, Proto_Varint 13 1, Proto_Varint 15 1,
     Proto_Bytes 20 (encode_wire_body body), Proto_Varint 23 (wire_atomicity outer),
     Proto_Varint 24 3, Proto_Fixed64 25 (wire_route_scope outer)]"

definition native_response_operation where
  "native_response_operation exact call_id kind code position =
    (let words = [fst call_id, snd call_id, reference_response_kind_number kind, code, if position = None then 0 else 1]
     in \<lparr>wire_opcode = 2, wire_words = (case position of None \<Rightarrow> words | Some n \<Rightarrow> words @ [n]),
         wire_blobs = [exact], wire_deadline = Deadline_Absent\<rparr>)"

lemma native_response_operation_matches_the_reference_body:
  "native_response_operation (encode_wire_core original) call_id kind code position =
    reference_response_body call_id kind code position original"
  by (cases position) (simp_all add: native_response_operation_def reference_response_body_def Let_def)

definition native_outbound_envelope_bytes where
  "native_outbound_envelope_bytes outer original call_id kind code position signature =
    put_proto_fields
      [Proto_Bytes 1 (put_proto_fields (native_response_fields outer
           (native_response_operation (encode_wire_core original) call_id kind code position))), Proto_Bytes 2 signature]"

lemma the_native_ack_response_header_order_matches_the_wire_core:
  "native_response_fields outer body = core_fields (native_response_core outer body)"
  by (simp add: native_response_fields_def native_response_core_def core_fields_def secondary_field_def)

theorem each_admitted_reference_response_has_the_exact_native_outbound_bytes:
  assumes encoded: "encode_guarded_reference_response
      (native_response_core outer (reference_response_body call_id kind code position original))
      original call_id kind code position signature = Some bytes"
  shows "native_outbound_envelope_bytes outer original call_id kind code position signature = bytes"
proof -
  let ?body = "reference_response_body call_id kind code position original"
  let ?core = "native_response_core outer ?body"
  have updates: "?core\<lparr>wire_message_family := Wire_Ack, wire_operation_body := ?body\<rparr> = ?core"
    by (simp add: native_response_core_def)
  have wire: "encode_wire_packet \<lparr>packet_core = ?core, packet_signature = signature\<rparr> = bytes"
    using encoded by (auto simp: encode_guarded_reference_response_def encode_reference_response_def
      Let_def updates split: if_splits)
  then show ?thesis
    unfolding native_outbound_envelope_bytes_def native_response_operation_matches_the_reference_body
    by (simp add: the_native_ack_response_header_order_matches_the_wire_core
      encode_wire_packet_def packet_fields_def encode_wire_core_def)
qed

theorem the_exact_native_outbound_bytes_decode_to_the_correlated_model_response:
  assumes encoded: "encode_guarded_reference_response
      (native_response_core outer (reference_response_body call_id kind code position original))
      original call_id kind code position signature = Some bytes"
  shows "map_option (correlate_reference_response original)
      (decode_wire_packet (native_outbound_envelope_bytes outer original call_id kind code position signature)) =
      Some (Some (call_id,kind,code,position))"
  using a_guarded_native_response_decodes_and_correlates_to_its_exact_result[OF encoded]
    each_admitted_reference_response_has_the_exact_native_outbound_bytes[OF encoded]
  by simp

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_native_ack_response_header_order_matches_the_wire_core
      native_response_operation_matches_the_reference_body each_admitted_reference_response_has_the_exact_native_outbound_bytes
      the_exact_native_outbound_bytes_decode_to_the_correlated_model_response})
  then () else error "Unexpected oracle in native outbound response bytes"
\<close>

end
