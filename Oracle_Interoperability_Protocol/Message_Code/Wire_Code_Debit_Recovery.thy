theory Wire_Code_Debit_Recovery
  imports Wire_Code_Debit_Selection Wire_Code_Response_Status Wire_Code_Path_Guards
    "OIP_Reference_Execution.Reference_Wire_Trace_Bounds"
begin

definition code_original_debit where
  "code_original_debit bytes core native generation =
    \<lparr>original_call = native_id native,original_origin = native_origin native,
      original_generation = generation,original_transport = authenticated_wire_message_id core,
      original_packet = bytes\<rparr>"

definition code_resolution_admission_scope where
  "code_resolution_admission_scope scope core = scope\<lparr>boundary_now := wire_sent_seconds core\<rparr>"

lemma resolution_rechecks_the_signed_origin_clock_instead_of_the_current_delivery_clock:
  "boundary_now (code_resolution_admission_scope scope core) = wire_sent_seconds core"
  "code_wire_expiry core (code_resolution_admission_scope scope core) = code_wire_expiry core scope"
  by (simp_all add: code_resolution_admission_scope_def code_wire_expiry_def)

lemma resolution_cannot_fail_only_because_the_original_delivery_clock_is_now_late:
  "code_check_versioned_scope core (code_resolution_admission_scope scope core) 6 \<noteq> Some Wire_TTL_Expired"
  by (auto simp: code_check_versioned_scope_def code_resolution_admission_scope_def
    code_wire_expiry_def Let_def split: option.splits if_splits)

text \<open>
  This is the successful applied-receipt slice, not the complete resolver.
  Attachment, authenticated-head freshness and current receipt authorization
  are supplied by their existing product consumers.  Pending, explicit close,
  retained refusal and concurrent-observation errors are separate obligations.
  The source resolver does not call the configured maximum-delivery-TTL check.
\<close>

definition code_checked_applied_debit_response where
  "code_checked_applied_debit_response verify authorized scope bytes credential_packet frame payload outer signature =
    (if code_check_declared_version bytes (boundary_max_frame scope) \<noteq> None then None
     else case decode_wire_packet bytes of None \<Rightarrow> None | Some packet \<Rightarrow>
       let core = packet_core packet in
       if code_check_operation code_reference_accepts core \<noteq> None \<or>
          \<not> code_matches_signed_packet bytes credential_packet \<or>
          code_admit_packet verify packet (code_resolution_admission_scope scope core) \<noteq> None
       then None
       else case code_decode_ordinary core of Code_Ordinary_Ready native credential versions (Wire_Debit generation) \<Rightarrow>
         resolve_selected_debit_response authorized frame (code_original_debit bytes core native generation)
           payload outer signature
        | _ \<Rightarrow> None)"

theorem a_checked_applied_resolution_returns_the_exact_received_native_debit:
  assumes emitted: "code_checked_applied_debit_response verify authorized scope bytes credential_packet frame payload outer signature = Some response"
  obtains packet native credential versions generation
  where
    "decode_wire_packet bytes = Some packet" "encode_wire_packet packet = bytes"
    "code_decode_ordinary (packet_core packet) =
      Code_Ordinary_Ready native credential versions (Wire_Debit generation)"
    "control_decisions (image_ordered_control frame) (native_id native) =
      Some (code_original_debit bytes (packet_core packet) native generation,Ref_Applied)"
    "retained_outcomes (reference_product (image_authority frame)) (native_id native) =
      Some \<lparr>result_payload = payload,result_outcome = Authority_Reply (Protocol_Response Source_Debited)\<rparr>"
    "map_option (correlate_reference_response (packet_core packet)) (decode_wire_packet response) =
      Some (Some (native_id native,Recorded_Result,12,Some (cut_revision (envelope_cut (payload_envelope payload)))))"
proof -
  obtain packet native credential versions generation where packet: "decode_wire_packet bytes = Some packet"
    and source: "code_decode_ordinary (packet_core packet) =
      Code_Ordinary_Ready native credential versions (Wire_Debit generation)"
    and exact: "resolve_selected_debit_response authorized frame
      (code_original_debit bytes (packet_core packet) native generation) payload outer signature = Some response"
    using emitted
    by (auto simp: code_checked_applied_debit_response_def Let_def
      split: option.splits code_ordinary_result.splits ordinary_wire_command.splits if_splits)
  have encoded: "encode_wire_packet packet = bytes"
    using every_accepted_wire_message_has_exactly_the_received_bytes[OF packet] by blast
  let ?request = "code_original_debit bytes (packet_core packet) native generation"
  obtain original where old:
      "decode_wire_packet (original_packet ?request) = Some original"
      "control_decisions (image_ordered_control frame) (original_call ?request) = Some (?request,Ref_Applied)"
      "retained_outcomes (reference_product (image_authority frame)) (original_call ?request) =
        Some \<lparr>result_payload = payload,result_outcome = Authority_Reply (Protocol_Response Source_Debited)\<rparr>"
      "map_option (correlate_reference_response (packet_core original)) (decode_wire_packet response) =
        Some (Some (original_call ?request,Recorded_Result,12,
          Some (cut_revision (envelope_cut (payload_envelope payload)))))"
    by (rule an_ordered_resolved_response_identifies_the_actual_retained_debit_and_the_original_bytes[OF exact])
  have same: "original = packet" using old(1) packet by (simp add: code_original_debit_def)
  show thesis
    using old(2,3,4) same
    by (intro that[OF packet encoded source]) (simp_all add: code_original_debit_def)
qed

lemma current_receipt_authorization_is_required_for_an_applied_response:
  "\<not> authorized \<Longrightarrow>
    code_checked_applied_debit_response verify authorized scope bytes credential_packet frame payload outer signature = None"
  by (auto simp: code_checked_applied_debit_response_def resolve_selected_debit_response_def Let_def
    split: option.splits code_ordinary_result.splits ordinary_wire_command.splits if_splits)

end
