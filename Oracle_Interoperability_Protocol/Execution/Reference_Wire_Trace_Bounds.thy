theory Reference_Wire_Trace_Bounds
  imports Reference_Trace_Consumers "OIP_Reference_Profile.Reference_Response_Correlation"
    "OIP_Reference_Profile.Reference_Product_Image" "OIP_Product.Wire_Debit_Bridge"
begin

lemma an_oversize_frame_cannot_create_an_ordered_reference_admission:
  assumes "length bytes > boundary_max_frame scope"
  shows "wire_gate verify attest body_allowed scope bytes = Gate_Refused Invalid_Wire_Format"
    "select_reference_wire_admission verify attest body_allowed scope decode may_prepare bytes control = control"
  using assms by (simp_all add: wire_gate_def select_reference_wire_admission_def)

lemma a_late_delivery_is_refused_even_though_a_selected_request_can_publish:
  assumes packet: "decode_wire_packet bytes = Some decoded" "original_packet request = bytes"
    and late: "wire_expiry scope (packet_core decoded) < boundary_now scope"
    and selected: "control_decisions control (original_call request) = Some (request, Ref_Pending)"
  shows "select_reference_wire_admission verify attest body_allowed scope decode may_prepare bytes control = control"
    "control_decisions (reference_publish_applied control control request head) (original_call request) = Some (request, Ref_Applied)"
  by (rule expired_packet_cannot_enter_the_ordered_reference_control[OF late packet(1)])
     (rule an_admitted_debit_publishes_without_rechecking_the_delivery_clock(2)[OF selected])

definition resolve_selected_debit_response where
  "resolve_selected_debit_response authorized frame request payload outer signature =
    (if authorized \<and> fst (original_call request) \<notin> control_revoked (image_ordered_control frame) \<and>
        control_decisions (image_ordered_control frame) (original_call request) = Some (request,Ref_Applied) \<and>
        retained_outcomes (reference_product (image_authority frame)) (original_call request) =
          Some \<lparr>result_payload = payload, result_outcome = Authority_Reply (Protocol_Response Source_Debited)\<rparr>
     then case decode_wire_packet (original_packet request) of None \<Rightarrow> None | Some original \<Rightarrow>
       encode_guarded_reference_response outer (packet_core original) (original_call request) Recorded_Result 12
         (Some (cut_revision (envelope_cut (payload_envelope payload)))) signature
     else None)"

lemma an_ordered_debit_response_cannot_be_resolved_from_a_prepare_or_refusal:
  assumes "\<not> authorized \<or> fst (original_call request) \<in> control_revoked (image_ordered_control frame) \<or>
       control_decisions (image_ordered_control frame) (original_call request) \<noteq> Some (request,Ref_Applied)"
  shows "resolve_selected_debit_response authorized frame request payload outer signature = None"
  using assms by (auto simp: resolve_selected_debit_response_def)

theorem an_ordered_resolved_response_identifies_the_actual_retained_debit_and_the_original_bytes:
  assumes emitted: "resolve_selected_debit_response authorized frame request payload outer signature = Some bytes"
  obtains original where "decode_wire_packet (original_packet request) = Some original"
    "control_decisions (image_ordered_control frame) (original_call request) = Some (request,Ref_Applied)"
    "retained_outcomes (reference_product (image_authority frame)) (original_call request) =
         Some \<lparr>result_payload = payload, result_outcome = Authority_Reply (Protocol_Response Source_Debited)\<rparr>"
    "map_option (correlate_reference_response (packet_core original)) (decode_wire_packet bytes) =
        Some (Some (original_call request,Recorded_Result,12,Some (cut_revision (envelope_cut (payload_envelope payload)))))"
proof -
  obtain original where input: "decode_wire_packet (original_packet request) = Some original"
    and applied: "control_decisions (image_ordered_control frame) (original_call request) = Some (request,Ref_Applied)"
    and retained: "retained_outcomes (reference_product (image_authority frame)) (original_call request) =
         Some \<lparr>result_payload = payload, result_outcome = Authority_Reply (Protocol_Response Source_Debited)\<rparr>"
    and exact: "encode_guarded_reference_response outer (packet_core original) (original_call request) Recorded_Result 12
       (Some (cut_revision (envelope_cut (payload_envelope payload)))) signature = Some bytes"
    using emitted by (auto simp: resolve_selected_debit_response_def split: option.splits if_splits)
  show thesis by (rule that[OF input applied retained a_guarded_native_response_decodes_and_correlates_to_its_exact_result[OF exact]])
qed

context reference_trace_consumer
begin

fun reference_ordered_debit_claim where
  "reference_ordered_debit_claim (Service_Execute route token proof target action endorsement) = external_call_claim action"
| "reference_ordered_debit_claim action = None"

definition consume_fresh_ordered_reference_debit where
  "consume_fresh_ordered_reference_debit verify_wire attest body_allowed scope decode may_prepare route token endorsement attach
      bytes connection request payload head frame =
    (let admitted = select_reference_wire_admission verify_wire attest body_allowed scope decode may_prepare bytes (image_ordered_control frame) in
     if admitted = image_ordered_control frame \<or> control_decisions admitted (original_call request) \<noteq> Some (request,Ref_Pending)
        \<or> original_packet request \<noteq> bytes \<or> retained_outcomes (reference_product (image_authority frame)) (original_call request) \<noteq> None
     then frame
     else case decode_wire_packet bytes of None \<Rightarrow> frame | Some packet \<Rightarrow>
       (case select_wire_debit route token endorsement attach (packet_core packet) of None \<Rightarrow> frame | Some (owner,action) \<Rightarrow>
        if decode (packet_core packet) \<noteq> Some request \<or>
           reference_ordered_debit_claim action \<noteq> Some (Execute_Ordinary, fst (original_call request), original_call request, payload) then frame
        else
         let executed = serve connection action None (image_authority frame); candidate = fst executed in
         if retained_outcomes (reference_product candidate) (original_call request) =
              Some \<lparr>result_payload = payload, result_outcome = Authority_Reply (Protocol_Response Source_Debited)\<rparr>
         then commit_reference_debit admitted (frame\<lparr>image_ordered_control := admitted\<rparr>) request head candidate else frame))"

theorem a_verified_wire_debit_can_only_publish_and_resolve_the_actual_selected_service_receipt:
  fixes after verify_wire attest body_allowed scope decode may_prepare route token endorsement attach bytes connection request payload head frame
  defines "after \<equiv> consume_fresh_ordered_reference_debit verify_wire attest body_allowed scope decode may_prepare route token endorsement attach
      bytes connection request payload head frame"
  assumes changed: "after \<noteq> frame"
  obtains packet owner action
  where "decode_wire_packet bytes = Some packet"
    "encode_wire_packet packet = bytes"
    "original_packet request = bytes"
    "select_wire_debit route token endorsement attach (packet_core packet) = Some (owner,action)"
    "image_authority after = fst (serve connection action None (image_authority frame))"
    "control_head (image_ordered_control after) = Some head"
    "image_transport after (original_transport request) = Some (encode_wire_core (packet_core packet))"
    "\<And>authorized outer signature response. resolve_selected_debit_response authorized after request payload outer signature = Some response \<Longrightarrow>
       map_option (correlate_reference_response (packet_core packet)) (decode_wire_packet response) =
          Some (Some (original_call request,Recorded_Result,12,Some (cut_revision (envelope_cut (payload_envelope payload)))))"
proof -
  let ?control = "select_reference_wire_admission verify_wire attest body_allowed scope decode may_prepare bytes (image_ordered_control frame)"
  let ?staged = "frame\<lparr>image_ordered_control := ?control\<rparr>"
  obtain packet owner action where decoded: "decode_wire_packet bytes = Some packet"
    and original: "original_packet request = bytes" and selected: "select_wire_debit route token endorsement attach (packet_core packet) = Some (owner,action)"
    and admitted: "control_decisions ?control (original_call request) = Some (request,Ref_Pending)"
    and published: "after = commit_reference_debit ?control ?staged request head (fst (serve connection action None (image_authority frame)))"
    using changed by (auto simp: after_def consume_fresh_ordered_reference_debit_def Let_def split: option.splits prod.splits if_splits)
  have preserved: "encode_wire_packet packet = bytes"
    using every_accepted_wire_message_has_exactly_the_received_bytes[OF decoded] by simp
  have packet: "decode_wire_packet (original_packet request) = Some packet" using original decoded by simp
  have current: "?control = image_ordered_control ?staged" by simp
  note atomic = an_ordered_debit_publishes_the_exact_input_and_product_view_together[OF current admitted packet]
  have result: "image_authority after = fst (serve connection action None (image_authority frame))"
    "control_head (image_ordered_control after) = Some head"
    "image_transport after (original_transport request) = Some (encode_wire_core (packet_core packet))"
    using atomic published by (simp_all add: Let_def)
  show thesis
  proof (rule that[OF decoded preserved original selected result])
    fix authorized outer signature response
    assume encoded: "resolve_selected_debit_response authorized after request payload outer signature = Some response"
    have exact: "encode_guarded_reference_response outer (packet_core packet) (original_call request) Recorded_Result 12
       (Some (cut_revision (envelope_cut (payload_envelope payload)))) signature = Some response"
      using encoded packet by (auto simp: resolve_selected_debit_response_def split: if_splits)
    show "map_option (correlate_reference_response (packet_core packet)) (decode_wire_packet response) =
          Some (Some (original_call request,Recorded_Result,12,Some (cut_revision (envelope_cut (payload_envelope payload)))))"
      by (rule a_guarded_native_response_decodes_and_correlates_to_its_exact_result[OF exact])
  qed
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms an_oversize_frame_cannot_create_an_ordered_reference_admission
    a_late_delivery_is_refused_even_though_a_selected_request_can_publish
    an_ordered_debit_response_cannot_be_resolved_from_a_prepare_or_refusal
    an_ordered_resolved_response_identifies_the_actual_retained_debit_and_the_original_bytes
    reference_trace_consumer.a_verified_wire_debit_can_only_publish_and_resolve_the_actual_selected_service_receipt})
  then () else error "Unexpected oracle in wire trace bounds"
\<close>

end
