theory Reference_Wire_Admission
  imports Reference_Ordered_Control
begin

definition select_reference_wire_admission where
  "select_reference_wire_admission verify attest body_allowed scope decode may_prepare bytes control =
    (case wire_gate verify attest body_allowed scope bytes of
       Gate_Refused reason \<Rightarrow> control
     | Gate_Admitted packet \<Rightarrow>
       let core = packet_core packet in
       (case decode core of None \<Rightarrow> control
        | Some request \<Rightarrow>
          if original_packet request = bytes \<and>
             original_transport request = authenticated_wire_message_id core \<and>
             fst (original_call request) = wire_principal core \<and> may_prepare request
          then reference_admit_pending control control request
          else control))"

lemma a_refused_delivery_cannot_create_a_pending_request:
  assumes "wire_gate verify attest body_allowed scope bytes = Gate_Refused reason"
  shows "select_reference_wire_admission verify attest body_allowed scope decode may_prepare bytes control = control"
  using assms by (simp add: select_reference_wire_admission_def)

lemma a_new_pending_request_has_the_exact_verified_wire_input:
  assumes changed: "select_reference_wire_admission verify attest body_allowed scope decode may_prepare bytes control \<noteq> control"
  obtains packet request where "decode_wire_packet bytes = Some packet"
    "encode_wire_packet packet = bytes"
    "current_wire_scope scope (packet_core packet)"
    "decode (packet_core packet) = Some request"
    "original_packet request = bytes"
    "original_transport request = authenticated_wire_message_id (packet_core packet)"
    "fst (original_call request) = wire_principal (packet_core packet)"
    "may_prepare request"
    "reference_can_deliver request control"
    "reference_work_can_start request control"
    "control_decisions (select_reference_wire_admission verify attest body_allowed scope decode may_prepare bytes control)
       (original_call request) = Some (request, Ref_Pending)"
proof -
  obtain packet request where gate: "wire_gate verify attest body_allowed scope bytes = Gate_Admitted packet"
    and decoded: "decode (packet_core packet) = Some request"
    and exact: "original_packet request = bytes"
      "original_transport request = authenticated_wire_message_id (packet_core packet)"
      "fst (original_call request) = wire_principal (packet_core packet)" "may_prepare request"
    using changed
    by (cases "wire_gate verify attest body_allowed scope bytes")
       (auto simp: select_reference_wire_admission_def Let_def split: option.splits if_splits)
  have admitted: "select_reference_wire_admission verify attest body_allowed scope decode may_prepare bytes control =
      reference_admit_pending control control request"
    using gate decoded exact by (simp add: select_reference_wire_admission_def Let_def)
  have current: "reference_can_deliver request control" "reference_work_can_start request control"
    "control_decisions control (original_call request) = None"
    using changed[unfolded admitted]
    by (auto simp: reference_admit_pending_def split: if_splits)
  have saved: "control_decisions (select_reference_wire_admission verify attest body_allowed scope decode may_prepare bytes control)
       (original_call request) = Some (request, Ref_Pending)"
    using admitted current by (simp add: reference_admit_pending_def)
  have parsed: "decode_wire_packet bytes = Some packet" and scoped: "current_wire_scope scope (packet_core packet)"
    using a_wire_admission_uses_the_exact_current_domain_key_epoch_and_signature[OF gate] by blast+
  have encoded: "encode_wire_packet packet = bytes"
    by (rule every_accepted_wire_message_has_exactly_the_received_bytes[OF parsed, THEN conjunct1])
  show thesis by (rule that[OF parsed encoded scoped decoded exact current(1,2) saved])
qed

lemma expired_packet_cannot_enter_the_ordered_reference_control:
  assumes late: "wire_expiry scope (packet_core packet) < boundary_now scope"
    and parsed: "decode_wire_packet bytes = Some packet"
  shows "select_reference_wire_admission verify attest body_allowed scope decode may_prepare bytes control = control"
proof (cases "wire_gate verify attest body_allowed scope bytes")
  case (Gate_Admitted delivered)
  then have decoded: "decode_wire_packet bytes = Some delivered"
    and on_time: "boundary_now scope \<le> wire_expiry scope (packet_core delivered)"
    using a_wire_admission_uses_the_exact_current_domain_key_epoch_and_signature by blast+
  have "delivered = packet" using decoded parsed by simp
  then show ?thesis using on_time late by simp
next
  case (Gate_Refused reason)
  then show ?thesis by (rule a_refused_delivery_cannot_create_a_pending_request)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms a_refused_delivery_cannot_create_a_pending_request
      a_new_pending_request_has_the_exact_verified_wire_input expired_packet_cannot_enter_the_ordered_reference_control})
  then () else error "Unexpected oracle in ordered wire admission"
\<close>

end
