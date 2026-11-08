theory EAB_Resolution_Instance
  imports "Promotion_Resolution" "Owner_Recovery_Effect"
begin

context source_attestation
begin

definition eab_resolution_view where
  "eab_resolution_view binding state =
    (let pending = binding \<in> unresolved_source_obligations state in
     \<lparr>unresolved_binding = (if pending then Some binding else None),
       unresolved_units = (if pending then binding_amount binding else 0),
       active_origin_units = source_units state (source_account_of binding),
       active_destination_units = destination_units state (destination_account_of binding)\<rparr>)"

theorem actual_eab_credit_implements_the_common_resolution:
  fixes authority endpoint index request route binding before
  defines "binding \<equiv> request_binding request"
    and "before \<equiv> machine_state (core_parent authority)"
  assumes pending: "binding \<in> unresolved_source_obligations before"
    and exact: "exact_record_reference authority index binding Confirmed_Decision (request_certificate request)"
    and admissible: "credit_admissible (lock_authority (current_lock_view authority endpoint)) request"
    and issued: "request_certificate request \<in> set (issued_certificates before)"
    and fresh: "credit_marker binding \<notin> consumed_at (received_messages before)"
  shows "let step = invoke_protocol endpoint (core_epoch authority) index (Deliver_Intent route request) authority in
    snd step = Protocol_Response (Delivery_Response (New_Credit binding)) \<and>
    eab_resolution_view binding (machine_state (core_parent (fst step))) =
      resolve_pending (\<lambda>_. True) (eab_resolution_kind authority index binding)
        (request_certificate request) (eab_resolution_view binding before)"
proof -
  let ?certificate = "request_certificate request"
  let ?step = "invoke_protocol endpoint (core_epoch authority) index (Deliver_Intent route request) authority"
  have run: "?step =
    (authority\<lparr>core_parent := fst (record_observation request (Delivery_Response (New_Credit binding))
      (commit_reservation_event (Credit_Event binding) (core_parent authority)))\<rparr>,
      Protocol_Response (Delivery_Response (New_Credit binding)))"
    using exact admissible issued fresh
    by (simp add: binding_def before_def invoke_protocol_def deliver_reserved_credit_def published_receive_expansion
      lift_protocol_result_def record_observation_def Let_def)
  have selected: "bound_resolution (\<lambda>_. True) (eab_resolution_kind authority index binding)
      binding ?certificate = Some Resolve_Credit"
    using exact by (simp add: the_current_eab_evidence_selects_the_exact_resolution_kind)
  show ?thesis
    using pending selected unfolding run
    by (simp add: before_def eab_resolution_view_def resolve_pending_def record_observation_def
      commit_reservation_event_def unresolved_source_obligations_def record_credit_def Let_def)
qed

theorem actual_eab_return_implements_the_common_resolution:
  fixes authority endpoint index request generation versions binding before
  defines "binding \<equiv> request_binding request"
    and "before \<equiv> machine_state (core_parent authority)"
  assumes pending: "binding \<in> unresolved_source_obligations before"
    and exact: "exact_record_reference authority index binding Reversed_Decision (request_certificate request)"
    and fence: "owns_recorded_reservation (current_lock_view authority endpoint) request generation (vector_lookup versions) before"
    and phase: "phase_at before (binding_key binding) = Some Source_Pending"
    and reversed: "reversed_source_evidence (lock_authority (current_lock_view authority endpoint)) request before"
  shows "let step = invoke_protocol endpoint (core_epoch authority) index (Return_Intent request generation versions) authority in
    snd step = Protocol_Response Reservation_Released \<and>
    eab_resolution_view binding (machine_state (core_parent (fst step))) =
      resolve_pending (\<lambda>_. True) (eab_resolution_kind authority index binding)
        (request_certificate request) (eab_resolution_view binding before)"
proof -
  let ?certificate = "request_certificate request"
  let ?step = "invoke_protocol endpoint (core_epoch authority) index (Return_Intent request generation versions) authority"
  have run: "?step =
    (authority\<lparr>core_parent := fst (record_observation request Reservation_Released
      (commit_reservation_event (Return_Event binding) (core_parent authority)))\<rparr>,
      Protocol_Response Reservation_Released)"
    using exact fence phase reversed
    by (simp add: binding_def before_def invoke_protocol_def release_to_source_def
      lift_protocol_result_def record_observation_def Let_def)
  have selected: "bound_resolution (\<lambda>_. True) (eab_resolution_kind authority index binding)
      binding ?certificate = Some Resolve_Return"
    using exact by (simp add: the_current_eab_evidence_selects_the_exact_resolution_kind)
  obtain claim where present: "reservation_at before (binding_key binding) = Some claim"
    using phase by (cases "reservation_at before (binding_key binding)") (simp_all add: phase_at_def)
  show ?thesis
    using pending selected present unfolding run
    by (simp add: before_def eab_resolution_view_def resolve_pending_def record_observation_def
      commit_reservation_event_def unresolved_source_obligations_def finish_reservation_def set_phase_def phase_at_def Let_def)
qed

lemma a_rejected_eab_resolution_is_the_same_pending_view:
  assumes invalid: "bound_resolution (\<lambda>_. True) (eab_resolution_kind authority index (request_binding request))
    (request_binding request) (request_certificate request) \<noteq> Some required"
  shows "let intent = (case required of Resolve_Credit \<Rightarrow> Deliver_Intent route request
                        | Resolve_Return \<Rightarrow> Return_Intent request generation versions);
             result = invoke_protocol endpoint (core_epoch authority) index intent authority in
         snd result = Finality_Rejected \<and>
         eab_resolution_view (request_binding request) (machine_state (core_parent (fst result))) =
         eab_resolution_view (request_binding request) (machine_state (core_parent authority))"
  using the_actual_eab_consumers_cannot_resolve_with_the_wrong_kind[OF invalid, of route generation versions endpoint]
  by (simp add: Let_def)

thm_oracles actual_eab_credit_implements_the_common_resolution actual_eab_return_implements_the_common_resolution
  a_rejected_eab_resolution_is_the_same_pending_view

end

end
