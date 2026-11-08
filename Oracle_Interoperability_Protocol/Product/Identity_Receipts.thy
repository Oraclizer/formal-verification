theory Identity_Receipts
  imports Owner_Recovery
begin

datatype authorized_receipt =
    Observed_Ordinary_Result collection_reply
  | Observed_Legal_Result legal_execution_reply
  | Observed_Spend_Result governed_spend_reply

fun exact_endpoint_receipt where
  "exact_endpoint_receipt verified who
    (Collect_Governed_Order stage entry actor call_id order payload) s =
    (case legal_receipts (regulated_orders s) call_id of None \<Rightarrow> None
     | Some receipt \<Rightarrow> if legal_receipt_matches receipt stage order payload
       then Some (Observed_Legal_Result (legal_result receipt)) else None)"
| "exact_endpoint_receipt verified who (Collect_Governed_Spend actor call_id payload authorization) s =
    (case spend_receipts s call_id of None \<Rightarrow> None
     | Some receipt \<Rightarrow> if spend_receipt_payload receipt = payload \<and> spend_receipt_order receipt = authorization
       then Some (Observed_Spend_Result (spend_receipt_reply receipt)) else None)"
| "exact_endpoint_receipt verified who (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect actor call_id payload))) s =
    Some (Observed_Ordinary_Result (observe_collection verified who call_id payload
      (legal_underlying_outcomes (governed_legal (regulated_orders s)))))"
| "exact_endpoint_receipt verified who action s = None"

definition read_authorized_receipt where
  "read_authorized_receipt directory policy authenticate verify verified route token proof target action s =
    (case external_call_claim action of Some (Read_Receipt, actor, call_id, payload) \<Rightarrow>
        if authorized_endpoint_action directory policy authenticate verify route token proof target action s \<and>
           call_local_status (product_calls (identity_source s)) = Endpoint_Up
        then exact_endpoint_receipt verified actor action s else None
     | _ \<Rightarrow> None)"

lemma obsolete_request_cannot_observe_an_existing_receipt:
  assumes "external_call_claim action = Some (Read_Receipt, actor, call_id, payload)"
    "cut_authority_epoch (envelope_cut (payload_envelope payload)) \<noteq>
       cut_authority_epoch (current_product_cut (identity_source s))"
  shows "read_authorized_receipt directory policy authenticate verify verified route token proof target action s = None"
proof -
  have denied: "\<not> endpoint_call_allowed directory policy authenticate verify token proof target Read_Receipt actor call_id payload (identity_source s)"
    by (rule an_older_signed_request_cannot_use_a_reopened_session[OF assms(2)])
  show ?thesis using assms(1) denied
    by (simp add: read_authorized_receipt_def authorized_endpoint_action_def endpoint_call_allowed_on_def)
qed

lemma unknown_legal_call_never_dispatches_from_receipt_lookup:
  assumes "legal_receipts (regulated_orders s) call_id = None"
  shows "read_authorized_receipt directory policy authenticate verify verified route token proof target
     (Collect_Governed_Order stage entry actor call_id order payload) s = None"
  using assms by (simp add: read_authorized_receipt_def)

lemma receipt_lookup_at_any_route_checks_the_same_endpoint_policy:
  "read_authorized_receipt directory policy authenticate verify verified first token proof target action s =
   read_authorized_receipt directory policy authenticate verify verified second token proof target action s"
  unfolding read_authorized_receipt_def authorized_endpoint_action_def endpoint_call_allowed_on_def by (rule refl)

lemma advancing_only_the_revision_does_not_revoke_a_signed_request:
  assumes "cut_authority_epoch (current_product_cut before) = cut_authority_epoch (current_product_cut after)"
    "product_sessions (product_durable before) = product_sessions (product_durable after)"
  shows "endpoint_call_allowed directory policy authenticate verify token proof target operation actor call_id payload before =
    endpoint_call_allowed directory policy authenticate verify token proof target operation actor call_id payload after"
  using assms by (simp add: endpoint_call_allowed_def endpoint_call_identity_def active_identity_def
      product_identity_bound_def Let_def)

lemma authorized_exact_receipt_reads_the_retained_outcome_without_an_effect:
  fixes action actor call_id payload
  defines "action \<equiv> Ordinary_Product_Action (Read_Authority_Action (Exact_Collect actor call_id payload))"
  assumes admitted: "authorized_endpoint_action directory policy authenticate verify route token proof target action s"
    and live: "call_local_status (product_calls (identity_source s)) = Endpoint_Up"
    and access: "result_access_bound verified actor call_id payload (legal_underlying_outcomes (governed_legal (regulated_orders s)))"
    and existing: "outcome_entries (legal_underlying_outcomes (governed_legal (regulated_orders s))) call_id = Some receipt"
    and exact: "result_payload receipt = payload"
    and ready: "result_completion_ready receipt (legal_underlying_outcomes (governed_legal (regulated_orders s)))"
  shows "read_authorized_receipt directory policy authenticate verify verified route token proof target action s =
    Some (Observed_Ordinary_Result (Collected (result_outcome receipt)))"
proof -
  have state: "outcome_source (legal_underlying_outcomes (governed_legal (regulated_orders s))) = identity_source s"
    by (simp add: identity_source_def regulated_read_world_def legal_underlying_outcomes_def observed_product_source_def)
  have recorded: "observe_collection verified actor call_id payload (legal_underlying_outcomes (governed_legal (regulated_orders s))) =
    Collected (result_outcome receipt)"
    using access existing exact ready live by (simp add: observe_collection_def state)
  show ?thesis using admitted live recorded by (simp add: action_def read_authorized_receipt_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    endpoint_call_refines_authenticated_namespace
    source_attestation.all_external_entries_use_the_same_final_consumer
    source_attestation.every_unauthorized_read_has_the_same_refusal
    source_attestation.handover_atomically_changes_owner_and_sessions_without_spending
    source_attestation.accepted_handover_transfers_exactly_the_live_claims
    source_attestation.handover_rejects_old_signed_actions_on_every_route
    obsolete_request_cannot_observe_an_existing_receipt})
  then () else error "Unexpected oracle in identity, receipts or ownership handover"
\<close>

end
