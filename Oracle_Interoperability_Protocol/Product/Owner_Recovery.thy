theory Owner_Recovery
  imports Ownership_Handover
begin

section \<open>Recovery control and the assigned worker fence\<close>

record 'token recovery_endorsement =
  endorsement_token :: 'token
  endorsement_session :: session_proof

fun recovery_intent where
  "recovery_intent (Cancel_Intent r g versions) = Some (binding_key (request_binding r))"
| "recovery_intent (Fence_Intent r g versions) = Some (binding_key (request_binding r))"
| "recovery_intent (Return_Intent r g versions) = Some (binding_key (request_binding r))"
| "recovery_intent (Reconcile_Intent r g versions) = Some (binding_key (request_binding r))"
| "recovery_intent (Reassign_Intent r duration) = Some (binding_key (request_binding r))"
| "recovery_intent intent = None"

fun owner_claim_origin where
  "owner_claim_origin (Client_Protocol endpoint index intent) = recovery_intent intent"
| "owner_claim_origin command = None"

definition recovery_has_current_endorsement where
  "recovery_has_current_endorsement directory policy authenticate endorse target key call_id payload authorization source \<longleftrightarrow>
    (\<exists>identity proof. authenticate (endorsement_token authorization) = Some identity \<and>
       proof = endorsement_session authorization \<and> active_identity directory identity proof source \<and>
       recovery_controller source key = Some (identity_principal identity) \<and>
       policy identity target (envelope_asset (payload_envelope payload)) Recover_Claim (proof_epoch proof) \<and>
       endorse identity proof target key call_id payload)"

definition recovery_requirements where
  "recovery_requirements directory policy authenticate endorse target action authorization source \<longleftrightarrow>
    (case external_call_claim action of None \<Rightarrow> False
     | Some (operation, actor, call_id, payload) \<Rightarrow>
       if operation \<noteq> Execute_Ordinary then True
       else case owner_claim_origin (envelope_command (payload_envelope payload)) of None \<Rightarrow> True
       | Some key \<Rightarrow> (case authorization of None \<Rightarrow> False | Some signed \<Rightarrow>
          recovery_has_current_endorsement directory policy authenticate endorse target key call_id payload signed source))"

definition replace_identity_source where
  "replace_identity_source source s =
    (let reads = regulated_read_world s; authority = read_authority reads; origins = settlement_primary authority;
         outcomes = origin_outcomes origins;
         updated = update_settlement_outcomes (outcomes\<lparr>outcome_source := source\<rparr>) authority
     in replace_regulated_reads (reads\<lparr>read_authority := updated\<rparr>) s)"

lemma replace_identity_source_consumes_the_same_authority:
  "identity_source (replace_identity_source source s) = source"
  by (simp add: identity_source_def replace_identity_source_def regulated_read_world_def replace_regulated_reads_def
      update_settlement_outcomes_def observed_product_source_def Let_def)

context source_attestation
begin

definition endpoint_with_owner_control where
  "endpoint_with_owner_control directory policy authenticate verify endorse route token proof target action authorization
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s =
    (if recovery_requirements directory policy authenticate endorse target action authorization (identity_source s)
     then run_authorized_endpoint directory policy authenticate verify route token proof target action
       legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s
     else s)"

definition handover_product_owner where
  "handover_product_owner directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal s =
    (if handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal (identity_source s)
     then replace_identity_source
       (apply_owner_handover directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal (identity_source s)) s
     else s)"

lemma no_unsigned_recovery_can_use_an_endpoint:
  assumes "external_call_claim action = Some (Execute_Ordinary, actor, call_id, payload)"
    "owner_claim_origin (envelope_command (payload_envelope payload)) = Some key"
  shows "endpoint_with_owner_control directory policy authenticate verify endorse route token proof target action None
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s = s"
  using assms by (simp add: endpoint_with_owner_control_def recovery_requirements_def)

lemma approval_from_an_old_controller_cannot_authorize_recovery:
  assumes "recovery_controller source key = Some current"
    "authenticate (endorsement_token endorsement) = Some identity"
    "identity_principal identity \<noteq> current"
  shows "\<not> recovery_has_current_endorsement directory policy authenticate endorse target key call_id payload endorsement source"
  using assms by (auto simp: recovery_has_current_endorsement_def)

lemma recovery_on_any_route_uses_the_same_final_consumer:
  "endpoint_with_owner_control directory policy authenticate verify endorse first token proof target action authorization
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s =
   endpoint_with_owner_control directory policy authenticate verify endorse second token proof target action authorization
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s"
  by (simp add: endpoint_with_owner_control_def all_external_entries_use_the_same_final_consumer)

lemma approved_recovery_reaches_the_real_checked_consumer:
  fixes action entry who expected call_id payload
  defines "action \<equiv> Ordinary_Product_Action (Execute_Checked entry who expected call_id payload)"
  assumes "authorized_endpoint_action directory policy authenticate verify route token proof target action s"
    "recovery_requirements directory policy authenticate endorse target action authorization (identity_source s)"
    "\<not> governed_command (envelope_command (payload_envelope payload))"
    "unclaimed_regulated_call s call_id"
  shows "endpoint_with_owner_control directory policy authenticate verify endorse route token proof target action authorization
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s =
     replace_regulated_reads (fst (execute_at_checked_cut permitted verified maintainers registered verified_ack
       Normal_Lock_Entry who expected call_id payload (regulated_read_world s))) s"
  using assms unfolding action_def
  by (simp add: endpoint_with_owner_control_def run_authorized_endpoint_def)

theorem handover_rejects_old_signed_actions_on_every_route:
  fixes s directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal updated
  assumes admit: "handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal (identity_source s)"
    and selected: "external_call_claim action = Some (operation, actor, call_id, payload)"
    and old_epoch: "cut_authority_epoch (envelope_cut (payload_envelope payload)) = cut_authority_epoch (current_product_cut (identity_source s))"
  defines "updated \<equiv> handover_product_owner directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal s"
  shows "endpoint_with_owner_control directory policy authenticate verify endorse route token proof target action authorization
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack updated = updated"
proof -
  have authority: "cut_authority_epoch (current_product_cut (identity_source updated)) = transfer_epoch proposal"
    using handover_atomically_changes_owner_and_sessions_without_spending(4)[OF admit]
    by (simp add: updated_def handover_product_owner_def admit replace_identity_source_consumes_the_same_authority)
  have newer: "cut_authority_epoch (current_product_cut (identity_source s)) < transfer_epoch proposal"
    using admit by (simp add: handover_is_authorized_def lock_context_batch_is_newer_def Let_def)
  have stale: "cut_authority_epoch (envelope_cut (payload_envelope payload)) \<noteq>
    cut_authority_epoch (current_product_cut (identity_source updated))"
    using authority old_epoch newer by simp
  have denied: "\<not> authorized_endpoint_action directory policy authenticate verify route token proof target action updated"
    using an_older_signed_request_cannot_use_a_reopened_session[OF stale]
    by (simp add: authorized_endpoint_action_def selected endpoint_call_allowed_on_def)
  show ?thesis using denied by (simp add: endpoint_with_owner_control_def denied_endpoint_has_no_effect_or_receipt_write)
qed

end

end
