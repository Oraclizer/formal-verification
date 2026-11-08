theory Identity_Endpoints
  imports Identity_Boundary
begin

section \<open>Classification before any effect or receipt consumer\<close>

fun external_call_claim where
  "external_call_claim (Apply_Governed_Order Legal_Source_Emission entry who expected call_id order payload) =
    Some (Emit_Legal_Order, who, call_id, payload)"
| "external_call_claim (Apply_Governed_Order Legal_Receiving_Commit entry who expected call_id order payload) =
    Some (Receive_Legal_Order, who, call_id, payload)"
| "external_call_claim (Apply_Governed_Spend entry who expected call_id payload authorization) =
    Some (Spend_Protected_Root, who, call_id, payload)"
| "external_call_claim (Collect_Governed_Order stage entry who call_id order payload) = Some (Read_Receipt, who, call_id, payload)"
| "external_call_claim (Collect_Governed_Spend who call_id payload authorization) = Some (Read_Receipt, who, call_id, payload)"
| "external_call_claim (Ordinary_Product_Action (Execute_Checked entry who expected call_id payload)) =
    Some (Execute_Ordinary, who, call_id, payload)"
| "external_call_claim (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect who call_id payload))) =
    Some (Read_Receipt, who, call_id, payload)"
| "external_call_claim action = None"

fun canonical_consumer_action where
  "canonical_consumer_action (Apply_Governed_Order stage entry who expected call_id order payload) =
    Apply_Governed_Order stage Regulatory_Normal who expected call_id order payload"
| "canonical_consumer_action (Apply_Governed_Spend entry who expected call_id payload authorization) =
    Apply_Governed_Spend Regulatory_Normal who expected call_id payload authorization"
| "canonical_consumer_action (Collect_Governed_Order stage entry who call_id order payload) =
    Collect_Governed_Order stage Regulatory_Normal who call_id order payload"
| "canonical_consumer_action (Ordinary_Product_Action (Execute_Checked entry who expected call_id payload)) =
    Ordinary_Product_Action (Execute_Checked Normal_Lock_Entry who expected call_id payload)"
| "canonical_consumer_action action = action"

definition identity_source where
  "identity_source s = observed_product_source (read_authority (regulated_read_world s))"

definition authorized_endpoint_action where
  "authorized_endpoint_action directory policy authenticate verify route token proof target action s \<longleftrightarrow>
    (case external_call_claim action of None \<Rightarrow> False
    | Some (operation, actor, call_id, payload) \<Rightarrow>
        endpoint_call_allowed_on route directory policy authenticate verify token proof target operation actor call_id payload (identity_source s))"

context source_attestation
begin

definition run_authorized_endpoint where
  "run_authorized_endpoint directory policy authenticate verify route token proof target action
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s =
    (if authorized_endpoint_action directory policy authenticate verify route token proof target action s then
       regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified
         maintainers registered verified_ack (canonical_consumer_action action) s
     else s)"

theorem all_external_entries_use_the_same_final_consumer:
  "run_authorized_endpoint directory policy authenticate verify first token proof target action
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s =
   run_authorized_endpoint directory policy authenticate verify second token proof target action
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s"
  unfolding run_authorized_endpoint_def authorized_endpoint_action_def endpoint_call_allowed_on_def by (rule refl)

lemma denied_endpoint_has_no_effect_or_receipt_write:
  assumes "\<not> authorized_endpoint_action directory policy authenticate verify route token proof target action s"
  shows "run_authorized_endpoint directory policy authenticate verify route token proof target action
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s = s"
  using assms by (simp add: run_authorized_endpoint_def)

lemma accepted_endpoint_uses_a_submitted_authenticated_namespace:
  assumes admitted: "authorized_endpoint_action directory policy authenticate verify route token proof target action s"
  obtains operation actor call_id payload identity where "external_call_claim action = Some (operation, actor, call_id, payload)"
    "authenticate token = Some identity"
    "directory (fst call_id) = Some identity" "identity_principal identity = fst call_id"
    "envelope_caller (payload_envelope payload) = fst call_id"
    "verify identity proof target operation call_id payload"
proof -
  obtain operation actor call_id payload where selected: "external_call_claim action = Some (operation, actor, call_id, payload)"
    using admitted by (auto simp: authorized_endpoint_action_def split: option.splits prod.splits)
  have bound: "endpoint_call_allowed directory policy authenticate verify token proof target operation actor call_id payload (identity_source s)"
    using admitted selected by (simp add: authorized_endpoint_action_def endpoint_call_allowed_on_def)
  then show thesis using that selected endpoint_call_refines_authenticated_namespace[OF bound] by blast
qed

lemma maintenance_context_cannot_be_submitted_as_a_client_action:
  "run_authorized_endpoint directory policy authenticate verify route token proof target
     (Ordinary_Product_Action (Read_Authority_Action (Exact_Install who epoch changes sessions)))
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s = s"
  by (simp add: run_authorized_endpoint_def authorized_endpoint_action_def)

end

end
