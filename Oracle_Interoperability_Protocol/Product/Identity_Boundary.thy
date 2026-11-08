theory Identity_Boundary
  imports Regulated_Acceptance
begin

section \<open>Authenticated submissions and the endpoint's final decision\<close>

record registered_identity =
  identity_principal :: product_principal
  identity_domain :: nat
  identity_ocid :: nat
  identity_rai :: nat

record session_proof =
  proof_session :: product_session_id
  proof_epoch :: nat

datatype identity_route =
    Identity_Normal
  | Identity_Administrative
  | Identity_Force_Inclusion
  | Identity_Upgrade
  | Identity_Adapter

datatype endpoint_use =
    Execute_Ordinary
  | Emit_Legal_Order
  | Receive_Legal_Order
  | Spend_Protected_Root
  | Read_Receipt
  | Read_Current_Data
  | Read_Historical_Data
  | Read_Raw_Data
  | Read_Operation_Status
  | Read_Journal
  | Transfer_Ownership
  | Recover_Claim

type_synonym identity_directory = "product_principal \<Rightarrow> registered_identity option"
type_synonym endpoint_policy =
  "registered_identity \<Rightarrow> nat \<Rightarrow> product_asset \<Rightarrow> endpoint_use \<Rightarrow> nat \<Rightarrow> bool"

definition active_identity where
  "active_identity directory identity proof source \<longleftrightarrow>
    directory (identity_principal identity) = Some identity \<and>
    proof_epoch proof = cut_authority_epoch (current_product_cut source) \<and>
    product_sessions (product_durable source) (proof_session proof) =
      Some \<lparr>session_principal = identity_principal identity, session_epoch = proof_epoch proof\<rparr>"

fun command_target where
  "command_target envelope (Client_Terminal cert) = fst (envelope_origin envelope)"
| "command_target envelope (Client_Protocol endpoint index intent) = endpoint"
| "command_target envelope (Client_Regulatory endpoint index request) = endpoint"
| "command_target envelope (Client_Publication key) = fst key"

definition endpoint_call_identity where
  "endpoint_call_identity directory policy authenticate verify token proof target operation actor call_id payload source \<longleftrightarrow>
    (let envelope = payload_envelope payload; command = envelope_command envelope in
     \<exists>identity. authenticate token = Some identity \<and> identity_principal identity = actor \<and>
       active_identity directory identity proof source \<and>
       proof_session proof = envelope_session envelope \<and>
       product_identity_bound actor call_id envelope source \<and> command_target envelope command = target \<and>
       verify identity proof target operation call_id payload \<and>
       policy identity target (envelope_asset envelope) operation (proof_epoch proof))"

definition endpoint_call_allowed where
  "endpoint_call_allowed directory policy authenticate verify token proof target operation actor call_id payload source \<longleftrightarrow>
    proof_epoch proof = cut_authority_epoch (envelope_cut (payload_envelope payload)) \<and>
    endpoint_call_identity directory policy authenticate verify token proof target operation actor call_id payload source"

lemma endpoint_call_refines_authenticated_namespace:
  assumes "endpoint_call_allowed directory policy authenticate verify token proof target operation actor call_id payload source"
  shows "\<exists>identity. authenticate token = Some identity \<and>
    directory (fst call_id) = Some identity \<and> identity_principal identity = fst call_id \<and>
    envelope_caller (payload_envelope payload) = fst call_id \<and>
    (\<forall>caller \<in> product_claimed_callers (envelope_command (payload_envelope payload)). caller = fst call_id) \<and>
    verify identity proof target operation call_id payload"
  using assms by (auto simp: endpoint_call_allowed_def endpoint_call_identity_def active_identity_def product_identity_bound_def Let_def)

lemma an_older_signed_request_cannot_use_a_reopened_session:
  assumes "cut_authority_epoch (envelope_cut (payload_envelope payload)) \<noteq>
    cut_authority_epoch (current_product_cut source)"
  shows "\<not> endpoint_call_allowed directory policy authenticate verify token proof target operation actor call_id payload source"
  using assms by (auto simp: endpoint_call_allowed_def endpoint_call_identity_def active_identity_def Let_def)

lemma endpoint_submission_requires_the_specific_capability:
  assumes "endpoint_call_allowed directory policy authenticate verify token proof target operation actor call_id payload source"
  obtains identity where "authenticate token = Some identity"
    "policy identity target (envelope_asset (payload_envelope payload)) operation (proof_epoch proof)"
  using assms by (auto simp: endpoint_call_allowed_def endpoint_call_identity_def Let_def)

definition endpoint_call_allowed_on where
  "endpoint_call_allowed_on (route :: identity_route) = endpoint_call_allowed"

lemma all_entry_routes_share_the_final_call_decision:
  "endpoint_call_allowed_on first = endpoint_call_allowed_on second"
  by (simp add: endpoint_call_allowed_on_def)

lemma endpoint_denial_precedes_effect_and_receipt:
  assumes "\<not> endpoint_call_allowed directory policy authenticate verify token proof target operation actor call_id payload source"
  shows "(if endpoint_call_allowed_on route directory policy authenticate verify token proof target operation actor call_id payload source
       then consume else (source, None)) = (source, None)"
  using assms by (simp add: endpoint_call_allowed_on_def)

end
