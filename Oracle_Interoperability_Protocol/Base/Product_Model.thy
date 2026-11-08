theory Product_Model
  imports "Evidence_Atomic_Binding.Finality_Refinement"
    "Evidence_Atomic_Binding.Finality_Recovery"
begin

section \<open>Product state and authoritative observations\<close>

type_synonym product_asset = nat
type_synonym product_principal = nat
type_synonym product_session_id = nat
type_synonym product_message_id = nat

type_synonym product_call_machine =
  "(finality_core, client_command, finality_reply, nat \<times> lock_context) durable_call_machine"
type_synonym product_public_action = "(client_command, nat \<times> lock_context) client_call_action"

record product_session_binding =
  session_principal :: product_principal
  session_epoch :: nat

record product_cut =
  cut_authority_epoch :: nat
  cut_revision :: nat

record product_envelope =
  envelope_message :: product_message_id
  envelope_origin :: source_key
  envelope_asset :: product_asset
  envelope_caller :: product_principal
  envelope_session :: product_session_id
  envelope_cut :: product_cut
  envelope_command :: client_command

record product_lock_token =
  token_asset :: product_asset
  token_owner :: product_principal
  token_generation :: nat

record product_durable =
  product_authority_epoch :: nat
  product_owners :: "product_asset \<Rightarrow> product_principal option"
  product_sessions :: "product_session_id \<Rightarrow> product_session_binding option"
  product_locks :: "product_asset \<Rightarrow> product_lock_token option"
  product_requests :: "client_call_id \<Rightarrow> product_envelope option"

record product_world =
  product_durable :: product_durable
  product_calls :: product_call_machine

definition current_product_cut :: "product_world \<Rightarrow> product_cut" where
  "current_product_cut s = \<lparr>cut_authority_epoch = product_authority_epoch (product_durable s),
    cut_revision = length (call_authority_log (product_calls s))\<rparr>"

text \<open>
  The public core sequence number advances even on ordinary calls. The product
  authority epoch belongs to the durable authorization context and is separate
  from that sequence number and the revision of the public authority log.
\<close>

definition current_lock_token :: "product_world \<Rightarrow> product_lock_token \<Rightarrow> bool" where
  "current_lock_token s token \<longleftrightarrow>
    product_locks (product_durable s) (token_asset token) = Some token"

text \<open>
  The public financial projection leaves out authoritative results. The product
  snapshot retains those results and the other durable inputs used by the next
  call. The public call history remains in the world because the completion
  consumer checks its invocation position. Endpoint status and local responses
  are runtime data. A snapshot is not itself evidence of authenticity.
\<close>

definition product_durable_snapshot where
  "product_durable_snapshot s = (product_durable s, call_genesis (product_calls s),
    call_authority_state (product_calls s), call_authority_log (product_calls s),
    call_authority_results (product_calls s), call_invocations (product_calls s),
    call_completions (product_calls s))"

section \<open>Admission and execution over the public machine\<close>

fun product_claimed_callers :: "client_command \<Rightarrow> product_principal set" where
  "product_claimed_callers (Client_Terminal cert) = {}"
| "product_claimed_callers (Client_Protocol endpoint index intent) =
    (case intent_request intent of None \<Rightarrow> {} | Some r \<Rightarrow> {request_caller r})"
| "product_claimed_callers (Client_Regulatory endpoint index r) = {request_caller r}"
| "product_claimed_callers (Client_Publication key) = {}"

definition product_identity_bound where
  "product_identity_bound who call_id envelope s \<longleftrightarrow>
    fst call_id = who \<and> envelope_caller envelope = who \<and>
    (\<forall>caller \<in> product_claimed_callers (envelope_command envelope). caller = who) \<and>
    product_sessions (product_durable s) (envelope_session envelope) =
      Some \<lparr>session_principal = who, session_epoch = cut_authority_epoch (current_product_cut s)\<rparr>"

definition product_new_call where
  "product_new_call who call_id envelope s \<longleftrightarrow>
    product_identity_bound who call_id envelope s \<and> envelope_cut envelope = current_product_cut s \<and>
    product_requests (product_durable s) call_id = None \<and>
    call_invocations (product_calls s) call_id = None \<and>
    call_authority_results (product_calls s) call_id = None \<and>
    call_local_status (product_calls s) = Endpoint_Up \<and>
    call_connection (product_calls s) = Authority_Connected"

definition product_prior_call where
  "product_prior_call who call_id envelope s \<longleftrightarrow>
    product_identity_bound who call_id envelope s \<and>
    product_requests (product_durable s) call_id = Some envelope"

text \<open>
  The authenticated identity and verification of the signed envelope belong to
  the entry point. The supplied predicate covers the entire typed envelope and
  call identifier. Later layers supply authority, wire and storage consumers.
  In particular, this entry boundary leaves recovery authentication to its
  caller and provides no independent result for a disconnected authority.
\<close>

context source_attestation
begin

definition product_apply_public :: "product_public_action list \<Rightarrow> product_world \<Rightarrow> product_world" where
  "product_apply_public actions s = s\<lparr>product_calls := finality_calls.run_calls actions (product_calls s)\<rparr>"

definition product_submit where
  "product_submit verified who call_id envelope s =
    (if verified who call_id envelope then
      if product_new_call who call_id envelope s then
        (product_apply_public [Begin_Call call_id (envelope_command envelope),
          Dispatch_Call call_id (envelope_command envelope)] s)\<lparr>product_durable :=
            (product_durable s)\<lparr>product_requests := (product_requests (product_durable s))(call_id := Some envelope)\<rparr>\<rparr>
      else if product_prior_call who call_id envelope s then
        product_apply_public [Collect_Response call_id (envelope_command envelope), Complete_Call call_id] s
      else s
    else s)"

definition product_crash :: "product_world \<Rightarrow> product_world" where
  "product_crash s = product_apply_public [Crash_Local_Endpoint] s"

definition product_restart where
  "product_restart checked_snapshot s =
    (if checked_snapshot = Some (product_durable_snapshot s) \<and>
        call_local_status (product_calls s) = Endpoint_Down \<and>
        call_connection (product_calls s) = Authority_Connected
     then product_apply_public [Recover_Local_Endpoint] s else s)"

lemma product_rejects_unbound_identity:
  "\<not> product_identity_bound who call_id envelope s \<Longrightarrow> product_submit verified who call_id envelope s = s"
  by (simp add: product_submit_def product_new_call_def product_prior_call_def)

lemma product_rejects_unverified_envelope:
  "\<not> verified who call_id envelope \<Longrightarrow> product_submit verified who call_id envelope s = s"
  by (simp add: product_submit_def)

lemma product_crash_keeps_snapshot:
  "product_durable_snapshot (product_crash s) = product_durable_snapshot s"
  by (simp add: product_crash_def product_apply_public_def product_durable_snapshot_def)

lemma product_crash_clears_cached_results:
  "call_local_results (product_calls (product_crash s)) call_id = None"
  by (simp add: product_crash_def product_apply_public_def)

lemma product_restart_rejects_wrong_snapshot:
  "checked_snapshot \<noteq> Some (product_durable_snapshot s) \<Longrightarrow> product_restart checked_snapshot s = s"
  by (simp add: product_restart_def)

lemma product_restart_requires_connected_authority:
  "call_connection (product_calls s) = Authority_Disconnected \<Longrightarrow> product_restart checked_snapshot s = s"
  by (simp add: product_restart_def)

lemma product_restart_from_durable_state:
  assumes "call_connection (product_calls s) = Authority_Connected"
  shows "call_local_status (product_calls (product_restart (Some (product_durable_snapshot s)) (product_crash s))) = Endpoint_Up \<and>
    product_durable_snapshot (product_restart (Some (product_durable_snapshot s)) (product_crash s)) = product_durable_snapshot s"
  using assms by (simp add: product_restart_def product_crash_def product_apply_public_def product_durable_snapshot_def)

lemma product_prior_call_uses_authoritative_result_path:
  assumes "verified who call_id envelope" "product_prior_call who call_id envelope s"
  shows "product_calls (product_submit verified who call_id envelope s) =
    finality_calls.run_calls [Collect_Response call_id (envelope_command envelope), Complete_Call call_id] (product_calls s)"
  using assms by (simp add: product_submit_def product_prior_call_def product_new_call_def product_apply_public_def)

lemma product_new_call_uses_authoritative_dispatch:
  assumes "verified who call_id envelope" "product_new_call who call_id envelope s"
  shows "product_calls (product_submit verified who call_id envelope s) =
    finality_calls.run_calls [Begin_Call call_id (envelope_command envelope),
      Dispatch_Call call_id (envelope_command envelope)] (product_calls s)"
  using assms by (simp add: product_submit_def product_apply_public_def)

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    source_attestation.product_rejects_unbound_identity
    source_attestation.product_rejects_unverified_envelope
    source_attestation.product_crash_keeps_snapshot
    source_attestation.product_crash_clears_cached_results
    source_attestation.product_restart_rejects_wrong_snapshot
    source_attestation.product_restart_requires_connected_authority
    source_attestation.product_restart_from_durable_state
    source_attestation.product_prior_call_uses_authoritative_result_path
    source_attestation.product_new_call_uses_authoritative_dispatch})
  then () else error "Unexpected oracle in product model"
\<close>

end
