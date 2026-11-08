theory Lock_Endpoints
  imports Lock_Finality
begin

section \<open>One credential check at every lock-consuming entry point\<close>

datatype lock_entry = Normal_Lock_Entry | Administrative_Lock_Entry | Adapter_Lock_Entry

definition authoritative_reservation_state :: "product_world \<Rightarrow> reservation_state" where
  "authoritative_reservation_state s = machine_state (core_parent (call_authority_state (product_calls s)))"

definition authoritative_lock_token where
  "authoritative_lock_token s asset =
    (let rs = authoritative_reservation_state s in
      case asset_owner rs asset of None \<Rightarrow> None
      | Some key \<Rightarrow> map_option (\<lambda>r. \<lparr>token_asset = asset,
          token_owner = reservation_worker r, token_generation = reservation_generation r\<rparr>)
          (reservation_at rs key))"

definition authoritative_lock_view where
  "authoritative_lock_view s = s\<lparr>product_durable := (product_durable s)
    \<lparr>product_locks := authoritative_lock_token s\<rparr>\<rparr>"

fun intent_lock_request :: "protocol_intent \<Rightarrow> (execution_request \<times> nat option) option" where
  "intent_lock_request (Reserve_Intent r versions duration) = None"
| "intent_lock_request (Dispatch_Intent r g versions) = Some (r, Some g)"
| "intent_lock_request (Source_Intent r g versions) = Some (r, Some g)"
| "intent_lock_request (Cancel_Intent r g versions) = Some (r, Some g)"
| "intent_lock_request (Fence_Intent r g versions) = Some (r, Some g)"
| "intent_lock_request (Reassign_Intent r duration) = None"
| "intent_lock_request (Write_Intent r g versions value) = Some (r, Some g)"
| "intent_lock_request (Time_Intent elapsed) = None"
| "intent_lock_request (Certificate_Intent cert) = None"
| "intent_lock_request (Deliver_Intent route r) = Some (r, None)"
| "intent_lock_request (Return_Intent r g versions) = Some (r, Some g)"
| "intent_lock_request (Reconcile_Intent r g versions) = Some (r, Some g)"
| "intent_lock_request (Descendant_Intent r root sender recipient amount) = None"
| "intent_lock_request (Data_Read_Intent r) = None"

fun command_lock_request :: "client_command \<Rightarrow> (execution_request \<times> nat option) option" where
  "command_lock_request (Client_Protocol endpoint index intent) = intent_lock_request intent"
| "command_lock_request (Client_Terminal cert) = None"
| "command_lock_request (Client_Regulatory endpoint index r) = None"
| "command_lock_request (Client_Publication key) = None"

definition envelope_matches_binding where
  "envelope_matches_binding envelope b \<longleftrightarrow>
    envelope_origin envelope = binding_key b \<and> envelope_asset envelope = binding_asset b"

definition envelope_matches_request where
  "envelope_matches_request envelope r \<longleftrightarrow>
    envelope_matches_binding envelope (request_binding r) \<and>
    request_authority_epoch r = cut_authority_epoch (envelope_cut envelope)"

fun command_binding_matches where
  "command_binding_matches envelope (Client_Terminal cert) =
    envelope_matches_binding envelope (statement_binding (certificate_statement cert))"
| "command_binding_matches envelope (Client_Protocol endpoint index intent) =
    (case intent of Certificate_Intent cert \<Rightarrow>
      envelope_matches_binding envelope (statement_binding (certificate_statement cert))
    | _ \<Rightarrow> (case intent_request intent of None \<Rightarrow> True
         | Some r \<Rightarrow> envelope_matches_request envelope r))"
| "command_binding_matches envelope (Client_Regulatory endpoint index r) =
    envelope_matches_request envelope r"
| "command_binding_matches envelope (Client_Publication key) = (envelope_origin envelope = key)"

definition lock_credential_matches where
  "lock_credential_matches who credential r generation s \<longleftrightarrow>
    (let token = credential_token credential; rs = authoritative_reservation_state s; b = request_binding r in
      token_asset token = binding_asset b \<and>
      credential_origin credential = binding_key b \<and>
      asset_owner rs (binding_asset b) = Some (binding_key b) \<and>
      (generation = None \<or> generation = Some (token_generation token)) \<and>
      product_lock_admitted who credential (authoritative_lock_view s))"

definition lock_envelope_admitted where
  "lock_envelope_admitted who envelope supplied s \<longleftrightarrow>
    command_binding_matches envelope (envelope_command envelope) \<and>
    (case command_lock_request (envelope_command envelope) of None \<Rightarrow> supplied = None
    | Some (r, g) \<Rightarrow> (case supplied of None \<Rightarrow> False
        | Some credential \<Rightarrow> lock_credential_matches who credential r g s))"

context source_attestation
begin

definition lock_submission_allowed where
  "lock_submission_allowed permitted verified entry who call_id envelope supplied s \<longleftrightarrow>
    permitted entry who (envelope_command envelope) \<and>
    verified who call_id envelope supplied \<and> lock_envelope_admitted who envelope supplied s"

definition submit_lock_entry where
  "submit_lock_entry permitted verified entry who call_id envelope supplied s =
    (if lock_submission_allowed permitted verified entry who call_id envelope supplied s
     then product_submit (\<lambda>_ _ _. True) who call_id envelope s else s)"

lemma every_lock_entry_rejects_missing_credential:
  assumes "command_lock_request (envelope_command envelope) = Some (r,g)"
  shows "submit_lock_entry permitted verified entry who call_id envelope None s = s"
  using assms by (simp add: submit_lock_entry_def lock_submission_allowed_def lock_envelope_admitted_def)

lemma every_lock_entry_checks_current_credential:
  assumes "command_lock_request (envelope_command envelope) = Some (r,g)"
    and "submit_lock_entry permitted verified entry who call_id envelope (Some credential) s \<noteq> s"
  shows "lock_credential_matches who credential r g s"
  using assms by (auto simp: submit_lock_entry_def lock_submission_allowed_def lock_envelope_admitted_def split: if_splits)

lemma every_lock_entry_rejects_older_authority_epoch:
  assumes "credential_epoch old < cut_authority_epoch (current_product_cut s)"
  shows "submit_lock_entry permitted verified entry who call_id envelope (Some old) s = s"
  using assms by (auto simp: submit_lock_entry_def lock_submission_allowed_def lock_envelope_admitted_def lock_credential_matches_def
      product_lock_admitted_def authoritative_lock_view_def current_product_cut_def Let_def
      split: option.splits prod.splits)

lemma every_lock_entry_rejects_replaced_generation:
  assumes "authoritative_lock_token s (token_asset (credential_token old)) = Some replacement"
    and "token_generation (credential_token old) < token_generation replacement"
  shows "submit_lock_entry permitted verified entry who call_id envelope (Some old) s = s"
proof -
  have different: "credential_token old \<noteq> replacement" using assms(2) by auto
  show ?thesis
    using assms(1) different
    by (auto simp: submit_lock_entry_def lock_submission_allowed_def lock_envelope_admitted_def lock_credential_matches_def
        product_lock_admitted_def authoritative_lock_view_def current_lock_token_def Let_def
        split: option.splits prod.splits)
qed

lemma authorized_current_entry_uses_actual_submission:
  assumes "permitted entry who (envelope_command envelope)"
    and "verified who call_id envelope supplied" "lock_envelope_admitted who envelope supplied s"
  shows "submit_lock_entry permitted verified entry who call_id envelope supplied s =
    product_submit (\<lambda>_ _ _. True) who call_id envelope s"
  using assms by (simp add: submit_lock_entry_def lock_submission_allowed_def)

lemma lock_submit_is_public_segment:
  "\<exists>word. product_calls (submit_lock_entry permitted verified entry who call_id envelope supplied s) =
     finality_calls.run_calls word (product_calls s)"
proof (cases "lock_submission_allowed permitted verified entry who call_id envelope supplied s")
  case False
  then show ?thesis by (intro exI[of _ "[]"]) (simp add: submit_lock_entry_def)
next
  case True
  note gate = this
  show ?thesis
  proof (cases "product_new_call who call_id envelope s")
    case True
    then show ?thesis using gate
      by (intro exI[of _ "[Begin_Call call_id (envelope_command envelope), Dispatch_Call call_id (envelope_command envelope)]"])
        (simp add: submit_lock_entry_def product_new_call_uses_authoritative_dispatch)
  next
    case False
    note fresh = this
    show ?thesis
    proof (cases "product_prior_call who call_id envelope s")
      case True
      then show ?thesis using gate
        by (intro exI[of _ "[Collect_Response call_id (envelope_command envelope), Complete_Call call_id]"])
          (simp add: submit_lock_entry_def product_prior_call_uses_authoritative_result_path)
    next
      case False
      then show ?thesis using gate fresh
        by (intro exI[of _ "[]"]) (simp add: submit_lock_entry_def product_submit_def)
    qed
  qed
qed

end

end
