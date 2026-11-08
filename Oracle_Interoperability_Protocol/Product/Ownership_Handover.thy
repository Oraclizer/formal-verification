theory Ownership_Handover
  imports Identity_Reads
begin

section \<open>One authoritative owner with atomic session replacement\<close>

record ownership_transfer =
  transfer_asset :: product_asset
  transfer_previous :: product_principal
  transfer_successor :: product_principal
  transfer_expected :: product_cut
  transfer_old_session :: product_session_id
  transfer_new_session :: product_session_id
  transfer_epoch :: nat
  transfer_contexts :: "(nat \<times> lock_context) list"

definition handover_sessions where
  "handover_sessions proposal old session =
    (if session = transfer_old_session proposal then None
     else if session = transfer_new_session proposal then
       Some \<lparr>session_principal = transfer_successor proposal, session_epoch = transfer_epoch proposal\<rparr>
     else map_option (\<lambda>binding. binding\<lparr>session_epoch := transfer_epoch proposal\<rparr>) (old session))"

definition owner_of_product where
  "owner_of_product source = product_owners (product_durable source)"

definition handover_is_authorized where
  "handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal source \<longleftrightarrow>
    (let old = transfer_previous proposal; successor = transfer_successor proposal; asset = transfer_asset proposal;
         actual = current_product_cut source; sessions = product_sessions (product_durable source);
         old_proof = \<lparr>proof_session = transfer_old_session proposal, proof_epoch = cut_authority_epoch actual\<rparr>
     in old \<noteq> successor \<and> owner_of_product source asset = Some old \<and> transfer_expected proposal = actual \<and>
        transfer_old_session proposal \<noteq> transfer_new_session proposal \<and> sessions (transfer_new_session proposal) = None \<and>
        maintainer \<in> maintainers \<and>
        lock_context_batch_is_newer registered (transfer_epoch proposal) (transfer_contexts proposal) source \<and>
        call_local_status (product_calls source) = Endpoint_Up \<and> call_connection (product_calls source) = Authority_Connected \<and>
        (\<exists>former incoming. authenticate owner_token = Some former \<and> authenticate successor_token = Some incoming \<and>
          identity_principal former = old \<and> identity_principal incoming = successor \<and>
          active_identity directory former old_proof source \<and> directory successor = Some incoming \<and>
          policy former (identity_domain former) asset Transfer_Ownership (cut_authority_epoch actual) \<and>
          approve former proposal \<and> approve incoming proposal))"

definition recoverable_reservation where
  "recoverable_reservation source key =
    (case reservation_at (authoritative_reservation_state source) key of None \<Rightarrow> None
     | Some claim \<Rightarrow> if active_reservation_phase (reservation_phase claim) then Some claim else None)"

definition recovery_controller where
  "recovery_controller source key =
    Option.bind (recoverable_reservation source key) (owner_of_product source \<circ> binding_asset \<circ> reservation_binding)"

context source_attestation
begin

definition apply_owner_handover where
  "apply_owner_handover directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal source =
    (if handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal source
     then let prepared = lock_product_step (\<lambda>_ _ _. False) (\<lambda>_ _ _ _. False) maintainers registered
        (Lock_Install maintainer (transfer_epoch proposal) (transfer_contexts proposal)
          (handover_sessions proposal (product_sessions (product_durable source)))) source
     in prepared\<lparr>product_durable := (product_durable prepared)\<lparr>product_owners :=
          (owner_of_product source)(transfer_asset proposal := Some (transfer_successor proposal))\<rparr>\<rparr>
     else source)"

lemma denied_handover_has_no_partial_write:
  assumes "\<not> handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal source"
  shows "apply_owner_handover directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal source = source"
  using assms by (simp add: apply_owner_handover_def)

lemma installing_contexts_keeps_the_entire_reservation_machine:
  "core_parent (call_authority_state (finality_calls.run_calls (map Apply_Authority_Input changes) calls)) =
   core_parent (call_authority_state calls)"
  by (induction changes arbitrary: calls)
    (simp_all add: finality_calls.apply_authority_input_def execute_finality_environment_def finality_step_def Let_def split: if_splits)

theorem handover_atomically_changes_owner_and_sessions_without_spending:
  fixes directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal source updated
  assumes admit: "handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal source"
  defines "updated \<equiv> apply_owner_handover directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal source"
  shows "owner_of_product updated = (owner_of_product source)(transfer_asset proposal := Some (transfer_successor proposal))"
    "product_sessions (product_durable updated) (transfer_old_session proposal) = None"
    "product_sessions (product_durable updated) (transfer_new_session proposal) =
      Some \<lparr>session_principal = transfer_successor proposal, session_epoch = transfer_epoch proposal\<rparr>"
    "cut_authority_epoch (current_product_cut updated) = transfer_epoch proposal"
    "authoritative_reservation_state updated = authoritative_reservation_state source"
proof -
  have gate: "maintainer \<in> maintainers"
    "lock_context_batch_is_newer registered (transfer_epoch proposal) (transfer_contexts proposal) source"
    "transfer_old_session proposal \<noteq> transfer_new_session proposal"
    using admit by (simp_all add: handover_is_authorized_def Let_def)
  show "owner_of_product updated = (owner_of_product source)(transfer_asset proposal := Some (transfer_successor proposal))"
    "product_sessions (product_durable updated) (transfer_old_session proposal) = None"
    "product_sessions (product_durable updated) (transfer_new_session proposal) =
      Some \<lparr>session_principal = transfer_successor proposal, session_epoch = transfer_epoch proposal\<rparr>"
    "cut_authority_epoch (current_product_cut updated) = transfer_epoch proposal"
    "authoritative_reservation_state updated = authoritative_reservation_state source"
    using admit gate
    by (simp_all add: updated_def apply_owner_handover_def handover_sessions_def owner_of_product_def
        authoritative_reservation_state_def current_product_cut_def product_apply_public_def
        installing_contexts_keeps_the_entire_reservation_machine Let_def)
qed

theorem accepted_handover_transfers_exactly_the_live_claims:
  fixes directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal source updated
  assumes admit: "handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal source"
  defines "updated \<equiv> apply_owner_handover directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal source"
  shows "recoverable_reservation updated key = recoverable_reservation source key"
    "recovery_controller updated key =
      (case recoverable_reservation source key of None \<Rightarrow> None
       | Some claim \<Rightarrow> if binding_asset (reservation_binding claim) = transfer_asset proposal
         then Some (transfer_successor proposal) else recovery_controller source key)"
proof -
  have preserved: "authoritative_reservation_state updated = authoritative_reservation_state source"
    unfolding updated_def by (rule handover_atomically_changes_owner_and_sessions_without_spending(5)[OF admit])
  then show same: "recoverable_reservation updated key = recoverable_reservation source key"
    by (simp add: recoverable_reservation_def)
  have owner: "owner_of_product updated = (owner_of_product source)(transfer_asset proposal := Some (transfer_successor proposal))"
    unfolding updated_def by (rule handover_atomically_changes_owner_and_sessions_without_spending(1)[OF admit])
  show "recovery_controller updated key =
      (case recoverable_reservation source key of None \<Rightarrow> None
       | Some claim \<Rightarrow> if binding_asset (reservation_binding claim) = transfer_asset proposal
         then Some (transfer_successor proposal) else recovery_controller source key)"
    by (cases "recoverable_reservation source key") (simp_all add: recovery_controller_def same owner)
qed

end

end
