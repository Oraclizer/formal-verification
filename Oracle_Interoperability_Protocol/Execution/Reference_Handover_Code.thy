theory Reference_Handover_Code
  imports "OIP_Reference_Profile.Reference_Handover_Consumption"
begin

definition native_replace_handover_sessions where
  "native_replace_handover_sessions proposal current =
    (if transfer_old_session proposal = transfer_new_session proposal \<or>
        current (transfer_new_session proposal) \<noteq> None \<or> current (transfer_old_session proposal) = None
     then None else
       let remaining = current(transfer_old_session proposal := None);
           updated = (\<lambda>session. map_option (\<lambda>binding.
             binding\<lparr>session_epoch := transfer_epoch proposal\<rparr>) (remaining session))
       in Some (updated(transfer_new_session proposal :=
            Some \<lparr>session_principal = transfer_successor proposal, session_epoch = transfer_epoch proposal\<rparr>)))"

lemma native_handover_sessions_match_the_product_sessions:
  assumes distinct: "transfer_old_session proposal \<noteq> transfer_new_session proposal"
    and old: "current (transfer_old_session proposal) \<noteq> None"
    and vacant: "current (transfer_new_session proposal) = None"
  shows "native_replace_handover_sessions proposal current = Some (handover_sessions proposal current)"
  using assms by (auto simp: native_replace_handover_sessions_def handover_sessions_def Let_def fun_eq_iff)

definition native_handover_observation where
  "native_handover_observation admitted installed proposal owners sessions reservation_state =
    (if \<not> admitted \<or> \<not> installed then None
     else map_option (\<lambda>updated.
        (owners(transfer_asset proposal := Some (transfer_successor proposal)),
          updated, transfer_epoch proposal, reservation_state))
       (native_replace_handover_sessions proposal sessions))"

record 'ledger rust_handover_image =
  rust_handover_owner :: "product_asset \<Rightarrow> product_principal option"
  rust_handover_sessions :: "product_session_id \<Rightarrow> product_session_binding option"
  rust_handover_epoch :: nat
  rust_handover_ledger :: 'ledger

definition rust_handover_matches where
  "rust_handover_matches related code source \<longleftrightarrow>
    rust_handover_owner code = owner_of_product source \<and>
    rust_handover_sessions code = product_sessions (product_durable source) \<and>
    rust_handover_epoch code = cut_authority_epoch (current_product_cut source) \<and>
    related (rust_handover_ledger code) (authoritative_reservation_state source)"

definition rust_handover_step where
  "rust_handover_step external approved proposal code =
    (if \<not> external \<or> \<not> approved \<or>
      rust_handover_owner code (transfer_asset proposal) \<noteq> Some (transfer_previous proposal) \<or>
      rust_handover_sessions code (transfer_old_session proposal) \<noteq> Some
        \<lparr>session_principal = transfer_previous proposal, session_epoch = rust_handover_epoch code\<rparr>
     then (code, False)
     else case native_replace_handover_sessions proposal (rust_handover_sessions code) of None \<Rightarrow> (code, False)
     | Some updated \<Rightarrow>
       (code\<lparr>rust_handover_owner := (rust_handover_owner code)(transfer_asset proposal := Some (transfer_successor proposal)),
             rust_handover_sessions := updated, rust_handover_epoch := transfer_epoch proposal\<rparr>, True))"

context source_attestation
begin

theorem a_native_handover_write_matches_owner_sessions_epoch_and_reservations:
  assumes admitted: "handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer
      maintainers registered proposal source"
  shows "let next = apply_owner_handover directory policy authenticate approve owner_token successor_token
           maintainer maintainers registered proposal source
    in native_handover_observation True True proposal (owner_of_product source)
         (product_sessions (product_durable source)) (authoritative_reservation_state source) =
       Some (owner_of_product next, product_sessions (product_durable next),
         cut_authority_epoch (current_product_cut next), authoritative_reservation_state next)"
proof -
  let ?sessions = "product_sessions (product_durable source)"
  let ?next = "apply_owner_handover directory policy authenticate approve owner_token successor_token
           maintainer maintainers registered proposal source"
  have distinct: "transfer_old_session proposal \<noteq> transfer_new_session proposal"
    and vacant: "?sessions (transfer_new_session proposal) = None"
    and maintainer: "maintainer \<in> maintainers"
    and batch: "lock_context_batch_is_newer registered (transfer_epoch proposal) (transfer_contexts proposal) source"
    using admitted by (simp_all add: handover_is_authorized_def Let_def)
  have old: "?sessions (transfer_old_session proposal) \<noteq> None"
    using admitted by (auto simp: handover_is_authorized_def active_identity_def Let_def)
  have session_map: "product_sessions (product_durable ?next) = handover_sessions proposal ?sessions"
    using admitted maintainer batch by (simp add: apply_owner_handover_def Let_def)
  note exact = handover_atomically_changes_owner_and_sessions_without_spending[OF admitted]
  show ?thesis using native_handover_sessions_match_the_product_sessions[OF distinct old vacant]
    exact(1,4,5) session_map by (simp add: native_handover_observation_def Let_def)
qed

lemma a_handover_without_either_approval_never_produces_a_native_write:
  "native_handover_observation False installed proposal owners sessions reservation_state = None"
  by (simp add: native_handover_observation_def)

theorem the_signed_rust_handover_preserves_related_reservations_and_returns_the_model_decision:
  assumes initial: "rust_handover_matches related code source"
    and admitted: "handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer
      maintainers registered proposal source"
    and policy_ready: "next_policy_valid"
  shows "let native = rust_handover_step True next_policy_valid proposal code;
       after = apply_owner_handover directory policy authenticate approve owner_token successor_token maintainer
         maintainers registered proposal source
    in rust_handover_matches related (fst native) after \<and> snd native = (after \<noteq> source)"
proof -
  let ?sessions = "product_sessions (product_durable source)"
  let ?after = "apply_owner_handover directory policy authenticate approve owner_token successor_token
     maintainer maintainers registered proposal source"
  have distinct: "transfer_old_session proposal \<noteq> transfer_new_session proposal"
    and vacant: "?sessions (transfer_new_session proposal) = None"
    and current: "owner_of_product source (transfer_asset proposal) = Some (transfer_previous proposal)"
    and maintenance: "maintainer \<in> maintainers"
    and batch: "lock_context_batch_is_newer registered (transfer_epoch proposal) (transfer_contexts proposal) source"
    using admitted by (simp_all add: handover_is_authorized_def Let_def)
  have old: "?sessions (transfer_old_session proposal) = Some \<lparr>session_principal = transfer_previous proposal,
      session_epoch = cut_authority_epoch (current_product_cut source)\<rparr>"
    using admitted by (auto simp: handover_is_authorized_def active_identity_def Let_def)
  have session_map: "product_sessions (product_durable ?after) = handover_sessions proposal ?sessions"
    using admitted maintenance batch by (simp add: apply_owner_handover_def Let_def)
  have occupied: "?sessions (transfer_old_session proposal) \<noteq> None" using old by simp
  have replacement: "native_replace_handover_sessions proposal ?sessions = Some (handover_sessions proposal ?sessions)"
    by (rule native_handover_sessions_match_the_product_sessions[OF distinct occupied vacant])
  note effect = handover_atomically_changes_owner_and_sessions_without_spending[OF admitted]
  have changed: "?after \<noteq> source" using old effect(2) by auto
  show ?thesis using initial policy_ready old current replacement session_map effect(1,4,5) changed
    by (simp add: rust_handover_step_def rust_handover_matches_def Let_def)
qed

lemma missing_ready_successor_policy_is_a_rust_refusal_with_no_state_change:
  "rust_handover_step external False proposal code = (code, False)"
  by (simp add: rust_handover_step_def)

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms native_handover_sessions_match_the_product_sessions
      source_attestation.a_native_handover_write_matches_owner_sessions_epoch_and_reservations
      source_attestation.the_signed_rust_handover_preserves_related_reservations_and_returns_the_model_decision
      source_attestation.missing_ready_successor_policy_is_a_rust_refusal_with_no_state_change
      source_attestation.a_handover_without_either_approval_never_produces_a_native_write})
  then () else error "Unexpected oracle in native handover code correspondence"
\<close>

end
