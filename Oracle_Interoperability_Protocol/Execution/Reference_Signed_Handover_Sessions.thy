theory Reference_Signed_Handover_Sessions
  imports Reference_Signed_Handover_Code
begin

definition rust_successor_session_owners where
  "rust_successor_session_owners successor session =
     {principal. session \<in> rust_policy_sessions successor principal}"

definition rust_bind_all_successor_sessions where
  "rust_bind_all_successor_sessions successor installed =
    (if \<forall>session binding. installed session = Some binding \<longrightarrow>
         session_epoch binding = rust_policy_epoch successor \<and>
         rust_successor_session_owners successor session = {session_principal binding}
     then Some (rust_policy_fingerprint successor) else None)"

definition rust_checked_handover_step where
  "rust_checked_handover_step admitted ready successor proposal code =
    (let installed = native_replace_handover_sessions proposal (rust_handover_sessions code);
         bound = (case installed of None \<Rightarrow> False
           | Some sessions \<Rightarrow> rust_bind_all_successor_sessions successor sessions =
                Some (rust_policy_fingerprint successor))
     in rust_handover_step admitted (ready \<and> bound) proposal code)"

lemma every_selected_ledger_session_has_exactly_its_next_principal:
  assumes bound: "rust_bind_all_successor_sessions successor installed = Some fingerprint"
    and stored: "installed session = Some binding"
  shows "fingerprint = rust_policy_fingerprint successor"
    "session_epoch binding = rust_policy_epoch successor"
    "rust_successor_session_owners successor session = {session_principal binding}"
  using bound stored by (auto simp: rust_bind_all_successor_sessions_def split: if_splits)

lemma an_unregistered_or_multiply_registered_surviving_session_refuses_the_install:
  assumes stored: "installed session = Some binding"
    and invalid: "session_epoch binding \<noteq> rust_policy_epoch successor \<or>
      rust_successor_session_owners successor session \<noteq> {session_principal binding}"
  shows "rust_bind_all_successor_sessions successor installed = None"
  using stored invalid by (auto simp: rust_bind_all_successor_sessions_def)

lemma the_checked_handover_refuses_an_invalid_surviving_session_before_any_write:
  assumes replaced: "native_replace_handover_sessions proposal (rust_handover_sessions code) = Some installed"
    and stored: "installed session = Some binding"
    and invalid: "session_epoch binding \<noteq> rust_policy_epoch successor \<or>
      rust_successor_session_owners successor session \<noteq> {session_principal binding}"
  shows "rust_checked_handover_step admitted ready successor proposal code = (code,False)"
proof -
  have refusal: "rust_bind_all_successor_sessions successor installed = None"
    by (rule an_unregistered_or_multiply_registered_surviving_session_refuses_the_install
      [where installed=installed and session=session and binding=binding and successor=successor, OF stored invalid])
  show ?thesis using refusal replaced
    by (simp add: rust_checked_handover_step_def rust_handover_step_def Let_def)
qed

context source_attestation
begin

theorem the_signed_handover_with_the_full_session_install_guard_matches_the_model_state_and_response:
  fixes approve ready admitted installed_ok
    verify current successor former incoming readiness proposal control code directory policy authenticate owner_token successor_token
    maintainer maintainers registered source
  defines "approve \<equiv> rust_handover_consent verify current successor former incoming"
    and "ready \<equiv> rust_register_next_policy verify readiness current successor = Some successor \<and>
         rust_current_policy_for_handover current successor proposal \<and>
         transfer_successor proposal \<notin> control_revoked control"
    and "admitted \<equiv> rust_handover_ledger_gate directory policy authenticate approve owner_token successor_token maintainer maintainers
        (lock_context_batch_is_newer registered (transfer_epoch proposal) (transfer_contexts proposal) source)
        (current_product_cut source) (call_local_status (product_calls source) = Endpoint_Up)
        (call_connection (product_calls source) = Authority_Connected) proposal code"
    and "installed_ok \<equiv> (case native_replace_handover_sessions proposal (rust_handover_sessions code) of None \<Rightarrow> False
         | Some sessions \<Rightarrow> rust_bind_all_successor_sessions successor sessions =
             Some (rust_policy_fingerprint successor))"
  assumes initial: "rust_handover_matches relate code source"
  shows "let (native,changed) = rust_checked_handover_step admitted ready successor proposal code;
       model = (if ready \<and> installed_ok
          then apply_owner_handover directory policy authenticate approve owner_token successor_token maintainer
             maintainers registered proposal source else source);
       selected = (if changed then rust_policy_fingerprint successor else rust_policy_fingerprint current)
     in rust_handover_matches relate native model \<and> changed = (model \<noteq> source) \<and>
       selected = (if model \<noteq> source then rust_policy_fingerprint successor else rust_policy_fingerprint current)"
proof -
  have gate: "admitted = handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer
        maintainers registered proposal source"
    using initial by (auto simp: admitted_def rust_handover_ledger_gate_def rust_handover_matches_def
      handover_is_authorized_def active_identity_def Let_def)
  have native: "rust_checked_handover_step admitted ready successor proposal code =
      rust_handover_step admitted (ready \<and> installed_ok) proposal code"
    by (simp add: rust_checked_handover_step_def installed_ok_def Let_def)
  show ?thesis
  proof (cases "ready \<and> installed_ok")
    case True
    note installed_now = True
    show ?thesis
    proof (cases admitted)
      case True
      then have authorized: "handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer
          maintainers registered proposal source" using gate by simp
      note correspondence = the_signed_rust_handover_preserves_related_reservations_and_returns_the_model_decision
        [OF initial authorized installed_now]
      show ?thesis unfolding native using correspondence by (simp add: True installed_now Let_def case_prod_beta)
    next
      case False
      then have denied: "\<not> handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer
          maintainers registered proposal source" using gate by simp
      have unchanged: "apply_owner_handover directory policy authenticate approve owner_token successor_token maintainer
          maintainers registered proposal source = source"
        by (rule denied_handover_has_no_partial_write[OF denied])
      show ?thesis unfolding native using initial by (simp add: False installed_now unchanged rust_handover_step_def Let_def)
    qed
  next
    case False
    show ?thesis unfolding native using initial by (simp add: False rust_handover_step_def Let_def)
  qed
qed

theorem removing_the_full_session_guard_can_change_the_decision_for_the_same_related_handover:
  fixes maintainer :: nat
    and maintainers registered :: "nat set"
    and proposal :: ownership_transfer
  assumes initial: "rust_handover_matches relate code source"
    and authorized: "handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer
        maintainers registered proposal source"
    and replaced: "native_replace_handover_sessions proposal (rust_handover_sessions code) = Some installed"
    and stored: "installed session = Some binding"
    and invalid: "session_epoch binding \<noteq> rust_policy_epoch successor \<or>
        rust_successor_session_owners successor session \<noteq> {session_principal binding}"
  shows "snd (rust_handover_step True True proposal code)"
    "rust_checked_handover_step True True successor proposal code = (code,False)"
proof -
  note related = the_signed_rust_handover_preserves_related_reservations_and_returns_the_model_decision
    [OF initial authorized TrueI]
  note changed = handover_atomically_changes_owner_and_sessions_without_spending[OF authorized]
  have old: "product_sessions (product_durable source) (transfer_old_session proposal) \<noteq> None"
    using authorized by (auto simp: handover_is_authorized_def active_identity_def Let_def)
  have differs: "apply_owner_handover directory policy authenticate approve owner_token successor_token maintainer
      maintainers registered proposal source \<noteq> source" using old changed(2) by auto
  show "snd (rust_handover_step True True proposal code)" using related differs by (simp add: Let_def)
  show "rust_checked_handover_step True True successor proposal code = (code,False)"
    by (rule the_checked_handover_refuses_an_invalid_surviving_session_before_any_write
      [where installed=installed and session=session and binding=binding and successor=successor, OF replaced stored invalid])
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms every_selected_ledger_session_has_exactly_its_next_principal
    an_unregistered_or_multiply_registered_surviving_session_refuses_the_install
    the_checked_handover_refuses_an_invalid_surviving_session_before_any_write
    source_attestation.the_signed_handover_with_the_full_session_install_guard_matches_the_model_state_and_response
    source_attestation.removing_the_full_session_guard_can_change_the_decision_for_the_same_related_handover})
  then () else error "Unexpected oracle in complete successor session binding"
\<close>

end
