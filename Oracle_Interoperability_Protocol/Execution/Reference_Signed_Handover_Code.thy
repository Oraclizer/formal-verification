theory Reference_Signed_Handover_Code
  imports Reference_Handover_Code "OIP_Reference_Profile.Reference_Handover_Provider" "OIP_Reference_Profile.Reference_Ordered_Control"
begin

record rust_handover_policy =
  rust_policy_profile :: recovery_profile
  rust_policy_fingerprint :: wire_bytes
  rust_policy_epoch :: nat
  rust_policy_response_key :: wire_bytes
  rust_policy_sources :: wire_bytes
  rust_policy_contexts :: "(nat \<times> lock_context) list"
  rust_policy_identities :: "nat \<Rightarrow> registered_identity option"
  rust_policy_keys :: "nat \<Rightarrow> wire_bytes option"
  rust_policy_sessions :: "nat \<Rightarrow> nat set"

datatype rust_handover_signed =
  Rust_Successor_Readiness recovery_profile wire_bytes wire_bytes "(nat \<times> lock_context) list"
  | Rust_Handover_Consent recovery_profile wire_bytes wire_bytes nat registered_identity ownership_transfer

definition native_readiness_preimage where
  "native_readiness_preimage current successor = Rust_Successor_Readiness (rust_policy_profile current)
      (rust_policy_fingerprint current) (rust_policy_fingerprint successor) (rust_policy_contexts successor)"

definition rust_register_next_policy where
  "rust_register_next_policy verify signature current successor =
    (if rust_policy_profile successor = rust_policy_profile current \<and>
        rust_policy_epoch current < rust_policy_epoch successor \<and> rust_policy_sources successor = rust_policy_sources current \<and>
        rust_policy_contexts successor \<noteq> [] \<and> sorted_wrt (<) (map fst (rust_policy_contexts successor)) \<and>
        (\<forall>(endpoint,ctx) \<in> set (rust_policy_contexts successor). context_authority_epoch (lock_authority ctx) = rust_policy_epoch successor) \<and>
        (\<forall>principal identity. rust_policy_identities successor principal = Some identity \<longrightarrow>
          rust_policy_identities current principal = Some identity) \<and>
        verify (rust_policy_response_key successor) (native_readiness_preimage current successor) signature
     then Some successor else None)"

definition rust_current_policy_for_handover where
  "rust_current_policy_for_handover current successor proposal \<longleftrightarrow>
    cut_authority_epoch (transfer_expected proposal) = rust_policy_epoch current \<and>
    transfer_epoch proposal = rust_policy_epoch successor \<and> transfer_contexts proposal = rust_policy_contexts successor \<and>
    transfer_previous proposal \<noteq> transfer_successor proposal \<and>
    transfer_new_session proposal \<in> rust_policy_sessions successor (transfer_successor proposal) \<and>
    transfer_old_session proposal \<notin> rust_policy_sessions successor (transfer_previous proposal)"

definition rust_handover_consent where
  "rust_handover_consent verify current successor former incoming identity proposal \<longleftrightarrow>
    (let principal = identity_principal identity in
     rust_policy_identities current principal = Some identity \<and>
     (\<exists>key. rust_policy_keys current principal = Some key \<and>
       (if principal = transfer_previous proposal then
          verify key (Rust_Handover_Consent (rust_policy_profile current) (rust_policy_fingerprint current)
            (rust_policy_fingerprint successor) 1 identity proposal) former
        else principal = transfer_successor proposal \<and>
          verify key (Rust_Handover_Consent (rust_policy_profile current) (rust_policy_fingerprint current)
            (rust_policy_fingerprint successor) 2 identity proposal) incoming)))"

definition rust_handover_ledger_gate where
  "rust_handover_ledger_gate directory policy authenticate approve owner_token successor_token maintainer maintainers installed
      current_cut online connected proposal code \<longleftrightarrow>
    (let previous = transfer_previous proposal; successor = transfer_successor proposal; asset = transfer_asset proposal;
         epoch = rust_handover_epoch code; sessions = rust_handover_sessions code in
     previous \<noteq> successor \<and> rust_handover_owner code asset = Some previous \<and> transfer_expected proposal = current_cut \<and>
     transfer_old_session proposal \<noteq> transfer_new_session proposal \<and> sessions (transfer_new_session proposal) = None \<and>
     maintainer \<in> maintainers \<and> installed \<and> online \<and> connected \<and>
     (\<exists>former incoming. authenticate owner_token = Some former \<and> authenticate successor_token = Some incoming \<and>
        identity_principal former = previous \<and> identity_principal incoming = successor \<and>
        directory previous = Some former \<and> directory successor = Some incoming \<and>
        sessions (transfer_old_session proposal) = Some \<lparr>session_principal = previous,session_epoch = epoch\<rparr> \<and>
        policy former (identity_domain former) asset Transfer_Ownership epoch \<and> approve former proposal \<and> approve incoming proposal))"

lemma a_next_signature_for_another_policy_does_not_bind_the_selected_readiness_preimage:
  assumes "rust_policy_fingerprint first \<noteq> rust_policy_fingerprint second"
  shows "native_readiness_preimage current first \<noteq> native_readiness_preimage current second"
  using assms by (simp add: native_readiness_preimage_def)

lemma a_wrong_detached_owner_signature_cannot_supply_the_native_consent:
  assumes owner: "identity_principal identity = transfer_previous proposal"
    and key: "rust_policy_keys current (transfer_previous proposal) = Some public_key"
    and wrong: "\<not> verify public_key (Rust_Handover_Consent (rust_policy_profile current) (rust_policy_fingerprint current)
       (rust_policy_fingerprint successor) 1 identity proposal) former"
  shows "\<not> rust_handover_consent verify current successor former incoming identity proposal"
  using owner key wrong by (simp add: rust_handover_consent_def Let_def)

lemma bad_readiness_or_successor_revocation_stops_the_same_native_handover_before_any_write:
  assumes "\<not> verify (rust_policy_response_key successor) (native_readiness_preimage current successor) readiness \<or>
      transfer_successor proposal \<in> control_revoked control"
  shows "rust_handover_step admitted
        (rust_register_next_policy verify readiness current successor = Some successor \<and>
         rust_current_policy_for_handover current successor proposal \<and>
         transfer_successor proposal \<notin> control_revoked control) proposal code = (code,False)"
  using assms by (auto simp: rust_register_next_policy_def rust_handover_step_def)

context source_attestation
begin

theorem the_actual_successor_checks_and_ledger_gate_produce_the_model_owner_session_and_policy_result:
  fixes approve ready admitted
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
  assumes initial: "rust_handover_matches relate code source"
  shows "let (native,changed) = rust_handover_step admitted ready proposal code;
       model = (if ready then apply_owner_handover directory policy authenticate approve owner_token successor_token maintainer
          maintainers registered proposal source else source);
       selected = (if changed then rust_policy_fingerprint successor else rust_policy_fingerprint current)
    in rust_handover_matches relate native model \<and> changed = (model \<noteq> source) \<and>
       selected = (if model \<noteq> source then rust_policy_fingerprint successor else rust_policy_fingerprint current)"
proof -
  have gate: "admitted = handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer
          maintainers registered proposal source"
    using initial by (auto simp: admitted_def rust_handover_ledger_gate_def rust_handover_matches_def
        handover_is_authorized_def active_identity_def Let_def)
  show ?thesis
  proof (cases ready)
    case True
    note ready_now = True
    show ?thesis
    proof (cases admitted)
      case True
      then have authorized: "handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer
          maintainers registered proposal source" using gate by simp
      note correspondence = the_signed_rust_handover_preserves_related_reservations_and_returns_the_model_decision
        [OF initial authorized ready_now]
      show ?thesis using correspondence by (simp add: Let_def case_prod_beta True ready_now)
    next
      case False
      then have denied: "\<not> handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer
          maintainers registered proposal source" using gate by simp
      have unchanged: "apply_owner_handover directory policy authenticate approve owner_token successor_token maintainer
          maintainers registered proposal source = source"
        by (rule denied_handover_has_no_partial_write[OF denied])
      show ?thesis using initial by (simp add: Let_def False ready_now unchanged rust_handover_step_def)
    qed
  next
    case False
    show ?thesis using initial by (simp add: Let_def False rust_handover_step_def)
  qed
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms a_next_signature_for_another_policy_does_not_bind_the_selected_readiness_preimage
    a_wrong_detached_owner_signature_cannot_supply_the_native_consent
    bad_readiness_or_successor_revocation_stops_the_same_native_handover_before_any_write
    source_attestation.the_actual_successor_checks_and_ledger_gate_produce_the_model_owner_session_and_policy_result})
  then () else error "Unexpected oracle in signed handover provider correspondence"
\<close>

end
