theory Handover_Typed_Model
  imports "OIP_V062_Handover_Seed_Frame.Handover_Seed_Frame"
begin

text \<open>This executable canary is explicitly the typed Rules path.
Its approval booleans are the fixture's Valid/Invalid tags. They are not
Ed25519 facts or evidence of successor-policy registration.\<close>

definition hg_proposal :: ownership_transfer where
  "hg_proposal = handover_case_proposal\<lparr>transfer_expected := current_product_cut hf_source\<rparr>"

definition hg_approve :: "bool \<Rightarrow> bool \<Rightarrow> registered_identity \<Rightarrow> ownership_transfer \<Rightarrow> bool" where
  "hg_approve owner_ok successor_ok identity proposal =
    (if identity_principal identity = 7 then owner_ok
     else identity_principal identity = 8 \<and> successor_ok)"

definition hg_gate :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "hg_gate owner_ok successor_ok = handover_is_authorized identity_case_directory
    (\<lambda>_ _ _ _ _. True) Some (hg_approve owner_ok successor_ok)
    (identity_case_user 7) (identity_case_user 8) (7::nat) {7} {0,2} hg_proposal hf_source"

definition hg_product_after :: "bool \<Rightarrow> bool \<Rightarrow> product_world" where
  "hg_product_after owner_ok successor_ok = sample.apply_owner_handover identity_case_directory
    (\<lambda>_ _ _ _ _. True) Some (hg_approve owner_ok successor_ok)
    (identity_case_user 7) (identity_case_user 8) (7::nat) {7} {0,2} hg_proposal hf_source"

text \<open>The extra owner field is the immutable native Binding.owner.
The public transfer_binding has no such field. The financial projection
retains it independently of the mutable owner registry.\<close>

definition hg_ledger_relation :: "(nat \<times> reservation_state) \<Rightarrow> reservation_state \<Rightarrow> bool" where
  "hg_ledger_relation ledger reservations \<longleftrightarrow> fst ledger = 7 \<and> snd ledger = reservations"

definition hg_native_before :: "(nat \<times> reservation_state) rust_handover_image" where
  "hg_native_before = \<lparr>rust_handover_owner = owner_of_product hf_source,
    rust_handover_sessions = product_sessions (product_durable hf_source),
    rust_handover_epoch = cut_authority_epoch (current_product_cut hf_source),
    rust_handover_ledger = (7, authoritative_reservation_state hf_source)\<rparr>"

ML_val \<open>
  writeln ("HANDOVER_GATE_TYPE " ^ Syntax.string_of_typ @{context} (Term.fastype_of @{term hg_gate}));
  writeln ("HANDOVER_GATE_DEFINITION " ^ Syntax.string_of_term @{context} (Thm.prop_of @{thm hg_gate_def}))
\<close>

definition hg_native_step :: "bool \<Rightarrow> bool \<Rightarrow> ((nat \<times> reservation_state) rust_handover_image \<times> bool)" where
  "hg_native_step owner_ok successor_ok =
    rust_handover_step (Handover_Typed_Model.hg_gate owner_ok successor_ok) True hg_proposal hg_native_before"

definition hg_without_successor_approval :: "bool \<Rightarrow> bool \<Rightarrow> ((nat \<times> reservation_state) rust_handover_image \<times> bool)" where
  "hg_without_successor_approval owner_ok successor_ok = hg_native_step owner_ok True"

lemma hg_initial_native_image_is_related:
  "rust_handover_matches hg_ledger_relation hg_native_before hf_source"
  by (simp add: rust_handover_matches_def hg_ledger_relation_def hg_native_before_def)

lemma hg_typed_gate_is_exactly_the_two_approvals:
  "hg_gate owner_ok successor_ok = (owner_ok \<and> successor_ok)"
  by (simp add: hg_gate_def hg_approve_def handover_is_authorized_def hg_proposal_def
      handover_case_proposal_def handover_case_context_def identity_case_user_def identity_case_directory_def
      hf_current_cut_is_derived_from_the_prefix hf_source_keeps_the_three_actual_session_bindings
      hf_three_actual_submissions_produce_the_public_call_word hf_calls_have_three_commits_and_remain_available
      hf_sessions_def active_identity_def lock_context_batch_is_newer_def lock_example_contexts_def
      sample_source_context_def sample_context_def example_context_def Let_def)

lemma hg_normal_authorized:
  "handover_is_authorized identity_case_directory (\<lambda>_ _ _ _ _. True) Some
    (hg_approve True True) (identity_case_user 7) (identity_case_user 8) (7::nat) {7} {0,2} hg_proposal hf_source"
  using hg_typed_gate_is_exactly_the_two_approvals[of True True] by (simp add: hg_gate_def)

lemma hg_normal_reuses_the_checked_native_product_relation:
  "rust_handover_matches hg_ledger_relation (fst (hg_native_step True True)) (hg_product_after True True)"
  "snd (hg_native_step True True) = (hg_product_after True True \<noteq> hf_source)"
  using sample.the_signed_rust_handover_preserves_related_reservations_and_returns_the_model_decision
    [OF hg_initial_native_image_is_related hg_normal_authorized TrueI]
  by (simp_all add: hg_native_step_def hg_product_after_def hg_typed_gate_is_exactly_the_two_approvals Let_def)

lemma hg_missing_successor_consent_preserves_the_entire_source:
  "hg_product_after True False = hf_source"
  "hg_native_step True False = (hg_native_before, False)"
proof -
  have denied: "\<not> handover_is_authorized identity_case_directory (\<lambda>_ _ _ _ _. True) Some
    (hg_approve True False) (identity_case_user 7) (identity_case_user 8) (7::nat) {7} {0,2} hg_proposal hf_source"
    using hg_typed_gate_is_exactly_the_two_approvals[of True False] by (simp add: hg_gate_def)
  show "hg_product_after True False = hf_source"
    unfolding hg_product_after_def by (rule sample.denied_handover_has_no_partial_write[OF denied])
  show "hg_native_step True False = (hg_native_before, False)"
    by (simp add: hg_native_step_def hg_typed_gate_is_exactly_the_two_approvals rust_handover_step_def)
qed

lemmas hg_native_defs = hg_native_step_def hg_native_before_def hg_proposal_def handover_case_proposal_def
  hg_typed_gate_is_exactly_the_two_approvals rust_handover_step_def native_replace_handover_sessions_def
  hf_current_cut_is_derived_from_the_prefix hf_source_keeps_the_three_actual_session_bindings hf_sessions_def Let_def

lemma hg_normal_native_owner_sessions_epoch_and_immutable_ledger:
  "snd (hg_native_step True True)"
  "rust_handover_owner (fst (hg_native_step True True)) 17 = Some 8"
  "rust_handover_sessions (fst (hg_native_step True True)) 1 = None"
  "rust_handover_sessions (fst (hg_native_step True True)) 3 = Some \<lparr>session_principal = 8, session_epoch = 10\<rparr>"
  "rust_handover_sessions (fst (hg_native_step True True)) 2 = Some \<lparr>session_principal = 7, session_epoch = 10\<rparr>"
  "rust_handover_sessions (fst (hg_native_step True True)) 4 = Some \<lparr>session_principal = 8, session_epoch = 10\<rparr>"
  "rust_handover_epoch (fst (hg_native_step True True)) = 10"
  "rust_handover_ledger (fst (hg_native_step True True)) = (7, authoritative_reservation_state hf_source)"
  by (simp_all add: hg_native_defs)

lemma hg_single_successor_approval_removal_changes_the_same_input:
  "snd (hg_native_step True False) = False"
  "snd (hg_without_successor_approval True False) = True"
  by (simp_all add: hg_without_successor_approval_def hg_missing_successor_consent_preserves_the_entire_source
      hg_normal_native_owner_sessions_epoch_and_immutable_ledger)

lemma hg_product_financial_state_and_phase_are_preserved:
  "authoritative_reservation_state (hg_product_after True True) = authoritative_reservation_state hf_source"
  using sample.handover_atomically_changes_owner_and_sessions_without_spending(5)[OF hg_normal_authorized]
  by (simp add: hg_product_after_def)

lemma hg_old_proof_is_rejected_but_the_worker_remains_live:
  "\<not> active_identity identity_case_directory (identity_case_user 7) (identity_case_proof 1 9) (hg_product_after True True)"
  "active_identity identity_case_directory (identity_case_user 7) (identity_case_proof 2 10) (hg_product_after True True)"
  "active_identity identity_case_directory (identity_case_user 8) (identity_case_proof 3 10) (hg_product_after True True)"
  using hg_normal_reuses_the_checked_native_product_relation(1)
    hg_normal_native_owner_sessions_epoch_and_immutable_ledger
  by (auto simp: rust_handover_matches_def active_identity_def identity_case_user_def
      identity_case_directory_def identity_case_proof_def)

lemma hg_any_old_signed_payload_fails_every_route:
  assumes "cut_authority_epoch (envelope_cut (payload_envelope payload)) = 9"
  shows "\<not> endpoint_call_allowed_on route directory policy authenticate verify token proof target operation actor call_id payload
    (hg_product_after True True)"
proof -
  have epoch: "cut_authority_epoch (current_product_cut (hg_product_after True True)) = 10"
    using hg_normal_reuses_the_checked_native_product_relation(1)
      hg_normal_native_owner_sessions_epoch_and_immutable_ledger(7)
    by (simp add: rust_handover_matches_def)
  show ?thesis unfolding endpoint_call_allowed_on_def
    by (rule an_older_signed_request_cannot_use_a_reopened_session) (simp add: assms epoch)
qed

thm_oracles hg_normal_reuses_the_checked_native_product_relation
  hg_missing_successor_consent_preserves_the_entire_source
  hg_single_successor_approval_removal_changes_the_same_input
  hg_product_financial_state_and_phase_are_preserved hg_old_proof_is_rejected_but_the_worker_remains_live
  hg_any_old_signed_payload_fails_every_route

ML \<open>
  if null (Thm_Deps.all_oracles @{thms hg_normal_reuses_the_checked_native_product_relation
      hg_missing_successor_consent_preserves_the_entire_source
      hg_single_successor_approval_removal_changes_the_same_input
      hg_product_financial_state_and_phase_are_preserved hg_old_proof_is_rejected_but_the_worker_remains_live
      hg_any_old_signed_payload_fails_every_route})
  then writeln "HANDOVER_TYPED_MODEL_ORACLES_EMPTY"
  else error "Unexpected oracle in the typed handover model"
\<close>

end
