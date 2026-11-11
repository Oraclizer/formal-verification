theory Control_Recovery_Finite
  imports "OIP_V062_Handover_Recovery_Control_Base.Control_Recovery_Base"
    "OIP_V062_Handover_Finite_Model.Handover_Finite_Model"
begin

definition hcf_post_image :: "hfp_ledger rust_handover_image" where
  "hcf_post_image = fst (hfp_run True True)"

definition hcf_active :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "hcf_active m_who m_session \<longleftrightarrow>
    m_who \<in> {7,8} \<and> rust_handover_epoch hcf_post_image = 10 \<and>
    rust_handover_sessions hcf_post_image m_session = Some \<lparr>session_principal = m_who, session_epoch = 10\<rparr>"

definition hcf_controller :: "nat option" where
  "hcf_controller =
    (let m_store = rust_handover_ledger hcf_post_image in
      if fp_present m_store \<and> active_reservation_phase (fp_phase m_store)
      then rust_handover_owner hcf_post_image (binding_asset (fp_binding m_store)) else None)"

definition hcf_endorsement_allowed :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "hcf_endorsement_allowed m_who m_session \<longleftrightarrow>
    hcf_active m_who m_session \<and> hcf_controller = Some m_who"

definition hcf_terminal_rows :: "(source_key \<times> terminal_record) list" where
  "hcf_terminal_rows = []"

definition hcf_record_reference :: "(source_key \<times> terminal_record) list \<Rightarrow> nat \<Rightarrow>
    transfer_binding \<Rightarrow> terminal_kind \<Rightarrow> source_certificate option" where
  "hcf_record_reference m_rows m_index m_binding m_kind =
    (case map_of m_rows (binding_key m_binding) of None \<Rightarrow> None
     | Some m_record \<Rightarrow>
       if terminal_binding m_record = m_binding \<and> terminal_kind m_record = m_kind \<and>
          m_index < length (terminal_evidence m_record)
       then Some (terminal_evidence m_record ! m_index) else None)"

text \<open>A present exact record is outside this extraction's empty-record
setup. None in that branch is an unsupported extraction, never a success.
For the checked setup the record lookup is proved absent.\<close>

definition hcf_refund_reply :: "finality_reply option" where
  "hcf_refund_reply =
    (if hcf_record_reference hcf_terminal_rows 0 (request_binding hc_refund_request) Reversed_Decision =
         Some (request_certificate hc_refund_request)
     then None else Some Finality_Rejected)"

definition hcf_selected_reply :: "nat \<Rightarrow> nat \<Rightarrow> finality_reply option" where
  "hcf_selected_reply m_who m_session =
    (if hcf_endorsement_allowed m_who m_session then hcf_refund_reply else None)"

lemma hcf_post_image_matches_checked_owner_sessions_and_epoch:
  "rust_handover_owner hcf_post_image = owner_of_product hc_post_source"
  "rust_handover_sessions hcf_post_image = product_sessions (product_durable hc_post_source)"
  "rust_handover_epoch hcf_post_image = cut_authority_epoch (current_product_cut hc_post_source)"
  using hg_normal_reuses_the_checked_native_product_relation(1)
  by (simp_all add: hcf_post_image_def hfp_run_is_related_to_the_checked_typed_execution
      hfp_project_image_def hc_post_source_def rust_handover_matches_def)

lemma hcf_active_is_the_actual_identity_gate:
  "hcf_active m_who m_session = active_identity identity_case_directory (identity_case_user m_who)
      (identity_case_proof m_session 10) hc_post_source"
  by (simp add: hcf_active_def active_identity_def hcf_post_image_matches_checked_owner_sessions_and_epoch
      hc_post_owner_and_live_sessions(2) identity_case_directory_def identity_case_user_def identity_case_proof_def)

lemma hcf_finite_controller_is_the_actual_controller:
  "hcf_controller = recovery_controller hc_post_source (0,17)"
  by (simp add: hcf_controller_def hcf_post_image_def hfp_run_def rust_handover_step_def
      hfp_seed_image_def hfp_owner_map_def hfp_session_map_def hfp_step_proposal_def
      native_replace_handover_sessions_def hfp_seed_ledger_def hfp_setup_word_def hfp_bootstrap_def
      sample_binding_def example_binding_def hc_actual_controller_is_the_successor Let_def)

lemma hcf_endorsement_is_the_checked_controller_gate:
  "hcf_endorsement_allowed m_who m_session = hc_endorsement_allowed m_who m_session"
  by (simp add: hcf_endorsement_allowed_def hcf_active_is_the_actual_identity_gate
      hcf_finite_controller_is_the_actual_controller hc_endorsement_allowed_def
      recovery_has_current_endorsement_def hc_endorsement_def hc_typed_authenticate_def
      hc_typed_policy_def hc_typed_endorse_def identity_case_user_def)

lemma hcf_empty_rows_are_the_actual_terminal_record_map:
  "map_of hcf_terminal_rows = core_records hc_post_core"
  by (simp add: hcf_terminal_rows_def hc_setup_and_handover_have_no_recorded_terminal_evidence)

lemma hcf_reference_lookup_is_the_actual_lookup:
  "hcf_record_reference hcf_terminal_rows m_index m_binding m_kind =
    record_reference hc_post_core m_index m_binding m_kind"
  by (simp add: hcf_record_reference_def record_reference_def hcf_empty_rows_are_the_actual_terminal_record_map)

lemma hcf_refund_observation_is_the_actual_refused_consumer:
  "hcf_refund_reply = Some (snd hc_refund_core_result)"
  by (simp add: hcf_refund_reply_def hcf_reference_lookup_is_the_actual_lookup
      hc_setup_and_handover_have_no_recorded_terminal_evidence record_reference_def
      hc_actual_refund_consumer_rejects_the_missing_record_without_financial_effect)

lemma hcf_selected_reply_is_the_actual_two_stage_observation:
  "hcf_selected_reply m_who m_session = hc_selected_reply m_who m_session"
  by (simp add: hcf_selected_reply_def hc_selected_reply_def hcf_endorsement_is_the_checked_controller_gate
      hcf_refund_observation_is_the_actual_refused_consumer)

thm_oracles hcf_active_is_the_actual_identity_gate hcf_finite_controller_is_the_actual_controller
  hcf_endorsement_is_the_checked_controller_gate hcf_empty_rows_are_the_actual_terminal_record_map
  hcf_reference_lookup_is_the_actual_lookup hcf_refund_observation_is_the_actual_refused_consumer
  hcf_selected_reply_is_the_actual_two_stage_observation

ML \<open>
  if null (Thm_Deps.all_oracles @{thms hcf_active_is_the_actual_identity_gate
      hcf_finite_controller_is_the_actual_controller hcf_endorsement_is_the_checked_controller_gate
      hcf_empty_rows_are_the_actual_terminal_record_map hcf_reference_lookup_is_the_actual_lookup
      hcf_refund_observation_is_the_actual_refused_consumer hcf_selected_reply_is_the_actual_two_stage_observation})
  then writeln "HANDOVER_RECOVERY_FINITE_ORACLES_EMPTY"
  else error "Unexpected oracle in finite recovery controls"
\<close>

end
