theory Handover_Finite_Model
  imports "OIP_V062_Handover_Typed_Model.Handover_Typed_Model"
begin

record hfp_ledger =
  fp_original_owner :: nat
  fp_binding :: transfer_binding
  fp_present :: bool
  fp_phase :: reservation_phase
  fp_worker :: nat
  fp_generation :: nat
  fp_deadline :: nat
  fp_footprint :: "nat list"
  fp_pending :: nat
  fp_source_units :: nat
  fp_destination_units :: nat
  fp_certificate_count :: nat
  fp_credit_count :: nat
  fp_source_effect_count :: nat

datatype hfp_setup_action = FP_Reserve | FP_Dispatch | FP_Debit

definition hfp_bootstrap :: hfp_ledger where
  "hfp_bootstrap = \<lparr>fp_original_owner = 7, fp_binding = sample_binding 17,
    fp_present = False, fp_phase = Reservation_Held, fp_worker = 0,
    fp_generation = 0, fp_deadline = 0, fp_footprint = [], fp_pending = 0,
    fp_source_units = 10, fp_destination_units = 0,
    fp_certificate_count = 0, fp_credit_count = 0, fp_source_effect_count = 0\<rparr>"

fun hfp_setup_step :: "hfp_setup_action \<Rightarrow> hfp_ledger \<Rightarrow> hfp_ledger" where
  "hfp_setup_step FP_Reserve m_store =
    (if \<not> fp_present m_store \<and> binding_amount (fp_binding m_store) \<le> fp_source_units m_store
     then m_store\<lparr>fp_present := True, fp_phase := Reservation_Held,
       fp_worker := 7, fp_generation := 0, fp_deadline := 10,
       fp_footprint := [binding_asset (fp_binding m_store)]\<rparr> else m_store)"
| "hfp_setup_step FP_Dispatch m_store =
    (if fp_present m_store \<and> fp_phase m_store = Reservation_Held
     then m_store\<lparr>fp_phase := Source_Submitted\<rparr> else m_store)"
| "hfp_setup_step FP_Debit m_store =
    (if fp_present m_store \<and> fp_phase m_store = Source_Submitted \<and>
         binding_amount (fp_binding m_store) \<le> fp_source_units m_store
     then m_store\<lparr>fp_phase := Source_Pending,
       fp_source_units := fp_source_units m_store - binding_amount (fp_binding m_store),
       fp_pending := binding_amount (fp_binding m_store),
       fp_source_effect_count := Suc (fp_source_effect_count m_store)\<rparr> else m_store)"

definition hfp_setup_word :: "hfp_setup_action list" where
  "hfp_setup_word = [FP_Reserve, FP_Dispatch, FP_Debit]"

definition hfp_seed_ledger :: hfp_ledger where
  "hfp_seed_ledger = fold hfp_setup_step hfp_setup_word hfp_bootstrap"

definition hfp_project_ledger :: "(nat \<times> reservation_state) \<Rightarrow> hfp_ledger" where
  "hfp_project_ledger m_raw =
    (let m_store = snd m_raw; m_claim = reservation_at m_store (0,17);
         m_binding = (case m_claim of None \<Rightarrow> sample_binding 17 | Some m_res \<Rightarrow> reservation_binding m_res)
     in \<lparr>fp_original_owner = fst m_raw, fp_binding = m_binding,
       fp_present = (m_claim \<noteq> None),
       fp_phase = (case m_claim of None \<Rightarrow> Reservation_Held | Some m_res \<Rightarrow> reservation_phase m_res),
       fp_worker = (case m_claim of None \<Rightarrow> 0 | Some m_res \<Rightarrow> reservation_worker m_res),
       fp_generation = (case m_claim of None \<Rightarrow> 0 | Some m_res \<Rightarrow> reservation_generation m_res),
       fp_deadline = (case m_claim of None \<Rightarrow> 0 | Some m_res \<Rightarrow> reservation_deadline m_res),
       fp_footprint = (case m_claim of None \<Rightarrow> [] | Some m_res \<Rightarrow> reservation_footprint m_res),
       fp_pending = (if m_binding \<in> example.unresolved_source_obligations m_store then binding_amount m_binding else 0),
       fp_source_units = source_units m_store (0,17), fp_destination_units = destination_units m_store (2,17,3),
       fp_certificate_count = length (issued_certificates m_store),
       fp_credit_count = length (credit_history (received_messages m_store)),
       fp_source_effect_count = length (source_effects m_store)\<rparr>)"

definition hfp_project_image :: "(nat \<times> reservation_state) rust_handover_image \<Rightarrow> hfp_ledger rust_handover_image" where
  "hfp_project_image m_image = \<lparr>rust_handover_owner = rust_handover_owner m_image,
    rust_handover_sessions = rust_handover_sessions m_image, rust_handover_epoch = rust_handover_epoch m_image,
    rust_handover_ledger = hfp_project_ledger (rust_handover_ledger m_image)\<rparr>"

definition hfp_owner_map :: "nat \<Rightarrow> nat option" where
  "hfp_owner_map = (\<lambda>m_asset. if m_asset = 17 then Some 7 else None)"

definition hfp_session_map :: "nat \<Rightarrow> product_session_binding option" where
  "hfp_session_map = (\<lambda>m_session. if m_session \<in> {1,2}
    then Some \<lparr>session_principal = 7, session_epoch = 9\<rparr>
    else if m_session = 4 then Some \<lparr>session_principal = 8, session_epoch = 9\<rparr> else None)"

definition hfp_seed_image :: "hfp_ledger rust_handover_image" where
  "hfp_seed_image = \<lparr>rust_handover_owner = hfp_owner_map, rust_handover_sessions = hfp_session_map,
    rust_handover_epoch = 9, rust_handover_ledger = hfp_seed_ledger\<rparr>"

text \<open>The executable ledger step never reads expected cut or contexts.
They are checked by the original typed admission proof, not replaced with an
empty-context admission. Only their unused execution carrier is erased.\<close>

definition hfp_step_proposal :: ownership_transfer where
  "hfp_step_proposal = \<lparr>transfer_asset = 17, transfer_previous = 7, transfer_successor = 8,
    transfer_expected = \<lparr>cut_authority_epoch = 9, cut_revision = 3\<rparr>,
    transfer_old_session = 1, transfer_new_session = 3, transfer_epoch = 10,
    transfer_contexts = []\<rparr>"

definition hfp_context_endpoints :: "nat list" where
  "hfp_context_endpoints = [0,2]"

definition hfp_run :: "bool \<Rightarrow> bool \<Rightarrow> (hfp_ledger rust_handover_image \<times> bool)" where
  "hfp_run m_owner_ok m_successor_ok =
    rust_handover_step (m_owner_ok \<and> m_successor_ok) True hfp_step_proposal hfp_seed_image"

lemma hfp_finite_prefix_matches_the_checked_financial_seed:
  "hfp_seed_ledger = hfp_project_ledger (7, authoritative_reservation_state hf_source)"
  by (simp add: hfp_seed_ledger_def hfp_setup_word_def hfp_bootstrap_def hfp_project_ledger_def
      hf_financial_seed_is_the_checked_pending_state finality_source_prefix_is_the_actual_parent_prefix
      sample_data_defs sample.protocol_definitions record_observation_def commit_reservation_event_def
      example.unresolved_source_obligations_def empty_message_state_def Let_def)

lemma hfp_owner_map_matches_the_checked_setup:
  "owner_of_product hf_source = hfp_owner_map"
  by (simp add: owner_of_product_def hfp_owner_map_def hf_setup_defs sample_request_def)

lemma hfp_session_map_matches_the_checked_setup:
  "product_sessions (product_durable hf_source) = hfp_session_map"
  by (simp add: hf_source_keeps_the_three_actual_session_bindings hfp_session_map_def hf_sessions_def fun_eq_iff)

lemma hfp_initial_image_is_the_exact_projection:
  "hfp_seed_image = hfp_project_image hg_native_before"
  by (simp add: hfp_seed_image_def hfp_project_image_def hg_native_before_def
      hfp_finite_prefix_matches_the_checked_financial_seed hfp_owner_map_matches_the_checked_setup
      hfp_session_map_matches_the_checked_setup hf_current_cut_is_derived_from_the_prefix)

lemma hfp_projection_commutes_with_the_same_step:
  "rust_handover_step m_admitted m_approved hfp_step_proposal (hfp_project_image m_code) =
    (hfp_project_image (fst (rust_handover_step m_admitted m_approved hg_proposal m_code)),
     snd (rust_handover_step m_admitted m_approved hg_proposal m_code))"
  by (auto simp: hfp_project_image_def rust_handover_step_def native_replace_handover_sessions_def
      hfp_step_proposal_def hg_proposal_def handover_case_proposal_def Let_def split: option.splits if_splits)

lemma hfp_run_is_related_to_the_checked_typed_execution:
  "hfp_run m_owner_ok m_successor_ok =
    (hfp_project_image (fst (hg_native_step m_owner_ok m_successor_ok)),
     snd (hg_native_step m_owner_ok m_successor_ok))"
  by (simp add: hfp_run_def hfp_initial_image_is_the_exact_projection
      hfp_projection_commutes_with_the_same_step hg_native_step_def hg_typed_gate_is_exactly_the_two_approvals)

lemma hfp_revision_and_context_counts_come_from_the_source:
  "length hfp_setup_word = cut_revision (current_product_cut hf_source)"
  "length hfp_context_endpoints = length (transfer_contexts hg_proposal)"
  by (simp_all add: hfp_setup_word_def hfp_context_endpoints_def hf_current_cut_is_derived_from_the_prefix
      hg_proposal_def handover_case_proposal_def numeral_3_eq_3 numeral_2_eq_2)

thm_oracles hfp_finite_prefix_matches_the_checked_financial_seed hfp_initial_image_is_the_exact_projection
  hfp_projection_commutes_with_the_same_step hfp_run_is_related_to_the_checked_typed_execution

ML \<open>
  if null (Thm_Deps.all_oracles @{thms hfp_finite_prefix_matches_the_checked_financial_seed
      hfp_initial_image_is_the_exact_projection hfp_projection_commutes_with_the_same_step
      hfp_run_is_related_to_the_checked_typed_execution hfp_revision_and_context_counts_come_from_the_source})
  then writeln "HANDOVER_FINITE_MODEL_ORACLES_EMPTY"
  else error "Unexpected oracle in finite handover projection"
\<close>

end
