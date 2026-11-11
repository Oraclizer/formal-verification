theory Handover_Finite_Export
  imports "OIP_V062_Handover_Finite_Model.Handover_Finite_Model"
    "HOL-Library.Code_Target_Nat"
begin

fun hfe_phase_tag :: "reservation_phase \<Rightarrow> nat" where
  "hfe_phase_tag Reservation_Held = 1"
| "hfe_phase_tag Source_Submitted = 2"
| "hfe_phase_tag Source_Pending = 3"
| "hfe_phase_tag Source_Confirmed = 4"
| "hfe_phase_tag Source_Returned = 5"
| "hfe_phase_tag Source_Cancelled = 6"

fun hfe_owner_row :: "nat option \<Rightarrow> nat list" where
  "hfe_owner_row None = [0,0]"
| "hfe_owner_row (Some m_owner) = [1,m_owner]"

fun hfe_session_row :: "nat \<Rightarrow> product_session_binding option \<Rightarrow> nat list" where
  "hfe_session_row m_session None = [m_session,0,0,0]"
| "hfe_session_row m_session (Some m_binding) =
    [m_session,1,session_principal m_binding,session_epoch m_binding]"

definition hfe_reservation_row :: "hfp_ledger \<Rightarrow> nat list" where
  "hfe_reservation_row m_store =
    (if \<not> fp_present m_store then [0]
     else let m_binding = fp_binding m_store in
       [1, fst (binding_key m_binding), snd (binding_key m_binding), binding_asset m_binding,
        fp_original_owner m_store, binding_destination m_binding, binding_recipient m_binding, binding_amount m_binding,
        hfe_phase_tag (fp_phase m_store), fp_worker m_store, fp_generation m_store, fp_deadline m_store] @
       fp_footprint m_store)"

definition hfe_financial_row :: "hfp_ledger \<Rightarrow> nat list" where
  "hfe_financial_row m_store = [fp_pending m_store, fp_source_units m_store, fp_destination_units m_store,
    fp_certificate_count m_store, fp_credit_count m_store, fp_source_effect_count m_store]"

definition hfe_image_rows :: "hfp_ledger rust_handover_image \<Rightarrow> nat \<Rightarrow> nat list list" where
  "hfe_image_rows m_image m_revision =
    [[rust_handover_epoch m_image,m_revision], hfe_owner_row (rust_handover_owner m_image 17)] @
    map (\<lambda>m_session. hfe_session_row m_session (rust_handover_sessions m_image m_session)) [1,2,3,4] @
    [hfe_reservation_row (rust_handover_ledger m_image), hfe_financial_row (rust_handover_ledger m_image)]"

definition hfe_result_rows :: "bool \<Rightarrow> bool \<Rightarrow>
    (hfp_ledger rust_handover_image \<times> bool) \<Rightarrow> nat list list" where
  "hfe_result_rows m_owner_ok m_successor_ok m_result =
    (let m_changed = snd m_result; m_revision = length hfp_setup_word;
         m_next_revision = (if m_changed then m_revision + length hfp_context_endpoints else m_revision)
     in [[1,1,(if m_owner_ok then 1 else 0),(if m_successor_ok then 1 else 0),(if m_changed then 1 else 0)]] @
       hfe_image_rows hfp_seed_image m_revision @ hfe_image_rows (fst m_result) m_next_revision)"

definition hfe_observe :: "bool \<Rightarrow> bool \<Rightarrow> nat list list" where
  "hfe_observe m_owner_ok m_successor_ok = hfe_result_rows m_owner_ok m_successor_ok (hfp_run m_owner_ok m_successor_ok)"

definition hfe_removal :: "bool \<Rightarrow> bool \<Rightarrow> nat list list" where
  "hfe_removal m_owner_ok m_successor_ok = hfe_result_rows m_owner_ok m_successor_ok (hfp_run m_owner_ok True)"

definition hfe_u64 :: "integer \<Rightarrow> bool" where
  "hfe_u64 m_word \<longleftrightarrow> 0 \<le> m_word \<and> m_word < 18446744073709551616"

fun hfe_observe_integer :: "integer list \<Rightarrow> integer list list" where
  "hfe_observe_integer [m_asset,m_event,m_source,m_receiver,m_former,m_successor,m_old_session,m_new_session,m_worker_session,
      m_old_epoch,m_new_epoch,m_amount,m_owner_ok,m_successor_ok] =
    (if list_all hfe_u64
       [m_asset,m_event,m_source,m_receiver,m_former,m_successor,m_old_session,m_new_session,m_worker_session,m_old_epoch,m_new_epoch,m_amount]
       \<and> [m_asset,m_event,m_source,m_receiver,m_former,m_successor,m_old_session,m_new_session,m_worker_session,m_old_epoch,m_new_epoch,m_amount] =
         [17,17,0,2,7,8,1,3,2,9,10,5]
       \<and> (m_owner_ok = 0 \<or> m_owner_ok = 1) \<and> (m_successor_ok = 0 \<or> m_successor_ok = 1)
     then map (map integer_of_nat) (hfe_observe (m_owner_ok = 1) (m_successor_ok = 1))
     else [[0]])"
| "hfe_observe_integer m_other_input = [[0]]"

fun hfe_removal_integer :: "integer list \<Rightarrow> integer list list" where
  "hfe_removal_integer [m_asset,m_event,m_source,m_receiver,m_former,m_successor,m_old_session,m_new_session,m_worker_session,
      m_old_epoch,m_new_epoch,m_amount,m_owner_ok,m_successor_ok] =
    (if hfe_observe_integer [m_asset,m_event,m_source,m_receiver,m_former,m_successor,m_old_session,m_new_session,m_worker_session,
         m_old_epoch,m_new_epoch,m_amount,m_owner_ok,m_successor_ok] = [[0]] then [[0]]
     else map (map integer_of_nat) (hfe_removal (m_owner_ok = 1) (m_successor_ok = 1)))"
| "hfe_removal_integer m_other_input = [[0]]"

lemma hfe_context_install_count_is_actual:
  "length (call_authority_log (sample.finality_calls.run_calls (map Apply_Authority_Input m_changes) m_calls)) =
    length (call_authority_log m_calls) + length m_changes"
  by (induction m_changes arbitrary: m_calls)
    (simp_all add: sample.finality_calls.apply_authority_input_def Let_def)

lemma hfe_normal_revision_is_the_checked_product_revision:
  "length hfp_setup_word + length hfp_context_endpoints =
    cut_revision (current_product_cut (hg_product_after True True))"
proof -
  have batch: "lock_context_batch_is_newer {0,2} (transfer_epoch hg_proposal) (transfer_contexts hg_proposal) hf_source"
    using hg_normal_authorized by (simp add: handover_is_authorized_def Let_def)
  show ?thesis
    by (simp add: hfp_revision_and_context_counts_come_from_the_source
        hg_product_after_def sample.apply_owner_handover_def hg_normal_authorized batch
        sample.product_apply_public_def current_product_cut_def hfe_context_install_count_is_actual Let_def)
qed

lemma hfe_denied_typed_product_is_unchanged:
  assumes "\<not> (m_owner_ok \<and> m_successor_ok)"
  shows "hg_product_after m_owner_ok m_successor_ok = hf_source"
proof -
  have denied: "\<not> hg_gate m_owner_ok m_successor_ok"
    using assms hg_typed_gate_is_exactly_the_two_approvals[of m_owner_ok m_successor_ok] by blast
  show ?thesis unfolding hg_product_after_def
    by (rule sample.denied_handover_has_no_partial_write[OF denied[unfolded hg_gate_def]])
qed

lemma hfe_every_reported_revision_matches_the_product:
  "(if snd (hfp_run m_owner_ok m_successor_ok)
     then length hfp_setup_word + length hfp_context_endpoints else length hfp_setup_word) =
    cut_revision (current_product_cut (hg_product_after m_owner_ok m_successor_ok))"
proof (cases "m_owner_ok \<and> m_successor_ok")
  case True
  then have flags: "m_owner_ok = True" "m_successor_ok = True" by auto
  show ?thesis
    using hfe_normal_revision_is_the_checked_product_revision
      hg_normal_native_owner_sessions_epoch_and_immutable_ledger(1)
    by (simp add: flags hfp_run_is_related_to_the_checked_typed_execution)
next
  case False
  have unchanged: "hg_product_after m_owner_ok m_successor_ok = hf_source"
    by (rule hfe_denied_typed_product_is_unchanged[OF False])
  have refused: "\<not> snd (hfp_run m_owner_ok m_successor_ok)"
    using False by (simp add: hfp_run_def rust_handover_step_def)
  show ?thesis using unchanged refused hfp_revision_and_context_counts_come_from_the_source(1) by simp
qed

lemma hfe_observed_image_is_the_exact_checked_projection:
  "hfe_image_rows (fst (hfp_run m_owner_ok m_successor_ok)) m_revision =
    hfe_image_rows (hfp_project_image (fst (hg_native_step m_owner_ok m_successor_ok))) m_revision"
  by (simp add: hfp_run_is_related_to_the_checked_typed_execution)

lemma hfe_observed_decision_is_not_a_case_table:
  "snd (hfp_run m_owner_ok m_successor_ok) = snd (hg_native_step m_owner_ok m_successor_ok)"
  by (simp add: hfp_run_is_related_to_the_checked_typed_execution)

lemma hfe_removal_changes_only_the_same_approval_condition:
  "snd (hfp_run m_owner_ok True) = snd (hg_without_successor_approval m_owner_ok m_successor_ok)"
  by (simp add: hfp_run_is_related_to_the_checked_typed_execution hg_without_successor_approval_def)

thm_oracles hfe_normal_revision_is_the_checked_product_revision hfe_every_reported_revision_matches_the_product
  hfe_observed_image_is_the_exact_checked_projection hfe_observed_decision_is_not_a_case_table
  hfe_removal_changes_only_the_same_approval_condition

ML \<open>
  if null (Thm_Deps.all_oracles @{thms hfe_normal_revision_is_the_checked_product_revision
      hfe_every_reported_revision_matches_the_product
      hfe_observed_image_is_the_exact_checked_projection hfe_observed_decision_is_not_a_case_table
      hfe_removal_changes_only_the_same_approval_condition})
  then writeln "HANDOVER_FINITE_EXPORT_ORACLES_EMPTY"
  else error "Unexpected oracle in finite handover export"
\<close>

export_code hfe_observe_integer hfe_removal_integer
  in SML module_name OIP_Handover_Finite_ABI file_prefix "oip_handover_finite_abi"

end
