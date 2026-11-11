theory Pending_Lock_G0
  imports Pending_Lock_Inputs
begin

definition pl_uncredited_guard_ready where
  "pl_uncredited_guard_ready =
    (case pl_case_before pl_case_reconcile_confirmed_not_credited of None \<Rightarrow> False | Some before \<Rightarrow>
      let request = pl_case_request pl_case_reconcile_confirmed_not_credited before
      in pls_phase before = PL_Pending \<and> pl_pending before > 0 \<and>
         pl_exact_confirmed before 0 \<and> pls_clock before < pls_expires before \<and>
         pl_request_admitted request before \<and> plr_verified request \<and>
         pl_effect_credential request before \<and> Suc (pls_revision before) < 2^64)"

definition pl_credit_guard_removal_witness where
  "pl_credit_guard_removal_witness =
    (case (pl_run_case True pl_case_reconcile_confirmed_not_credited,
           pl_run_case False pl_case_reconcile_confirmed_not_credited) of
      (Some (before,request,after,reply),Some (mut_before,mut_request,mut_after,mut_reply)) \<Rightarrow>
        before = mut_before \<and> request = mut_request \<and> after = before \<and> reply = PL_Rejected \<and>
        mut_reply = PL_Reconciled_Reply \<and> pls_phase mut_after = PL_Reconciled \<and>
        map_of (pls_active before) (pl_asset (pls_binding before)) = Some (pl_origin (pls_binding before)) \<and>
        map_of (pls_active mut_after) (pl_asset (pls_binding before)) = None \<and>
        pl_pending before > 0 \<and> pl_pending mut_after = 0 \<and>
        pl_visible_mass mut_after + pl_amount (pls_binding before) = pl_visible_mass before
     | _ \<Rightarrow> False)"

definition pl_exact_credit_positive_witness where
  "pl_exact_credit_positive_witness =
    (case pl_run_case True pl_case_reconcile_exact_credit of None \<Rightarrow> False
     | Some (before,request,after,reply) \<Rightarrow> reply = PL_Reconciled_Reply \<and>
       pls_source after = pls_source before \<and> pls_destination_balance after = pls_destination_balance before \<and>
       pls_root_funding after = pls_root_funding before \<and> pl_visible_mass after = pl_visible_mass before \<and>
       map_of (pls_active after) (pl_asset (pls_binding before)) = None \<and>
       pl_receipt_credential request after \<and> \<not> pl_effect_credential request after)"

definition pl_old_token_after_preempt_witness where
  "pl_old_token_after_preempt_witness =
    (case pl_run_case True pl_case_pending_preempt of None \<Rightarrow> False
     | Some (before,request,after,reply) \<Rightarrow>
       let old_token = pl_seed_credential (pls_binding before) (pls_holder before) (pls_generation before) (pls_epoch before);
           old_request = pl_fresh_request after (pls_holder before) 1 (PL_Cancel (pls_generation before)) (Some old_token)
       in reply = PL_Preempted \<and> pls_generation after = Suc (pls_generation before) \<and>
          pl_pending after = pl_pending before \<and> pl_pending after > 0 \<and>
          pls_evidence after = pls_evidence before \<and> pls_terminal after = pls_terminal before \<and>
          \<not> pl_bound_credential old_request after (pls_generation before))"

lemma pl_removed_footprint_member_has_no_active_entry:
  fixes asset :: nat and entries :: "(nat \<times> (nat \<times> nat)) list"
  assumes "asset \<in> set footprint"
  shows "map_of (filter (\<lambda>(member,key). member \<notin> set footprint) entries) asset = None"
  using assms by (induction entries) (auto split: prod.splits)

theorem pl_phase_only_guard_removal_has_a_typed_counterexample_contract:
  fixes state :: pl_state and request :: pl_request
  assumes command: "plr_command request = PL_Reconcile generation reference"
    and pending: "pls_phase state = PL_Pending"
    and amount: "0 < pl_amount (pls_binding state)"
    and admission: "pl_request_admitted request state"
    and verified: "plr_verified request"
    and credential: "pl_effect_credential request state"
    and revision: "Suc (pls_revision state) < 2^64"
    and current: "pls_clock state < pls_expires state"
    and exact: "pl_exact_confirmed state reference"
    and member: "pl_asset (pls_binding state) \<in> set (pls_footprint state)"
  shows "pl_step True request state = (state,PL_Rejected)"
    "pl_step False request state =
      ((pl_release PL_Reconciled state)\<lparr>pls_revision := Suc (pls_revision state)\<rparr>,PL_Reconciled_Reply)"
    "pl_pending (fst (pl_step False request state)) = 0"
    "pl_visible_mass (fst (pl_step False request state)) + pl_amount (pls_binding state) = pl_visible_mass state"
    "pl_visible_mass (fst (pl_step False request state)) < pl_visible_mass state"
    "map_of (pls_active (fst (pl_step False request state))) (pl_asset (pls_binding state)) = None"
proof -
  have pl_exists: "pls_exists state" and pl_binding_exact: "plr_binding request = pls_binding state"
    using credential command
    by (auto simp: pl_effect_credential_def pl_bound_credential_def split: option.splits)
  have pl_normal: "pl_step True request state = (state,PL_Rejected)"
    by (rule pl_confirmed_attestation_is_not_prior_credit[OF command]) (simp add: pending)
  have pl_mutant: "pl_step False request state =
      ((pl_release PL_Reconciled state)\<lparr>pls_revision := Suc (pls_revision state)\<rparr>,PL_Reconciled_Reply)"
    using command admission verified credential revision current exact pl_exists pl_binding_exact
    by (simp add: pl_step_def pl_apply_def Let_def)
  have pl_mass: "pl_visible_mass (fst (pl_step False request state)) + pl_amount (pls_binding state) = pl_visible_mass state"
    using pl_mutant pl_exists pending
    by (simp add: pl_visible_mass_def pl_pending_def pl_release_def add.assoc)
  show "pl_step True request state = (state,PL_Rejected)" by (rule pl_normal)
  show "pl_step False request state =
      ((pl_release PL_Reconciled state)\<lparr>pls_revision := Suc (pls_revision state)\<rparr>,PL_Reconciled_Reply)"
    by (rule pl_mutant)
  show "pl_pending (fst (pl_step False request state)) = 0"
    by (simp add: pl_mutant pl_pending_def pl_release_def)
  show "pl_visible_mass (fst (pl_step False request state)) + pl_amount (pls_binding state) = pl_visible_mass state"
    by (rule pl_mass)
  show "pl_visible_mass (fst (pl_step False request state)) < pl_visible_mass state"
    using pl_mass amount by arith
  show "map_of (pls_active (fst (pl_step False request state))) (pl_asset (pls_binding state)) = None"
    using member
    by (simp add: pl_mutant pl_release_def pl_removed_footprint_member_has_no_active_entry)
qed

text \<open>
  The generic phase-only removal contract and native frames are kernel checked.
  The four concrete predicates above retain the exact frozen setup/program and
  are evaluated in generated standalone SML, not by expensive ground kernel
  normalization. A true standalone readiness/pair is a finite nonvacuity and
  mutation-reach observation with compiler/runtime and typed-seed boundaries.
\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      pl_pending_cancel_and_fence_are_full_native_stutters
      pl_preempt_preserves_source_obligation_and_evidence
      pl_native_timeout_has_no_financial_or_release_authority
      pl_confirmed_attestation_is_not_prior_credit
      pl_reconcile_preserves_balances_and_terminal_records
      pl_credit_prefix_preserves_the_active_lock
      pl_phase_only_guard_removal_has_a_typed_counterexample_contract})
  then () else error "Unexpected oracle in native pending-lock G0"
\<close>

end
