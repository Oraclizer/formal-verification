theory Pending_Lock_Model
  imports "OIP_Reference_Execution.Reference_Lock_Code"
    "OIP_Product_Base.Lock_Release" "OIP_Product_Base.Lock_Footprint"
begin

record pl_binding =
  pl_origin :: "nat \<times> nat"
  pl_asset :: nat
  pl_owner :: nat
  pl_destination :: nat
  pl_recipient :: nat
  pl_amount :: nat

datatype pl_phase = PL_Held | PL_Dispatched | PL_Pending | PL_Credited | PL_Reconciled | PL_Refunded | PL_Closed
datatype pl_evidence_kind = PL_Confirmed | PL_Reversed
datatype pl_command = PL_Cancel nat | PL_Fence nat | PL_Preempt nat | PL_Time nat | PL_Reconcile nat nat
datatype pl_reply = PL_Rejected | PL_Closed_Reply | PL_Preempted | PL_Time_Observed | PL_Reconciled_Reply

record pl_credential =
  plc_asset :: nat
  plc_origin :: "nat \<times> nat"
  plc_holder :: nat
  plc_generation :: nat
  plc_epoch :: nat

record pl_state =
  pls_binding :: pl_binding
  pls_exists :: bool
  pls_epoch :: nat
  pls_revision :: nat
  pls_clock :: nat
  pls_holder :: nat
  pls_generation :: nat
  pls_expires :: nat
  pls_phase :: pl_phase
  pls_footprint :: "nat list"
  pls_active :: "(nat \<times> (nat \<times> nat)) list"
  pls_versions :: "(nat \<times> nat) list"
  pls_assets :: "nat list"
  pls_contexts :: "nat list"
  pls_sessions :: "(nat \<times> (nat \<times> nat)) list"
  pls_grants :: "(nat \<times> nat \<times> nat) list"
  pls_connected :: bool
  pls_terminal :: "nat option"
  pls_evidence :: "(nat \<times> (pl_binding \<times> pl_evidence_kind)) list"
  pls_source :: nat
  pls_destination_balance :: nat
  pls_root_funding :: nat

record pl_request =
  plr_binding :: pl_binding
  plr_actor :: nat
  plr_caller :: nat
  plr_session :: nat
  plr_endpoint :: nat
  plr_cut_epoch :: nat
  plr_cut_revision :: nat
  plr_route :: nat
  plr_verified :: bool
  plr_credential :: "pl_credential option"
  plr_versions :: "(nat \<times> nat) list"
  plr_command :: pl_command

fun pl_permission :: "pl_command \<Rightarrow> nat" where
  "pl_permission (PL_Cancel g) = 0"
| "pl_permission (PL_Fence g) = 1"
| "pl_permission (PL_Preempt d) = 2"
| "pl_permission (PL_Time elapsed) = 3"
| "pl_permission (PL_Reconcile g reference) = 4"

fun pl_generation_requirement :: "pl_command \<Rightarrow> nat option" where
  "pl_generation_requirement (PL_Cancel g) = Some g"
| "pl_generation_requirement (PL_Fence g) = Some g"
| "pl_generation_requirement (PL_Reconcile g reference) = Some g"
| "pl_generation_requirement command = None"

definition pl_value_at where
  "pl_value_at rows key = (case map_of rows key of None \<Rightarrow> 0 | Some value \<Rightarrow> value)"

definition pl_owns_footprint where
  "pl_owns_footprint state \<longleftrightarrow>
    list_all (\<lambda>asset. map_of (pls_active state) asset = Some (pl_origin (pls_binding state))) (pls_footprint state)"

definition pl_versions_match where
  "pl_versions_match request state \<longleftrightarrow>
    list_all (\<lambda>asset. pl_value_at (plr_versions request) asset = pl_value_at (pls_versions state) asset) (pls_footprint state)"

definition pl_request_admitted where
  "pl_request_admitted request state \<longleftrightarrow>
    pls_connected state \<and> plr_caller request = plr_actor request \<and>
    plr_cut_epoch request = pls_epoch state \<and> plr_cut_revision request = pls_revision state \<and>
    plr_endpoint request = fst (pl_origin (plr_binding request)) \<and>
    pl_asset (plr_binding request) \<in> set (pls_assets state) \<and>
    pl_destination (plr_binding request) \<in> set (pls_contexts state) \<and>
    plr_endpoint request \<in> set (pls_contexts state) \<and>
    (plr_actor request,plr_route request,pl_permission (plr_command request)) \<in> set (pls_grants state) \<and>
    map_of (pls_sessions state) (plr_session request) = Some (plr_actor request,pls_epoch state)"

definition pl_bound_credential where
  "pl_bound_credential request state generation \<longleftrightarrow>
    pls_exists state \<and> pls_binding state = plr_binding request \<and>
    (case plr_credential request of None \<Rightarrow> False | Some token \<Rightarrow>
      plc_asset token = pl_asset (plr_binding request) \<and> plc_origin token = pl_origin (plr_binding request) \<and>
      plc_holder token = pls_holder state \<and> pls_holder state = plr_actor request \<and>
      plc_generation token = pls_generation state \<and> generation = pls_generation state \<and>
      plc_epoch token = pls_epoch state)"

definition pl_effect_credential where
  "pl_effect_credential request state \<longleftrightarrow>
    (case pl_generation_requirement (plr_command request) of None \<Rightarrow> plr_credential request = None
     | Some generation \<Rightarrow> pl_bound_credential request state generation \<and>
       map_of (pls_active state) (pl_asset (plr_binding request)) = Some (pl_origin (plr_binding request)) \<and>
       pl_owns_footprint state \<and> pl_versions_match request state)"

definition pl_receipt_credential where
  "pl_receipt_credential request state \<longleftrightarrow>
    (case pl_generation_requirement (plr_command request) of None \<Rightarrow> plr_credential request = None
     | Some generation \<Rightarrow> pl_bound_credential request state generation)"

definition pl_exact_confirmed where
  "pl_exact_confirmed state reference \<longleftrightarrow>
    pls_terminal state \<noteq> None \<and>
    (case map_of (pls_evidence state) reference of None \<Rightarrow> False
     | Some (binding,kind) \<Rightarrow> kind = PL_Confirmed \<and> binding = pls_binding state)"

definition pl_release where
  "pl_release phase state = state\<lparr>pls_active := filter (\<lambda>(asset,key). asset \<notin> set (pls_footprint state)) (pls_active state),
      pls_phase := phase\<rparr>"

definition pl_apply where
  "pl_apply require_credit_phase request state =
    (if \<not> pls_exists state \<or> plr_binding request \<noteq> pls_binding state then (state,PL_Rejected)
     else case plr_command request of
       PL_Cancel g \<Rightarrow> if pls_phase state = PL_Held \<and> pls_clock state < pls_expires state
         then (pl_release PL_Closed state,PL_Closed_Reply) else (state,PL_Rejected)
     | PL_Fence g \<Rightarrow> if pls_phase state = PL_Dispatched \<and> pls_clock state < pls_expires state
         then (pl_release PL_Closed state,PL_Closed_Reply) else (state,PL_Rejected)
     | PL_Preempt duration \<Rightarrow>
         if pls_clock state + duration < 2^64 \<and> Suc (pls_generation state) < 2^64 \<and>
            duration > 0 \<and> pls_expires state \<le> pls_clock state \<and> pl_owns_footprint state
         then (state\<lparr>pls_holder := plr_actor request,pls_generation := Suc (pls_generation state),
                pls_expires := pls_clock state + duration\<rparr>,PL_Preempted) else (state,PL_Rejected)
     | PL_Time elapsed \<Rightarrow> if pls_clock state + elapsed < 2^64
         then (state\<lparr>pls_clock := pls_clock state + elapsed\<rparr>,PL_Time_Observed) else (state,PL_Rejected)
     | PL_Reconcile g reference \<Rightarrow>
         if (\<not> require_credit_phase \<or> pls_phase state = PL_Credited) \<and>
            pls_clock state < pls_expires state \<and> pl_exact_confirmed state reference
         then (pl_release PL_Reconciled state,PL_Reconciled_Reply) else (state,PL_Rejected))"

definition pl_step where
  "pl_step require_credit_phase request state =
    (if Suc (pls_revision state) \<ge> 2^64 \<or> \<not> pl_request_admitted request state \<or>
        \<not> plr_verified request \<or> \<not> pl_effect_credential request state then (state,PL_Rejected)
     else let (next,reply) = pl_apply require_credit_phase request state in
       if reply = PL_Rejected then (next,reply)
       else (next\<lparr>pls_revision := Suc (pls_revision state)\<rparr>,reply))"

definition pl_pending where
  "pl_pending state = (if pls_exists state \<and> pls_phase state = PL_Pending then pl_amount (pls_binding state) else 0)"

definition pl_visible_mass where
  "pl_visible_mass state = pls_source state + pls_destination_balance state + pl_pending state"

lemma pl_pending_cancel_and_fence_are_full_native_stutters:
  assumes "pls_phase state = PL_Pending"
  shows "plr_command request = PL_Cancel g \<Longrightarrow> pl_step True request state = (state,PL_Rejected)"
    "plr_command request = PL_Fence g \<Longrightarrow> pl_step True request state = (state,PL_Rejected)"
  using assms by (auto simp: pl_step_def pl_apply_def Let_def split: if_splits)

lemma pl_preempt_preserves_source_obligation_and_evidence:
  fixes state :: pl_state
  assumes "plr_command request = PL_Preempt duration"
  defines "after \<equiv> fst (pl_step True request state)"
  shows "pls_binding after = pls_binding state" "pls_phase after = pls_phase state"
    "pls_source after = pls_source state" "pls_destination_balance after = pls_destination_balance state"
    "pl_pending after = pl_pending state" "pls_terminal after = pls_terminal state"
    "pls_evidence after = pls_evidence state" "pls_root_funding after = pls_root_funding state"
    "pls_active after = pls_active state"
  using assms by (auto simp: after_def pl_step_def pl_apply_def pl_pending_def Let_def split: if_splits)

lemma pl_native_timeout_has_no_financial_or_release_authority:
  fixes state :: pl_state
  assumes "plr_command request = PL_Time elapsed"
  defines "after \<equiv> fst (pl_step True request state)"
  shows "pls_source after = pls_source state" "pls_destination_balance after = pls_destination_balance state"
    "pl_pending after = pl_pending state" "pls_phase after = pls_phase state"
    "pls_holder after = pls_holder state" "pls_generation after = pls_generation state"
    "pls_active after = pls_active state" "pls_terminal after = pls_terminal state"
    "pls_evidence after = pls_evidence state"
  using assms by (auto simp: after_def pl_step_def pl_apply_def pl_pending_def Let_def split: if_splits)

lemma pl_confirmed_attestation_is_not_prior_credit:
  assumes "plr_command request = PL_Reconcile g reference" "pls_phase state \<noteq> PL_Credited"
  shows "pl_step True request state = (state,PL_Rejected)"
  using assms by (auto simp: pl_step_def pl_apply_def Let_def split: if_splits)

lemma pl_reconcile_preserves_balances_and_terminal_records:
  fixes state :: pl_state
  assumes "plr_command request = PL_Reconcile g reference"
  defines "after \<equiv> fst (pl_step True request state)"
  shows "pls_source after = pls_source state" "pls_destination_balance after = pls_destination_balance state"
    "pls_evidence after = pls_evidence state" "pls_terminal after = pls_terminal state"
    "pls_root_funding after = pls_root_funding state"
  using assms by (auto simp: after_def pl_step_def pl_apply_def pl_release_def Let_def split: if_splits)

lemma pl_refreshed_reference_may_differ_from_primary:
  assumes "pls_terminal state = Some primary" "map_of (pls_evidence state) reference = Some (pls_binding state,PL_Confirmed)"
  shows "pl_exact_confirmed state reference"
  using assms by (simp add: pl_exact_confirmed_def)

lemma pl_old_generation_cannot_pass_bound_credential:
  assumes "plr_credential request = Some token" "plc_generation token \<noteq> pls_generation state"
  shows "\<not> pl_bound_credential request state generation"
  using assms by (simp add: pl_bound_credential_def)

lemma pl_old_epoch_cannot_pass_bound_credential:
  assumes "plr_credential request = Some token" "plc_epoch token \<noteq> pls_epoch state"
  shows "\<not> pl_bound_credential request state generation"
  using assms by (simp add: pl_bound_credential_def)

text \<open>
  This is the finite native release/maintenance slice of src/lock_finality.rs.
  The verification Boolean is a named trusted-fixture callback boundary. The
  model checks typed current caller/session/cut/grant and lease inputs itself.
  It is not an envelope verifier, persistent-result model or arbitrary ledger
  serializer. Prefix establishment and the before-state must be compared at
  the actual source consumer. Native Phase::Credited must not be confused with
  the abstract reservation phase that also carries a separate credit history.
\<close>

context source_attestation
begin

lemmas pl_public_pending_cancel = actual_cancel_cannot_release_a_pending_source
lemmas pl_public_pending_fence = actual_fence_cannot_release_a_debited_source
lemmas pl_public_reassignment_frame = actual_reassignment_preserves_pending_and_source_evidence
lemmas pl_public_timeout_frame = actual_finality_timeout_preserves_pending_and_balances
lemmas pl_public_prior_credit_guard = actual_reconcile_requires_prior_exact_credit
lemmas pl_public_reconcile_financial_frame = actual_reconcile_does_not_move_funds
lemmas pl_public_expired_lease_guard = expired_lease_cannot_refund_or_reconcile

end

end
