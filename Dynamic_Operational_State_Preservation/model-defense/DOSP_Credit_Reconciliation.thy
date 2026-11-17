theory DOSP_Credit_Reconciliation
  imports DOSP_Consensus_Billing_Cases
begin

datatype reconciliation_lease = Live_Lease nat version_vector | Expired_Lease nat

fun reconcile_confirmed_command where
  "reconcile_confirmed_command (Live_Lease generation versions) index r = Reconcile_Current_Lock index r generation versions"
| "reconcile_confirmed_command (Expired_Lease duration) index r = Settle_Lock Reconcile_Credit index r duration"

context integrated_dosp_authority
begin

definition clear_confirmed_custody where
  "clear_confirmed_custody s a lease index r released t b \<longleftrightarrow>
    (let request = request_binding r;
         confirmed = (lifecycle_phase s = Idle_Cycle \<and> lifecycle_session s = active_session \<and>
           cycle_custody s = Native_Debit_Pending (binding_key request) \<and>
           lifecycle_cutover s = degree_state (current_operational a) \<and>
           binding_asset request = registered_asset (current_operational a) \<and>
           fst (lifecycle_session s) = binding_asset request);
         native = execute_integrated_client (reconcile_confirmed_command lease index r) a
     in if confirmed \<and> snd native = Lock_Result Reservation_Released then
       released \<and> t = s\<lparr>cycle_custody := Local_Cells_Only\<rparr> \<and> b = fst native
     else \<not> released \<and> t = s \<and> b = a)"

lemma confirmed_custody_cannot_release_by_a_different_key:
  assumes "cycle_custody s \<noteq> Native_Debit_Pending (binding_key (request_binding r))"
  shows "clear_confirmed_custody s a lease index r released t b \<longleftrightarrow> \<not> released \<and> t = s \<and> b = a"
  using assms by (simp add: clear_confirmed_custody_def Let_def)

lemma accepted_custody_cleanup_preserves_the_public_and_native_bills:
  assumes cleanup: "clear_confirmed_custody s a lease index r True t b"
  shows "cycle_custody t = Local_Cells_Only \<and> lifecycle_invoice t = lifecycle_invoice s \<and>
    committed_cycles (metered_ledger b) = committed_cycles (metered_ledger a) \<and>
    lifecycle_cutover t = lifecycle_cutover s \<and> degree_state (current_operational b) = degree_state (current_operational a)"
proof -
  have local: "t = s\<lparr>cycle_custody := Local_Cells_Only\<rparr>"
    and native: "execute_integrated_client (reconcile_confirmed_command lease index r) a = (b, Lock_Result Reservation_Released)"
    using cleanup by (auto simp: clear_confirmed_custody_def Let_def split: if_splits intro: prod_eqI)
  have history: "committed_cycles (metered_ledger b) = committed_cycles (metered_ledger a) \<and>
    degree_state (current_operational b) = degree_state (current_operational a)"
  proof (cases lease)
    case Live_Lease
    then show ?thesis using native by (auto simp: Let_def with_finality_core_def with_operational_state_def)
  next
    case (Expired_Lease duration)
    let ?state = "current_operational a"
    let ?result = "resolve_cutover_lock Reconcile_Credit (core_epoch (credit_core ?state)) index r duration ?state"
    have evaluated: "?result = (fst ?result, snd ?result)" by simp
    have preserves: "degree_state (fst ?result) = degree_state ?state"
      using lock_resolution_keeps_the_cutover_and_durable_publication[OF evaluated] by blast
    show ?thesis using Expired_Lease native preserves
      by (auto simp: Let_def with_operational_state_def)
  qed
  show ?thesis using local history by simp
qed

end

abbreviation first_custody_view where
  "first_custody_view \<equiv> episode_initial\<lparr>lifecycle_cutover := degree_state (current_operational after_first_meter),
    cycle_custody := Native_Debit_Pending (0,17)\<rparr>"

theorem actual_confirmed_credit_releases_its_own_custody_without_rebilling:
  "\<exists>t b. joined_dosp.clear_confirmed_custody first_custody_view after_first_meter (Live_Lease 0 []) 0 (sample_request 17)
      True t b \<and> cycle_custody t = Local_Cells_Only \<and>
    asset_owner (machine_state (core_parent (credit_core (current_operational b)))) 17 = None \<and>
    committed_cycles (metered_ledger b) = committed_cycles (metered_ledger after_first_meter)"
proof -
  let ?core = "(finality_sample_certified 17)\<lparr>core_parent := sample_credited,core_epoch := 8, core_published := {(0,17)}\<rparr>"
  let ?b = "with_finality_core ?core after_first_meter"
  have operational: "current_operational after_first_meter = fst metered_fixture_result"
    unfolding after_first_meter_shape(1) first_meter_ledger by simp
  have core: "credit_core (current_operational after_first_meter) = first_paid_core"
    by (simp only: operational first_paid_authority eab_primary_authority.select_convs)
  have actual: "joined_dosp.execute_integrated_client close_first_lock after_first_meter = (?b, Lock_Result Reservation_Released)"
    using first_paid_reconciliation by (simp add: core Let_def)
  have accepted: "joined_dosp.clear_confirmed_custody first_custody_view after_first_meter (Live_Lease 0 []) 0 (sample_request 17)
      True (first_custody_view\<lparr>cycle_custody := Local_Cells_Only\<rparr>) ?b"
    by (simp only: joined_dosp.clear_confirmed_custody_def Let_def reconcile_confirmed_command.simps
      actual fst_conv snd_conv; simp add: episode_initial_def fixture_binding operational first_metered_operational_fields)
  have unlocked: "asset_owner (machine_state (core_parent (credit_core (current_operational ?b)))) 17 = None"
    by (simp add: with_finality_core_def with_operational_state_def)
  show ?thesis using accepted unlocked joined_dosp.accepted_custody_cleanup_preserves_the_public_and_native_bills[OF accepted]
    by blast
qed

end
