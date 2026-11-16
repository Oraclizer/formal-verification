theory Rollback_Trade_Examples
  imports Rollback_Trade_Recovery
begin

definition flagged_repair_start :: "nat recovery_state" where
  "flagged_repair_start = repair_start\<lparr>rollback_incomplete := True\<rparr>"

definition resync_approval :: nat where "resync_approval = 3"

definition resynced_end :: "nat recovery_state" where
  "resynced_end = (install_replica flagged_repair_start 7 1)\<lparr>
    rollback_incomplete := pending_ids (install_replica flagged_repair_start 7 1) \<noteq> {}\<rparr>"

lemma resync_reaches_actual_installation:
  "recovery_step {} {3} flagged_repair_start (Governance_Resync resync_approval 7 20)
    (Accepted (Installed 7 1 20)) resynced_end"
  unfolding resynced_end_def
  by (rule recovery_step.Authorized_Resync)
     (simp_all add: resync_approval_def flagged_repair_start_def repair_start_def)

lemma resynced_end_has_no_pending_work:
  "pending_ids resynced_end = {}"
  by (simp add: resynced_end_def install_replica_def flagged_repair_start_def repair_start_def pending_ids_def dom_def)

lemma ordinary_trade_follows_resync:
  "recovery_step {} {3} resynced_end (Ordinary_Trade 23) (Accepted (Traded 23)) resynced_end"
  by (rule final_install_admits_trade_and_preserves_facts(1)[
    OF resync_reaches_actual_installation resynced_end_has_no_pending_work])

definition resync_then_trade_run :: "nat \<Rightarrow> nat repair_event" where
  "resync_then_trade_run i =
    (if i = 0 then mk_event flagged_repair_start (Governance_Resync resync_approval 7 20)
       (Accepted (Installed 7 1 20)) resynced_end
     else if i = 1 then mk_event resynced_end (Ordinary_Trade 23) (Accepted (Traded 23)) resynced_end
     else mk_event resynced_end Wait_For_Source (Internal ()) resynced_end)"

lemma flagged_repair_start_is_valid:
  "flagged_repair_start \<in> recovery_carrier"
  using repair_start_well_formed
  by (simp add: flagged_repair_start_def recovery_carrier_def replica_covered_def pending_ids_def)

theorem resync_then_trade_is_an_actual_run:
  "infinite_run (recovery_step {} {3}) {flagged_repair_start} recovery_carrier resync_then_trade_run"
  "step_outcome (resync_then_trade_run 1) = Accepted (Traded 23)"
  "irreversible_facts resynced_end = irreversible_facts flagged_repair_start"
proof -
  have final_valid: "resynced_end \<in> recovery_carrier"
    by (rule recovery_carrier_closed[OF resync_reaches_actual_installation flagged_repair_start_is_valid])
  show "infinite_run (recovery_step {} {3}) {flagged_repair_start} recovery_carrier resync_then_trade_run"
    using final_valid flagged_repair_start_is_valid resync_reaches_actual_installation ordinary_trade_follows_resync
    by (auto simp: infinite_run_def step_occurs_def resync_then_trade_run_def mk_event_def
        split: if_splits intro: recovery_step.Idle)
  show "step_outcome (resync_then_trade_run 1) = Accepted (Traded 23)"
    by (simp add: resync_then_trade_run_def mk_event_def)
  show "irreversible_facts resynced_end = irreversible_facts flagged_repair_start"
    by (rule recovery_never_changes_irreversible_facts[OF resync_reaches_actual_installation])
qed

lemma resync_example_activates_reopening_under_finite_interference:
  "\<exists>n. \<forall>i\<ge>n. \<forall>tx.
    recovery_step {} {3} (source_state (resync_then_trade_run i)) (Ordinary_Trade tx)
      (Accepted (Traded tx)) (source_state (resync_then_trade_run i))"
proof (rule recorded_rollback_admits_offered_trades_after_work_drains[OF resync_then_trade_is_an_actual_run(1)])
  show "rollback_work_invariant (source_state (resync_then_trade_run 0))"
    by (simp add: resync_then_trade_run_def mk_event_def rollback_work_invariant_def
        flagged_repair_start_def repair_start_def pending_ids_def dom_def)
  have no_interference: "\<And>i. \<not> affects_recovery (resync_then_trade_run i)"
    by (auto simp: resync_then_trade_run_def mk_event_def affects_recovery_def split: if_splits)
  show "finite {i. affects_recovery (resync_then_trade_run i)}" by (simp add: no_interference)
next
  fix i assume "\<And>j. i \<le> j \<Longrightarrow> \<not> affects_recovery (resync_then_trade_run j)"
    and pending: "pending_ids (source_state (resync_then_trade_run i)) \<noteq> {}"
  have "i = 0" using pending resynced_end_has_no_pending_work
    by (auto simp: resync_then_trade_run_def mk_event_def split: if_splits)
  then show "\<exists>j\<ge>i. \<exists>w d seq. step_outcome (resync_then_trade_run j) = Accepted (Installed w d seq)"
    by (intro exI[of _ 0]) (simp add: resync_then_trade_run_def mk_event_def)
qed

definition flagged_without_work :: "nat recovery_state" where
  "flagged_without_work = repair_end\<lparr>rollback_incomplete := True\<rparr>"

definition blocked_trade_run :: "nat \<Rightarrow> nat repair_event" where
  "blocked_trade_run = (\<lambda>_. mk_event flagged_without_work (Ordinary_Trade 23)
     (Rejected Recovery_Blocks_Trade) flagged_without_work)"

theorem empty_pending_does_not_imply_trade_admission:
  "infinite_run (recovery_step {} {3}) {flagged_without_work} recovery_carrier blocked_trade_run"
  "pending_ids flagged_without_work = {}"
  "\<forall>i. pending_ids (source_state (blocked_trade_run i)) = {}"
  "finite {i. affects_recovery (blocked_trade_run i)}"
  "\<forall>i. step_outcome (blocked_trade_run i) = Rejected Recovery_Blocks_Trade"
  "\<not> recovery_step {} {3} flagged_without_work (Ordinary_Trade 23)
     (Accepted (Traded 23)) flagged_without_work"
  "\<not> recovery_step {} {3} flagged_without_work (Governance_Resync 3 7 20)
     (Accepted (Installed 7 1 20)) t"
proof -
  have valid: "flagged_without_work \<in> recovery_carrier" using repair_end_well_formed
    by (simp add: flagged_without_work_def recovery_carrier_def replica_covered_def pending_ids_def)
  have flagged: "rollback_incomplete flagged_without_work" by (simp add: flagged_without_work_def)
  have refuses: "recovery_step {} {3} flagged_without_work (Ordinary_Trade 23)
    (Rejected Recovery_Blocks_Trade) flagged_without_work"
    by (rule recovery_step.Refuse_Trade) (rule disjI2[OF flagged])
  show "infinite_run (recovery_step {} {3}) {flagged_without_work} recovery_carrier blocked_trade_run"
    using valid refuses by (simp add: infinite_run_def step_occurs_def blocked_trade_run_def mk_event_def)
  show no_pending: "pending_ids flagged_without_work = {}"
    by (simp add: flagged_without_work_def repair_end_def install_replica_def repair_start_def pending_ids_def dom_def)
  show "\<forall>i. pending_ids (source_state (blocked_trade_run i)) = {}"
    by (simp add: no_pending blocked_trade_run_def mk_event_def)
  show "finite {i. affects_recovery (blocked_trade_run i)}"
    by (simp add: affects_recovery_def blocked_trade_run_def mk_event_def)
  show "\<forall>i. step_outcome (blocked_trade_run i) = Rejected Recovery_Blocks_Trade"
    by (simp add: blocked_trade_run_def mk_event_def)
  show "\<not> recovery_step {} {3} flagged_without_work (Ordinary_Trade 23) (Accepted (Traded 23)) flagged_without_work"
    using flagged by (simp add: trade_is_admitted_iff_drained_and_rollback_clear)
  show "\<not> recovery_step {} {3} flagged_without_work (Governance_Resync 3 7 20) (Accepted (Installed 7 1 20)) t"
    by (rule no_install_without_pending_work[OF no_pending])
qed

end
