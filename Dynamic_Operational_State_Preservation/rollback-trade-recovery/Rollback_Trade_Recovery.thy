theory Rollback_Trade_Recovery
  imports DOSP_Recovery.Recovery_Examples
begin

definition rollback_work_invariant :: "'d recovery_state \<Rightarrow> bool" where
  "rollback_work_invariant s \<longleftrightarrow> (rollback_incomplete s \<longrightarrow> pending_ids s \<noteq> {})"

lemma recovery_preserves_rollback_work:
  assumes step: "recovery_step grants governance s a r t"
    and recorded: "rollback_work_invariant s"
  shows "rollback_work_invariant t"
  using step recorded
  by (cases rule: recovery_step.cases)
     (auto simp: rollback_work_invariant_def pending_ids_def install_replica_def)

lemma trade_is_admitted_iff_drained_and_rollback_clear:
  "recovery_step grants governance s (Ordinary_Trade tx) (Accepted (Traded tx)) s \<longleftrightarrow>
    pending_ids s = {} \<and> \<not> rollback_incomplete s"
proof
  assume "recovery_step grants governance s (Ordinary_Trade tx) (Accepted (Traded tx)) s"
  then show "pending_ids s = {} \<and> \<not> rollback_incomplete s" by (cases rule: recovery_step.cases) auto
next
  assume "pending_ids s = {} \<and> \<not> rollback_incomplete s"
  then show "recovery_step grants governance s (Ordinary_Trade tx) (Accepted (Traded tx)) s"
    by (auto intro: recovery_step.Admit_Trade)
qed

theorem final_install_admits_trade_and_preserves_facts:
  assumes installed: "recovery_step grants governance s a (Accepted (Installed work d sequence)) t"
    and drained: "pending_ids t = {}"
  shows "recovery_step grants governance t (Ordinary_Trade tx) (Accepted (Traded tx)) t"
    and "irreversible_facts t = irreversible_facts s"
proof -
  have cleared: "\<not> rollback_incomplete t"
    using installed drained by (cases rule: recovery_step.cases) (auto simp: pending_ids_def install_replica_def)
  show "recovery_step grants governance t (Ordinary_Trade tx) (Accepted (Traded tx)) t"
    by (rule recovery_step.Admit_Trade[OF drained cleared])
  show "irreversible_facts t = irreversible_facts s"
    by (rule recovery_never_changes_irreversible_facts[OF installed])
qed

lemma no_install_without_pending_work:
  assumes "pending_ids s = {}"
  shows "\<not> recovery_step grants governance s a (Accepted (Installed work d sequence)) t"
proof
  assume "recovery_step grants governance s a (Accepted (Installed work d sequence)) t"
  then have "work_owner s work = Some d" by (meson actual_install_uses_primary_record)
  with assms show False by (auto simp: pending_ids_def dom_def)
qed

lemma run_preserves_rollback_work:
  fixes events :: "nat \<Rightarrow> 'd repair_event"
  assumes run: "infinite_run (recovery_step grants governance) initial recovery_carrier events"
    and start: "rollback_work_invariant (source_state (events 0))"
  shows "rollback_work_invariant (source_state (events i))"
proof (induction i)
  case 0
  show ?case by (rule start)
next
  case (Suc i)
  have step: "step_occurs (recovery_step grants governance) (events i)"
    and link: "target_state (events i) = source_state (events (Suc i))"
    using run by (simp_all add: infinite_run_def)
  have actual: "recovery_step grants governance (source_state (events i)) (step_action (events i))
      (step_outcome (events i)) (source_state (events (Suc i)))"
    using step by (simp only: step_occurs_def link)
  show ?case by (rule recovery_preserves_rollback_work[OF actual Suc.IH])
qed

theorem recorded_rollback_admits_offered_trades_after_work_drains:
  fixes events :: "nat \<Rightarrow> 'd repair_event"
  assumes run: "infinite_run (recovery_step grants governance) initial recovery_carrier events"
    and recorded: "rollback_work_invariant (source_state (events 0))"
    and finite_interference: "finite {i. affects_recovery (events i)}"
    and selected:
      "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> affects_recovery (events j)) \<Longrightarrow>
       pending_ids (source_state (events i)) \<noteq> {} \<Longrightarrow>
       \<exists>j\<ge>i. \<exists>w d seq. step_outcome (events j) = Accepted (Installed w d seq)"
  shows "\<exists>n. \<forall>i\<ge>n. \<forall>tx.
    recovery_step grants governance (source_state (events i)) (Ordinary_Trade tx)
      (Accepted (Traded tx)) (source_state (events i))"
proof -
  from recovery_finishes_under_finite_interference[OF run finite_interference selected]
  obtain n where settled: "\<forall>i\<ge>n.
    pending_ids (source_state (events i)) = {} \<and>
    (\<forall>d\<in>active_domains (source_state (events i)).
       replica (source_state (events i)) d = primary_record (source_state (events i))) \<and>
    (\<forall>j\<le>i. pending_ids (source_state (events j)) \<union> completion_log (source_state (events j))
       \<subseteq> completion_log (source_state (events i)))" ..
  show ?thesis
  proof (rule exI[of _ n], intro allI impI)
    fix i tx assume late: "n \<le> i"
    have drained: "pending_ids (source_state (events i)) = {}"
      by (rule conjunct1[OF settled[rule_format, OF late]])
    have still_recorded: "rollback_work_invariant (source_state (events i))"
      by (rule run_preserves_rollback_work[OF run recorded])
    have cleared: "\<not> rollback_incomplete (source_state (events i))"
      using still_recorded drained by (simp add: rollback_work_invariant_def)
    show "recovery_step grants governance (source_state (events i)) (Ordinary_Trade tx)
      (Accepted (Traded tx)) (source_state (events i))"
      by (rule recovery_step.Admit_Trade[OF drained cleared])
  qed
qed

end
