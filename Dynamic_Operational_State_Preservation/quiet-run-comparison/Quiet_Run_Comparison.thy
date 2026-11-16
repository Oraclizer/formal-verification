theory Quiet_Run_Comparison
  imports DOSP_Atomic_Comparison.Atomic_Comparison
begin

definition quiet_replica_frame :: "'d recovery_state \<Rightarrow> 'd recovery_state \<Rightarrow> bool" where
  "quiet_replica_frame initial s \<longleftrightarrow>
     active_domains s \<subseteq> active_domains initial \<and>
     primary_record s = primary_record initial \<and>
     primary_sequence s = primary_sequence initial \<and>
     irreversible_facts s = irreversible_facts initial \<and>
     preserves_outside replica (active_domains initial) initial s \<and>
     (\<forall>d\<in>active_domains initial.
        replica s d \<noteq> primary_record initial \<longrightarrow> (\<exists>i. work_owner s i = Some d))"

lemma initial_quiet_replica_frame:
  assumes "s \<in> recovery_carrier"
  shows "quiet_replica_frame s s"
  using assms by (simp add: quiet_replica_frame_def recovery_carrier_def replica_covered_def preserves_outside_def)

lemma install_keeps_quiet_replica_frame:
  assumes frame: "quiet_replica_frame initial s"
    and active: "d \<in> active_domains s"
    and owned: "work_owner s job = Some d"
  shows "quiet_replica_frame initial (install_replica s job d)"
proof -
  have in_initial: "d \<in> active_domains initial"
    using active frame by (auto simp: quiet_replica_frame_def)
  have same_record: "primary_record s = primary_record initial"
    using frame by (simp add: quiet_replica_frame_def)
  have covered: "\<And>x. x \<in> active_domains initial \<Longrightarrow>
      replica (install_replica s job d) x \<noteq> primary_record initial \<Longrightarrow>
      \<exists>i. work_owner (install_replica s job d) i = Some x"
  proof -
    fix x assume dx: "x \<in> active_domains initial"
      and differs: "replica (install_replica s job d) x \<noteq> primary_record initial"
    have other: "x \<noteq> d" using differs same_record by (auto simp: install_replica_def)
    have old_differs: "replica s x \<noteq> primary_record initial"
      using differs other by (simp add: install_replica_def)
    obtain i where work: "work_owner s i = Some x"
      using frame dx old_differs by (auto simp: quiet_replica_frame_def)
    have "i \<noteq> job" using work owned other by auto
    then show "\<exists>i. work_owner (install_replica s job d) i = Some x"
      using work by (auto simp: install_replica_def)
  qed
  show ?thesis using frame in_initial covered
    by (auto simp: quiet_replica_frame_def install_replica_def preserves_outside_def)
qed

lemma unowned_departure_keeps_quiet_replica_frame:
  assumes frame: "quiet_replica_frame initial s" and unowned: "\<nexists>i. work_owner s i = Some old"
  shows "quiet_replica_frame initial (s\<lparr>active_domains := active_domains s - {old},
    route_epoch := epoch, work_owner := carry_owner old successor (work_owner s)\<rparr>)"
proof -
  have same_owners: "carry_owner old successor (work_owner s) = work_owner s"
  proof (rule ext)
    fix j
    have "work_owner s j \<noteq> Some old" using unowned by blast
    then show "carry_owner old successor (work_owner s) j = work_owner s j"
      by (simp add: carry_owner_def)
  qed
  show ?thesis using same_owners frame by (auto simp: quiet_replica_frame_def preserves_outside_def)
qed

lemma quiet_replica_frame_ignores_recovery_flag:
  "quiet_replica_frame initial (s\<lparr>rollback_incomplete := flag\<rparr>) = quiet_replica_frame initial s"
  by (simp add: quiet_replica_frame_def preserves_outside_def)

lemma quiet_step_keeps_replica_frame:
  assumes occurs: "step_occurs (recovery_step grants governance) e"
    and quiet: "\<not> affects_recovery e"
    and frame: "quiet_replica_frame initial (source_state e)"
  shows "quiet_replica_frame initial (target_state e)"
  using occurs unfolding step_occurs_def
proof (cases rule: recovery_step.cases)
  case Join_Route
  then show ?thesis using quiet by (simp add: affects_recovery_def)
next
  case Leave_Route
  then show ?thesis using quiet frame
    by (auto simp: affects_recovery_def intro: unowned_departure_keeps_quiet_replica_frame)
next
  case Detect_Divergence
  then show ?thesis using quiet by (simp add: affects_recovery_def)
next
  case Ordinary_Repair
  then show ?thesis using frame
    by (auto intro: install_keeps_quiet_replica_frame)
next
  case Authorized_Resync
  then show ?thesis using frame
    by (auto simp: quiet_replica_frame_ignores_recovery_flag intro: install_keeps_quiet_replica_frame)
qed (use frame in auto)

lemma quiet_trace_keeps_replica_frame:
  assumes trace: "finite_trace (recovery_step grants governance) recovery_carrier s es t"
    and quiet: "\<And>e. e \<in> set es \<Longrightarrow> \<not> affects_recovery e"
    and frame: "quiet_replica_frame initial s"
  shows "quiet_replica_frame initial t"
  using trace quiet frame
proof (induction es arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  have head: "step_occurs (recovery_step grants governance) e"
    and from_s: "source_state e = s"
    and tail: "finite_trace (recovery_step grants governance) recovery_carrier (target_state e) es t"
    using Cons.prems(1) by simp_all
  have next_frame: "quiet_replica_frame initial (target_state e)"
    by (rule quiet_step_keeps_replica_frame[OF head]) (use Cons.prems from_s in auto)
  show ?case
    by (rule Cons.IH[OF tail _ next_frame]) (use Cons.prems(2) in simp)
qed

lemma actual_run_window_is_finite_trace:
  assumes run: "infinite_run step initial carrier events"
  shows "finite_trace step carrier (source_state (events k)) (map events [k..<k + len])
    (source_state (events (k + len)))"
proof (induction len arbitrary: k)
  case 0
  then show ?case using run by (simp add: infinite_run_def)
next
  case (Suc len)
  have events_list: "[k..<k + Suc len] = k # [Suc k..<Suc k + len]"
    by (subst upt_conv_Cons) simp_all
  have state: "source_state (events k) \<in> carrier"
    and actual: "step_occurs step (events k)"
    and linked: "target_state (events k) = source_state (events (Suc k))"
    using run by (auto simp: infinite_run_def)
  have same_endpoint: "Suc k + len = k + Suc len" by simp
  have tail: "finite_trace step carrier (source_state (events (Suc k)))
      (map events [Suc k..<Suc k + len]) (source_state (events (k + Suc len)))"
    using Suc.IH[of "Suc k"] by (simp only: same_endpoint)
  have linked_tail: "finite_trace step carrier (target_state (events k))
      (map events [Suc k..<Suc k + len]) (source_state (events (k + Suc len)))"
    using tail by (simp only: linked)
  show ?case unfolding events_list list.map finite_trace.simps(2)
    by (intro conjI state refl actual linked_tail)
qed

lemma quiet_drained_window_is_atomic_at_original_footprint:
  fixes events :: "nat \<Rightarrow> 'd repair_event"
  assumes run: "infinite_run (recovery_step grants governance) initial recovery_carrier events"
    and order: "k \<le> n"
    and quiet: "\<And>j. k \<le> j \<Longrightarrow> j < n \<Longrightarrow> \<not> affects_recovery (events j)"
    and drained: "pending_ids (source_state (events n)) = {}"
  shows "finite_trace (recovery_step grants governance) recovery_carrier
      (source_state (events k)) (map events [k..<n]) (source_state (events n))"
    and "replica (source_state (events n)) =
        update_cells (active_domains (source_state (events k)))
          (\<lambda>_. primary_record (source_state (events k))) (replica (source_state (events k))) \<and>
      active_domains (source_state (events n)) \<subseteq> active_domains (source_state (events k)) \<and>
      primary_record (source_state (events n)) = primary_record (source_state (events k)) \<and>
      primary_sequence (source_state (events n)) = primary_sequence (source_state (events k)) \<and>
      irreversible_facts (source_state (events n)) = irreversible_facts (source_state (events k))"
proof -
  let ?s = "source_state (events k)"
  let ?t = "source_state (events n)"
  have index_end: "k + (n - k) = n" using order by simp
  show trace: "finite_trace (recovery_step grants governance) recovery_carrier ?s (map events [k..<n]) ?t"
    using actual_run_window_is_finite_trace[OF run, of k "n-k"] by (simp only: index_end)
  have initial_valid: "?s \<in> recovery_carrier" using run by (simp add: infinite_run_def)
  have initial_frame: "quiet_replica_frame ?s ?s" by (rule initial_quiet_replica_frame[OF initial_valid])
  have quiet_events: "\<And>e. e \<in> set (map events [k..<n]) \<Longrightarrow> \<not> affects_recovery e"
    using quiet by auto
  have frame: "quiet_replica_frame ?s ?t"
    by (rule quiet_trace_keeps_replica_frame[OF trace quiet_events initial_frame])
  have replicas: "replica ?t = update_cells (active_domains ?s) (\<lambda>_. primary_record ?s) (replica ?s)"
  proof (rule ext)
    fix d
    show "replica ?t d = update_cells (active_domains ?s) (\<lambda>_. primary_record ?s) (replica ?s) d"
    proof (cases "d \<in> active_domains ?s")
      case True
      then have "replica ?t d = primary_record ?s"
        using frame drained by (auto simp: quiet_replica_frame_def pending_ids_def dom_def)
      with True show ?thesis by (simp add: update_cells_def)
    next
      case False
      then show ?thesis using frame
        by (simp add: quiet_replica_frame_def preserves_outside_def update_cells_def)
    qed
  qed
  show "replica ?t = update_cells (active_domains ?s) (\<lambda>_. primary_record ?s) (replica ?s) \<and>
      active_domains ?t \<subseteq> active_domains ?s \<and> primary_record ?t = primary_record ?s \<and>
      primary_sequence ?t = primary_sequence ?s \<and> irreversible_facts ?t = irreversible_facts ?s"
    using replicas frame by (simp add: quiet_replica_frame_def)
qed

theorem finite_interference_reaches_the_atomic_replica_update:
  fixes events :: "nat \<Rightarrow> 'd repair_event"
  assumes run: "infinite_run (recovery_step grants governance) initial recovery_carrier events"
    and finite_interference: "finite {i. affects_recovery (events i)}"
    and repair_selected:
      "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> affects_recovery (events j)) \<Longrightarrow>
        pending_ids (source_state (events i)) \<noteq> {} \<Longrightarrow>
        \<exists>j\<ge>i. \<exists>w d seq. step_outcome (events j) = Accepted (Installed w d seq)"
  obtains k n where "k \<le> n"
    and "\<And>j. k \<le> j \<Longrightarrow> \<not> affects_recovery (events j)"
    and "\<And>i. n \<le> i \<Longrightarrow>
        finite_trace (recovery_step grants governance) recovery_carrier
          (source_state (events k)) (map events [k..<i]) (source_state (events i)) \<and>
        pending_ids (source_state (events i)) = {} \<and>
        replica (source_state (events i)) =
          update_cells (active_domains (source_state (events k)))
            (\<lambda>_. primary_record (source_state (events k))) (replica (source_state (events k))) \<and>
        active_domains (source_state (events i)) \<subseteq> active_domains (source_state (events k)) \<and>
        primary_record (source_state (events i)) = primary_record (source_state (events k)) \<and>
        primary_sequence (source_state (events i)) = primary_sequence (source_state (events k)) \<and>
        irreversible_facts (source_state (events i)) = irreversible_facts (source_state (events k)) \<and>
        (\<forall>j\<le>i. pending_ids (source_state (events j)) \<union> completion_log (source_state (events j))
          \<subseteq> completion_log (source_state (events i)))"
proof -
  let ?k = "Suc (Max {j. affects_recovery (events j)})"
  have quiet: "\<And>j. ?k \<le> j \<Longrightarrow> \<not> affects_recovery (events j)"
  proof -
    fix j assume suffix: "?k \<le> j"
    show "\<not> affects_recovery (events j)"
    proof
      assume "affects_recovery (events j)"
      then have "j \<le> Max {i. affects_recovery (events i)}"
        by (intro Max_ge[OF finite_interference]) simp
      with suffix show False by simp
    qed
  qed
  from recovery_finishes_under_finite_interference[OF run finite_interference repair_selected]
  obtain n where settled: "\<forall>i\<ge>n.
    pending_ids (source_state (events i)) = {} \<and>
    (\<forall>d\<in>active_domains (source_state (events i)).
      replica (source_state (events i)) d = primary_record (source_state (events i))) \<and>
    (\<forall>j\<le>i. pending_ids (source_state (events j)) \<union> completion_log (source_state (events j))
      \<subseteq> completion_log (source_state (events i)))" ..
  show thesis
  proof (rule that[of ?k "max ?k n"])
    show "?k \<le> max ?k n" by simp
    show "\<And>j. ?k \<le> j \<Longrightarrow> \<not> affects_recovery (events j)" by (rule quiet)
  next
    fix i assume late: "max ?k n \<le> i"
    have in_window: "?k \<le> i" and past_drain: "n \<le> i" using late by simp_all
    note settled_here = settled[rule_format, OF past_drain]
    have drained: "pending_ids (source_state (events i)) = {}" by (rule conjunct1[OF settled_here])
    have ledger: "\<forall>j\<le>i.
      pending_ids (source_state (events j)) \<union> completion_log (source_state (events j))
        \<subseteq> completion_log (source_state (events i))"
      by (rule conjunct2[OF conjunct2[OF settled_here]])
    have quiet_window: "\<And>j. ?k \<le> j \<Longrightarrow> j < i \<Longrightarrow> \<not> affects_recovery (events j)"
      by (intro quiet)
    from quiet_drained_window_is_atomic_at_original_footprint[OF run in_window quiet_window drained]
      drained ledger show
      "finite_trace (recovery_step grants governance) recovery_carrier
         (source_state (events ?k)) (map events [?k..<i]) (source_state (events i)) \<and>
       pending_ids (source_state (events i)) = {} \<and>
       replica (source_state (events i)) =
         update_cells (active_domains (source_state (events ?k)))
           (\<lambda>_. primary_record (source_state (events ?k))) (replica (source_state (events ?k))) \<and>
       active_domains (source_state (events i)) \<subseteq> active_domains (source_state (events ?k)) \<and>
       primary_record (source_state (events i)) = primary_record (source_state (events ?k)) \<and>
       primary_sequence (source_state (events i)) = primary_sequence (source_state (events ?k)) \<and>
       irreversible_facts (source_state (events i)) = irreversible_facts (source_state (events ?k)) \<and>
       (\<forall>j\<le>i. pending_ids (source_state (events j)) \<union> completion_log (source_state (events j))
         \<subseteq> completion_log (source_state (events i)))"
      by blast
  qed
qed

end
