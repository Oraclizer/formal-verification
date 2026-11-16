theory Atomic_Comparison
  imports DOSP_Views.Recovery_Observations DOSP_Recovery.Recovery_Examples
begin

definition fixed_recovery_frame :: "'d recovery_state \<Rightarrow> 'd recovery_state \<Rightarrow> bool" where
  "fixed_recovery_frame s t \<longleftrightarrow>
    active_domains t = active_domains s \<and> primary_record t = primary_record s \<and>
    primary_sequence t = primary_sequence s \<and> irreversible_facts t = irreversible_facts s \<and>
    preserves_outside replica (active_domains s) s t"

lemma fixed_recovery_frame_refl:
  "fixed_recovery_frame s s"
  by (simp add: fixed_recovery_frame_def preserves_outside_def)

lemma fixed_recovery_frame_trans:
  "\<lbrakk>fixed_recovery_frame s t; fixed_recovery_frame t u\<rbrakk> \<Longrightarrow> fixed_recovery_frame s u"
  by (auto simp: fixed_recovery_frame_def preserves_outside_def)

lemma install_respects_fixed_recovery_frame:
  assumes "recovery_step grants governance s a (Accepted (Installed job d sequence)) t"
  shows "fixed_recovery_frame s t"
  using assms
  by (cases rule: recovery_step.cases) (auto simp: fixed_recovery_frame_def install_replica_def preserves_outside_def)

lemma installation_trace_respects_fixed_recovery_frame:
  assumes run: "finite_trace (recovery_step grants governance) recovery_carrier s es t"
    and installs: "\<And>e. e \<in> set es \<Longrightarrow> \<exists>job d sequence. step_outcome e = Accepted (Installed job d sequence)"
  shows "fixed_recovery_frame s t \<and> t \<in> recovery_carrier"
  using run installs
proof (induction es arbitrary: s)
  case Nil
  then show ?case by (auto simp: fixed_recovery_frame_refl)
next
  case (Cons e es)
  have remainder: "finite_trace (recovery_step grants governance) recovery_carrier (target_state e) es t"
    using Cons.prems(1) by simp
  have tail: "\<And>x. x \<in> set es \<Longrightarrow> \<exists>job d sequence. step_outcome x = Accepted (Installed job d sequence)"
    using Cons.prems(2) by simp
  have stable_tail: "fixed_recovery_frame (target_state e) t \<and> t \<in> recovery_carrier"
    by (rule Cons.IH[OF remainder tail])
  obtain job d sequence where installed: "step_outcome e = Accepted (Installed job d sequence)"
    using Cons.prems(2)[of e] by auto
  have from_s: "source_state e = s" and occurrence: "step_occurs (recovery_step grants governance) e"
    using Cons.prems(1) by simp_all
  have "recovery_step grants governance s (step_action e) (Accepted (Installed job d sequence)) (target_state e)"
    using occurrence by (simp only: step_occurs_def from_s installed)
  then have "fixed_recovery_frame s (target_state e)" by (rule install_respects_fixed_recovery_frame)
  with stable_tail show ?case by (meson fixed_recovery_frame_trans)
qed

theorem drained_sequential_repair_equals_atomic_replica_update:
  assumes run: "finite_trace (recovery_step grants governance) recovery_carrier s es t"
    and installs: "\<And>e. e \<in> set es \<Longrightarrow> \<exists>job d sequence. step_outcome e = Accepted (Installed job d sequence)"
    and drained: "pending_ids t = {}"
  shows "replica t = update_cells (active_domains s) (\<lambda>_. primary_record s) (replica s) \<and>
    active_domains t = active_domains s \<and>
    primary_sequence t = primary_sequence s \<and> irreversible_facts t = irreversible_facts s"
proof -
  have framed: "fixed_recovery_frame s t" and closed: "t \<in> recovery_carrier"
    using installation_trace_respects_fixed_recovery_frame[OF run installs] by auto
  have same_members: "active_domains t = active_domains s"
    and same_record: "primary_record t = primary_record s"
    using framed by (simp_all add: fixed_recovery_frame_def)
  have cells: "replica t = update_cells (active_domains s) (\<lambda>_. primary_record s) (replica s)"
  proof (rule ext)
    fix d
    show "replica t d = update_cells (active_domains s) (\<lambda>_. primary_record s) (replica s) d"
    proof (cases "d \<in> active_domains s")
      case True
      then have "d \<in> active_domains t" by (simp add: same_members)
      then have "replica t d = primary_record t" by (rule empty_pending_coherent[OF closed drained])
      then show ?thesis using True same_record by (simp add: update_cells_def)
    next
      case False
      then show ?thesis
        using framed by (simp add: fixed_recovery_frame_def preserves_outside_def update_cells_def)
    qed
  qed
  show ?thesis using cells framed by (simp add: fixed_recovery_frame_def)
qed

definition installed_record :: "'d repair_event \<Rightarrow> bool" where
  "installed_record e \<longleftrightarrow> (\<exists>job d sequence. step_outcome e = Accepted (Installed job d sequence))"

lemma removing_state_stutters_preserves_trace_endpoints:
  assumes run: "finite_trace step carrier s es t"
    and ignored: "\<And>e. e \<in> set es \<Longrightarrow> \<not> keep e \<Longrightarrow> source_state e = target_state e"
  shows "finite_trace step carrier s (filter keep es) t"
  using run ignored
proof (induction es arbitrary: s)
  case Nil
  then show ?case by auto
next
  case (Cons e es)
  have tail: "finite_trace step carrier (target_state e) es t" using Cons.prems(1) by simp
  have tail_ignored: "\<And>x. x \<in> set es \<Longrightarrow> \<not> keep x \<Longrightarrow> source_state x = target_state x"
    using Cons.prems(2) by simp
  have filtered: "finite_trace step carrier (target_state e) (filter keep es) t"
    by (rule Cons.IH[OF tail tail_ignored])
  show ?case
  proof (cases "keep e")
    case True
    then show ?thesis using Cons.prems(1) filtered by simp
  next
    case False
    have "s = target_state e" using False Cons.prems(1) Cons.prems(2)[of e] by auto
    then show ?thesis using False filtered by simp
  qed
qed

corollary drained_repair_with_idle_steps_has_the_atomic_replica_endpoint:
  assumes run: "finite_trace (recovery_step grants governance) recovery_carrier s es t"
    and silent_state: "\<And>e. e \<in> set es \<Longrightarrow> \<not> installed_record e \<Longrightarrow> source_state e = target_state e"
    and drained: "pending_ids t = {}"
  shows "replica t = update_cells (active_domains s) (\<lambda>_. primary_record s) (replica s)"
proof -
  have trace: "finite_trace (recovery_step grants governance) recovery_carrier s (filter installed_record es) t"
    by (rule removing_state_stutters_preserves_trace_endpoints[OF run silent_state])
  have installed: "\<And>e. e \<in> set (filter installed_record es) \<Longrightarrow>
      \<exists>job d sequence. step_outcome e = Accepted (Installed job d sequence)"
    by (auto simp: installed_record_def)
  show ?thesis using drained_sequential_repair_equals_atomic_replica_update[OF trace installed drained]
    by blast
qed

definition two_repairs_start :: "nat recovery_state" where
  "two_repairs_start = repair_start\<lparr>replica := (replica repair_start)(2 := 9),
     work_owner := (work_owner repair_start)(8 \<mapsto> 2)\<rparr>"

definition first_install :: "nat recovery_state" where
  "first_install = install_replica two_repairs_start 7 1"

definition second_install :: "nat recovery_state" where
  "second_install = install_replica first_install 8 2"

lemma two_actual_repairs_and_an_idle_step_validate_the_atomic_endpoint:
  "replica second_install =
     update_cells (active_domains two_repairs_start) (\<lambda>_. primary_record two_repairs_start) (replica two_repairs_start) \<and>
   replica two_repairs_start 1 \<noteq> replica first_install 1 \<and>
   replica first_install 2 \<noteq> replica second_install 2 \<and>
   recovery_step {} {} second_install (Ordinary_Trade 23) (Accepted (Traded 23)) second_install"
proof -
  have first: "recovery_step {} {} two_repairs_start (Apply_Repair 7 20) (Accepted (Installed 7 1 20)) first_install"
    unfolding first_install_def
    by (rule recovery_step.Ordinary_Repair) (simp_all add: two_repairs_start_def repair_start_def)
  have second: "recovery_step {} {} first_install (Apply_Repair 8 20) (Accepted (Installed 8 2 20)) second_install"
    unfolding second_install_def
    by (rule recovery_step.Ordinary_Repair)
       (simp_all add: first_install_def install_replica_def two_repairs_start_def repair_start_def)
  have ownership: "work_owner two_repairs_start 7 = Some 1" "work_owner two_repairs_start 8 = Some 2"
    by (simp_all add: two_repairs_start_def repair_start_def)
  have covered: "replica_covered two_repairs_start"
    unfolding replica_covered_def
  proof (intro ballI impI)
    fix d
    assume "d \<in> active_domains two_repairs_start"
    then have "d = 1 \<or> d = 2" by (simp add: two_repairs_start_def repair_start_def)
    then show "\<exists>i. work_owner two_repairs_start i = Some d" using ownership by blast
  qed
  have first_carrier: "two_repairs_start \<in> recovery_carrier"
    using covered by (auto simp: recovery_carrier_def pending_ids_def two_repairs_start_def repair_start_def)
  have mid_carrier: "first_install \<in> recovery_carrier"
    by (rule recovery_carrier_closed[OF first first_carrier])
  have final_carrier: "second_install \<in> recovery_carrier"
    by (rule recovery_carrier_closed[OF second mid_carrier])
  let ?first = "mk_event two_repairs_start (Apply_Repair 7 20) (Accepted (Installed 7 1 20)) first_install"
  let ?idle = "mk_event first_install Wait_For_Source (Internal ()) first_install"
  let ?second = "mk_event first_install (Apply_Repair 8 20) (Accepted (Installed 8 2 20)) second_install"
  have idle: "recovery_step {} {} first_install Wait_For_Source (Internal ()) first_install" by (rule recovery_step.Idle)
  have trace: "finite_trace (recovery_step {} {}) recovery_carrier two_repairs_start [?first, ?idle, ?second] second_install"
    using first idle second first_carrier mid_carrier final_carrier
    by (simp add: step_occurs_def mk_event_def)
  have stutters: "\<And>e. e \<in> set [?first, ?idle, ?second] \<Longrightarrow> \<not> installed_record e \<Longrightarrow> source_state e = target_state e"
    by (auto simp: mk_event_def installed_record_def)
  have drained: "pending_ids second_install = {}"
    by (auto simp: pending_ids_def second_install_def first_install_def install_replica_def two_repairs_start_def repair_start_def)
  have opened: "recovery_step {} {} second_install (Ordinary_Trade 23) (Accepted (Traded 23)) second_install"
    using drained by (intro recovery_step.Admit_Trade)
      (simp_all add: second_install_def first_install_def install_replica_def two_repairs_start_def repair_start_def)
  have changes: "replica two_repairs_start 1 \<noteq> replica first_install 1"
    "replica first_install 2 \<noteq> replica second_install 2"
    by (simp_all add: second_install_def first_install_def install_replica_def two_repairs_start_def repair_start_def)
  show ?thesis
    using drained_repair_with_idle_steps_has_the_atomic_replica_endpoint[OF trace stutters drained] opened changes
    by blast
qed

end
