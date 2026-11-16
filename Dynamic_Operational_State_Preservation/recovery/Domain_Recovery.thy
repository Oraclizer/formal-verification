theory Domain_Recovery
  imports DOSP_Progress.Recovery_Progress
begin

record 'd recovery_state =
  active_domains :: "'d set"
  route_epoch :: nat
  primary_record :: nat
  primary_sequence :: nat
  source_ready :: bool
  replica :: "'d \<Rightarrow> nat"
  work_owner :: "nat \<Rightarrow> 'd option"
  completion_log :: "nat set"
  irreversible_facts :: "nat set"
  rollback_incomplete :: bool

datatype 'd route_change = Join_Domain 'd nat | Leave_Domain 'd 'd
type_synonym 'd routing_grants = "('d route_change \<times> nat \<times> nat) set"

datatype 'd repair_action =
    Activate "'d route_change" nat nat nat
  | Notice_Divergence nat 'd nat
  | Apply_Repair nat nat
  | Governance_Resync nat nat nat
  | Ordinary_Trade nat
  | Wait_For_Source

datatype 'd repair_success =
    Joined 'd nat
  | Left 'd 'd
  | Opened nat
  | Installed nat 'd nat
  | Traded nat

datatype recovery_rejection = Recovery_Blocks_Trade | Stale_Route
datatype recovery_failure = Evidence_Unavailable

type_synonym 'd repair_result =
  "('d repair_success, recovery_rejection, recovery_failure, unit) transition_result"
type_synonym 'd repair_event = "('d recovery_state, 'd repair_action, 'd repair_result) transition"

definition pending_ids :: "'d recovery_state \<Rightarrow> nat set" where
  "pending_ids s = dom (work_owner s)"

definition fresh_work :: "'d recovery_state \<Rightarrow> nat \<Rightarrow> bool" where
  "fresh_work s i \<longleftrightarrow> work_owner s i = None \<and> i \<notin> completion_log s"

definition carry_owner ::
  "'d \<Rightarrow> 'd \<Rightarrow> (nat \<Rightarrow> 'd option) \<Rightarrow> nat \<Rightarrow> 'd option"
where
  "carry_owner from into owners i =
    (if owners i = Some from then Some into else owners i)"

lemma carry_owner_domain [simp]:
  "dom (carry_owner from into owners) = dom owners"
  by (auto simp: dom_def carry_owner_def)

lemma carry_owner_value:
  "carry_owner from into owners job = (if owners job = Some from then Some into else owners job)"
  by (simp add: carry_owner_def)

definition install_replica ::
  "'d recovery_state \<Rightarrow> nat \<Rightarrow> 'd \<Rightarrow> 'd recovery_state"
where
  "install_replica s i d =
     s\<lparr>replica := (replica s)(d := primary_record s),
       work_owner := (work_owner s)(i := None),
       completion_log := insert i (completion_log s)\<rparr>"

definition current_grant ::
  "'d routing_grants \<Rightarrow> 'd recovery_state \<Rightarrow> 'd route_change \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "current_grant grants s change epoch boundary root_time \<longleftrightarrow>
      (change, epoch, boundary) \<in> grants \<and> route_epoch s < epoch \<and> boundary \<le> root_time"

inductive recovery_step ::
  "'d routing_grants \<Rightarrow> nat set \<Rightarrow> ('d recovery_state, 'd repair_action, 'd repair_result) step_rel"
  for grants governance
where
  Join_Route:
    "\<lbrakk>current_grant grants s (Join_Domain d i) epoch boundary root_time;
      d \<notin> active_domains s; fresh_work s i\<rbrakk> \<Longrightarrow>
     recovery_step grants governance s (Activate (Join_Domain d i) epoch boundary root_time) (Accepted (Joined d i))
       (s\<lparr>active_domains := insert d (active_domains s), route_epoch := epoch,
           work_owner := (work_owner s)(i \<mapsto> d)\<rparr>)"
| Leave_Route:
    "\<lbrakk>current_grant grants s (Leave_Domain old successor) epoch boundary root_time;
      old \<in> active_domains s; successor \<in> active_domains s; old \<noteq> successor\<rbrakk> \<Longrightarrow>
     recovery_step grants governance s (Activate (Leave_Domain old successor) epoch boundary root_time)
       (Accepted (Left old successor))
       (s\<lparr>active_domains := active_domains s - {old}, route_epoch := epoch,
           work_owner := carry_owner old successor (work_owner s)\<rparr>)"
| Reject_Route:
    "\<not> current_grant grants s change epoch boundary root_time \<Longrightarrow>
     recovery_step grants governance s (Activate change epoch boundary root_time) (Rejected Stale_Route) s"
| Detect_Divergence:
    "\<lbrakk>d \<in> active_domains s; fresh_work s i; observed \<noteq> primary_record s\<rbrakk> \<Longrightarrow>
     recovery_step grants governance s (Notice_Divergence i d observed) (Accepted (Opened i))
       (s\<lparr>replica := (replica s)(d := observed), work_owner := (work_owner s)(i \<mapsto> d)\<rparr>)"
| Ordinary_Repair:
    "\<lbrakk>work_owner s i = Some d; d \<in> active_domains s; source_ready s;
      sequence = primary_sequence s; \<not> rollback_incomplete s\<rbrakk> \<Longrightarrow>
     recovery_step grants governance s (Apply_Repair i sequence)
       (Accepted (Installed i d sequence)) (install_replica s i d)"
| Authorized_Resync:
    "\<lbrakk>work_owner s i = Some d; d \<in> active_domains s; source_ready s;
      sequence = primary_sequence s; rollback_incomplete s; approval \<in> governance\<rbrakk> \<Longrightarrow>
     recovery_step grants governance s (Governance_Resync approval i sequence)
       (Accepted (Installed i d sequence))
       ((install_replica s i d)\<lparr>rollback_incomplete := pending_ids (install_replica s i d) \<noteq> {}\<rparr>)"
| Refuse_Trade:
    "pending_ids s \<noteq> {} \<or> rollback_incomplete s \<Longrightarrow>
     recovery_step grants governance s (Ordinary_Trade tx) (Rejected Recovery_Blocks_Trade) s"
| Admit_Trade:
    "\<lbrakk>pending_ids s = {}; \<not> rollback_incomplete s\<rbrakk> \<Longrightarrow>
     recovery_step grants governance s (Ordinary_Trade tx) (Accepted (Traded tx)) s"
| Source_Wait:
    "\<not> source_ready s \<Longrightarrow>
     recovery_step grants governance s Wait_For_Source (Operational_Failure Evidence_Unavailable) s"
| Idle:
    "recovery_step grants governance s Wait_For_Source (Internal ()) s"

fun admitted_result :: "'d repair_result \<Rightarrow> nat set" where
  "admitted_result (Accepted (Joined d i)) = {i}"
| "admitted_result (Accepted (Opened i)) = {i}"
| "admitted_result _ = {}"

fun finished_result :: "'d repair_result \<Rightarrow> nat set" where
  "finished_result (Accepted (Installed i d sequence)) = {i}"
| "finished_result _ = {}"

definition affects_recovery :: "'d repair_event \<Rightarrow> bool" where
  "affects_recovery e \<longleftrightarrow>
    admitted_result (step_outcome e) \<noteq> {} \<or>
    (\<exists>old receiver. step_outcome e = Accepted (Left old receiver) \<and>
      (\<exists>i. work_owner (source_state e) i = Some old))"

definition replica_covered :: "'d recovery_state \<Rightarrow> bool" where
  "replica_covered s \<longleftrightarrow>
   (\<forall>d\<in>active_domains s. replica s d \<noteq> primary_record s \<longrightarrow> (\<exists>i. work_owner s i = Some d))"

definition recovery_carrier :: "'d recovery_state set" where
  "recovery_carrier = {s.
    finite (pending_ids s) \<and> pending_ids s \<inter> completion_log s = {} \<and>
    (\<forall>i d. work_owner s i = Some d \<longrightarrow> d \<in> active_domains s) \<and>
    replica_covered s}"

lemma recovery_work_accounting:
  assumes "step_occurs (recovery_step grants governance) e" "source_state e \<in> recovery_carrier"
  shows "accounts_for pending_ids completion_log
    (\<lambda>x. admitted_result (step_outcome x)) (\<lambda>x. finished_result (step_outcome x)) e"
  using assms unfolding step_occurs_def
  by (cases rule: recovery_step.cases)
     (auto simp: accounts_for_def recovery_carrier_def fresh_work_def pending_ids_def install_replica_def dom_def
       carry_owner_def split: if_splits)

lemma joined_replica_covered:
  assumes covered: "replica_covered s" and fresh: "fresh_work s i"
  shows "replica_covered
    (s\<lparr>active_domains := insert d (active_domains s), route_epoch := epoch,
       work_owner := (work_owner s)(i \<mapsto> d)\<rparr>)"
proof -
  let ?t = "s\<lparr>active_domains := insert d (active_domains s), route_epoch := epoch,
                   work_owner := (work_owner s)(i \<mapsto> d)\<rparr>"
  show ?thesis unfolding replica_covered_def
  proof (intro ballI impI)
    fix x
    assume "x \<in> active_domains ?t" "replica ?t x \<noteq> primary_record ?t"
    then have member: "x \<in> insert d (active_domains s)" and mismatch: "replica s x \<noteq> primary_record s" by simp_all
    show "\<exists>j. work_owner ?t j = Some x"
    proof (cases "x = d")
      case True
      then show ?thesis by (intro exI[of _ i]) simp
    next
      case False
      then obtain j where owner: "work_owner s j = Some x"
        using covered member mismatch by (auto simp: replica_covered_def)
      have "j \<noteq> i" using fresh owner by (auto simp: fresh_work_def)
      with owner show ?thesis by (intro exI[of _ j]) simp
    qed
  qed
qed

lemma carried_replica_covered:
  assumes covered: "replica_covered s"
  shows "replica_covered
    (s\<lparr>active_domains := active_domains s - {old}, route_epoch := epoch,
       work_owner := carry_owner old successor (work_owner s)\<rparr>)"
  unfolding replica_covered_def
proof (simp del: ball_simps, intro ballI impI)
  fix x
  assume member: "x \<in> active_domains s - {old}" and mismatch: "replica s x \<noteq> primary_record s"
  obtain j where owner: "work_owner s j = Some x"
    using covered member mismatch by (auto simp: replica_covered_def)
  show "\<exists>j. carry_owner old successor (work_owner s) j = Some x"
    using member owner by (intro exI[of _ j]) (simp add: carry_owner_def)
qed

lemma noticed_replica_covered:
  assumes covered: "replica_covered s" and fresh: "fresh_work s i"
  shows "replica_covered
    (s\<lparr>replica := (replica s)(d := observed), work_owner := (work_owner s)(i \<mapsto> d)\<rparr>)"
proof -
  let ?t = "s\<lparr>replica := (replica s)(d := observed), work_owner := (work_owner s)(i \<mapsto> d)\<rparr>"
  show ?thesis unfolding replica_covered_def
  proof (intro ballI impI)
    fix x
    assume "x \<in> active_domains ?t" "replica ?t x \<noteq> primary_record ?t"
    then have member: "x \<in> active_domains s"
      and mismatch: "((replica s)(d := observed)) x \<noteq> primary_record s" by simp_all
    show "\<exists>j. work_owner ?t j = Some x"
    proof (cases "x = d")
      case True
      then show ?thesis by (intro exI[of _ i]) simp
    next
      case False
      then obtain j where owner: "work_owner s j = Some x"
        using covered member mismatch by (auto simp: replica_covered_def)
      have "j \<noteq> i" using fresh owner by (auto simp: fresh_work_def)
      with owner show ?thesis by (intro exI[of _ j]) simp
    qed
  qed
qed

lemma installed_replica_covered:
  assumes covered: "replica_covered s" and installed: "work_owner s i = Some d"
  shows "replica_covered (install_replica s i d)"
proof (unfold replica_covered_def, intro ballI impI)
  fix x
  assume "x \<in> active_domains (install_replica s i d)"
    "replica (install_replica s i d) x \<noteq> primary_record (install_replica s i d)"
  then have member: "x \<in> active_domains s"
    and mismatch: "((replica s)(d := primary_record s)) x \<noteq> primary_record s"
    by (simp_all add: install_replica_def)
  have other: "x \<noteq> d" using mismatch by auto
  obtain j where owner: "work_owner s j = Some x"
    using covered member mismatch other by (auto simp: replica_covered_def)
  have "j \<noteq> i" using owner installed other by auto
  then show "\<exists>j. work_owner (install_replica s i d) j = Some x"
    using owner by (intro exI[of _ j]) (simp add: install_replica_def)
qed

lemma coverage_rollback [simp]:
  "replica_covered (s\<lparr>rollback_incomplete := retry\<rparr>) = replica_covered s"
  by (simp add: replica_covered_def)

lemma recovery_carrier_closed:
  assumes step: "recovery_step grants governance s a r t" and valid: "s \<in> recovery_carrier"
  shows "t \<in> recovery_carrier"
proof -
  have covered_s: "replica_covered s" using valid by (simp add: recovery_carrier_def)
  have covered: "replica_covered t" using step covered_s
    by (cases rule: recovery_step.cases)
       (simp_all add: joined_replica_covered carried_replica_covered noticed_replica_covered installed_replica_covered)
  show ?thesis using step valid covered
    by (cases rule: recovery_step.cases)
       (auto simp: recovery_carrier_def fresh_work_def pending_ids_def install_replica_def carry_owner_value
         split: if_splits)
qed

lemma recovery_never_changes_irreversible_facts:
  assumes "recovery_step grants governance s a r t"
  shows "irreversible_facts t = irreversible_facts s"
  using assms by (cases rule: recovery_step.cases) (simp_all add: install_replica_def)

lemma leave_transports_work:
  assumes "recovery_step grants governance s a (Accepted (Left old successor)) t"
  shows "pending_ids t = pending_ids s \<and> completion_log t = completion_log s \<and>
    (\<forall>i. work_owner s i = Some old \<longrightarrow> work_owner t i = Some successor) \<and>
    (\<forall>i. work_owner s i \<noteq> Some old \<longrightarrow> work_owner t i = work_owner s i)"
  using assms
  by (cases rule: recovery_step.cases) (auto simp: pending_ids_def carry_owner_def)

lemma actual_install_uses_primary_record:
  assumes "recovery_step grants governance s a (Accepted (Installed i d sequence)) t"
  shows "work_owner s i = Some d \<and> d \<in> active_domains s \<and> source_ready s \<and>
    sequence = primary_sequence s \<and> replica t d = primary_record s \<and>
    i \<in> completion_log t \<and> preserves_outside replica {d} s t"
  using assms
  by (cases rule: recovery_step.cases) (auto simp: install_replica_def preserves_outside_def)

lemma ordinary_trade_is_blocked:
  assumes "recovery_step grants governance s (Ordinary_Trade tx) r t"
    "pending_ids s \<noteq> {} \<or> rollback_incomplete s"
  shows "r = Rejected Recovery_Blocks_Trade \<and> t = s"
  using assms by (cases rule: recovery_step.cases) auto

lemma empty_pending_coherent:
  assumes "s \<in> recovery_carrier" "pending_ids s = {}" "d \<in> active_domains s"
  shows "replica s d = primary_record s"
  using assms by (auto simp: recovery_carrier_def replica_covered_def pending_ids_def dom_def)

theorem recovery_finishes_under_finite_interference:
  fixes events :: "nat \<Rightarrow> 'd repair_event"
  assumes run: "infinite_run (recovery_step grants governance) initial recovery_carrier events"
    and finite_interference: "finite {i. affects_recovery (events i)}"
    and repair_selected:
      "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> affects_recovery (events j)) \<Longrightarrow>
       pending_ids (source_state (events i)) \<noteq> {} \<Longrightarrow>
       \<exists>j\<ge>i. \<exists>w d seq. step_outcome (events j) = Accepted (Installed w d seq)"
  shows "\<exists>n. \<forall>i\<ge>n.
    pending_ids (source_state (events i)) = {} \<and>
    (\<forall>d\<in>active_domains (source_state (events i)).
      replica (source_state (events i)) d = primary_record (source_state (events i))) \<and>
    (\<forall>j\<le>i. pending_ids (source_state (events j)) \<union> completion_log (source_state (events j))
      \<subseteq> completion_log (source_state (events i)))"
proof -
  have charged: "\<And>i. admitted_result (step_outcome (events i)) \<noteq> {} \<Longrightarrow> affects_recovery (events i)"
    by (simp add: affects_recovery_def)
  have ledger: "\<And>i. accounts_for pending_ids completion_log
    (\<lambda>x. admitted_result (step_outcome x)) (\<lambda>x. finished_result (step_outcome x)) (events i)"
    using run by (auto simp: infinite_run_def intro: recovery_work_accounting)
  have scheduled: "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> affects_recovery (events j)) \<Longrightarrow>
    pending_ids (source_state (events i)) \<noteq> {} \<Longrightarrow>
    \<exists>j\<ge>i. finished_result (step_outcome (events j)) \<noteq> {}"
    using repair_selected by (metis finished_result.simps(1) insert_not_empty)
  let ?births = "\<lambda>e. admitted_result (step_outcome e)"
  let ?repairs = "\<lambda>e. finished_result (step_outcome e)"
  have supplied: "\<exists>n. \<forall>i\<ge>n.
    pending_ids (source_state (events i)) = {} \<and>
    (\<forall>j\<le>i. pending_ids (source_state (events j)) \<union> completion_log (source_state (events j))
      \<subseteq> completion_log (source_state (events i)))"
  proof (rule eventual_completion_under_finite_interference[where
    step="recovery_step grants governance" and initial=initial and carrier=recovery_carrier
    and admitted="?births" and finished="?repairs" and interfering=affects_recovery])
    show "infinite_run (recovery_step grants governance) initial recovery_carrier events" by (rule run)
    show "\<And>i. accounts_for pending_ids completion_log ?births ?repairs (events i)" by (rule ledger)
    show "\<And>i. ?births (events i) \<noteq> {} \<Longrightarrow> affects_recovery (events i)" by (rule charged)
    show "finite {i. affects_recovery (events i)}" by (rule finite_interference)
    show "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> affects_recovery (events j)) \<Longrightarrow>
      pending_ids (source_state (events i)) \<noteq> {} \<Longrightarrow> \<exists>j\<ge>i. ?repairs (events j) \<noteq> {}"
      by (rule scheduled)
  qed
  then obtain n where drained: "\<forall>i\<ge>n.
    pending_ids (source_state (events i)) = {} \<and>
    (\<forall>j\<le>i. pending_ids (source_state (events j)) \<union> completion_log (source_state (events j))
      \<subseteq> completion_log (source_state (events i)))"
    by blast
  have settled: "\<And>i. n \<le> i \<Longrightarrow>
    pending_ids (source_state (events i)) = {} \<and>
    (\<forall>j\<le>i. pending_ids (source_state (events j)) \<union> completion_log (source_state (events j))
      \<subseteq> completion_log (source_state (events i)))"
    using drained by blast
  have coherent: "\<And>i d. n \<le> i \<Longrightarrow> d \<in> active_domains (source_state (events i)) \<Longrightarrow>
    replica (source_state (events i)) d = primary_record (source_state (events i))"
  proof -
    fix i d assume "n \<le> i" "d \<in> active_domains (source_state (events i))"
    moreover have "source_state (events i) \<in> recovery_carrier"
      using run by (simp add: infinite_run_def)
    ultimately show "replica (source_state (events i)) d = primary_record (source_state (events i))"
      by (meson empty_pending_coherent settled)
  qed
  show ?thesis using settled coherent by (intro exI[of _ n]) blast
qed

end
