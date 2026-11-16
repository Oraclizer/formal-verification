theory Recovery_Examples
  imports Domain_Recovery Catalog_Recovery
begin

definition mk_event :: "'s \<Rightarrow> 'a \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> ('s, 'a, 'r) transition" where
  "mk_event s a r t = \<lparr>source_state = s, step_action = a, step_outcome = r, target_state = t\<rparr>"

definition repair_start :: "nat recovery_state" where
  "repair_start =
    \<lparr>active_domains = {1,2}, route_epoch = 1, primary_record = 41, primary_sequence = 20,
      source_ready = True, replica = (\<lambda>d. if d = 1 then 0 else 41),
      work_owner = Map.empty(7 \<mapsto> 1), completion_log = {}, irreversible_facts = {13},
      rollback_incomplete = False\<rparr>"

definition repair_end :: "nat recovery_state" where
  "repair_end = install_replica repair_start 7 1"

definition repair_run :: "nat \<Rightarrow> nat repair_event" where
  "repair_run n =
    (if n = 0 then mk_event repair_start (Apply_Repair 7 20) (Accepted (Installed 7 1 20)) repair_end
     else mk_event repair_end Wait_For_Source (Internal ()) repair_end)"

lemma repair_start_well_formed:
  "repair_start \<in> recovery_carrier"
  by (auto simp: repair_start_def recovery_carrier_def replica_covered_def pending_ids_def dom_def)

lemma repair_end_well_formed:
  "repair_end \<in> recovery_carrier"
  by (auto simp: repair_end_def repair_start_def recovery_carrier_def replica_covered_def
    pending_ids_def install_replica_def dom_def)

lemma example_real_install:
  "recovery_step {} {} repair_start (Apply_Repair 7 20) (Accepted (Installed 7 1 20)) repair_end"
  by (unfold repair_end_def, rule recovery_step.Ordinary_Repair) (simp_all add: repair_start_def)

lemma repair_run_occurs:
  "infinite_run (recovery_step {} {}) {repair_start} recovery_carrier repair_run"
  using repair_start_well_formed repair_end_well_formed example_real_install
  by (auto simp: infinite_run_def step_occurs_def repair_run_def mk_event_def split: if_splits intro: recovery_step.Idle)

lemma repair_run_takes_exact_repair:
  "finite {n. affects_recovery (repair_run n)}"
  "\<And>i. pending_ids (source_state (repair_run i)) \<noteq> {} \<Longrightarrow>
    \<exists>j\<ge>i. \<exists>job d seq. step_outcome (repair_run j) = Accepted (Installed job d seq)"
proof -
  have "{n. affects_recovery (repair_run n)} = {}"
    by (auto simp: affects_recovery_def repair_run_def mk_event_def split: if_splits)
  then show "finite {n. affects_recovery (repair_run n)}" by simp
  fix i
  assume "pending_ids (source_state (repair_run i)) \<noteq> {}"
  then have "i = 0"
    by (auto simp: repair_run_def mk_event_def repair_end_def install_replica_def
      repair_start_def pending_ids_def dom_def split: if_splits)
  then show "\<exists>j\<ge>i. \<exists>job d seq. step_outcome (repair_run j) = Accepted (Installed job d seq)"
    by (intro exI[of _ 0]) (auto simp: repair_run_def mk_event_def)
qed

theorem executed_repair_activates_group_completion:
  "\<exists>n. \<forall>i\<ge>n. 7 \<in> completion_log (source_state (repair_run i))"
proof -
  have started: "7 \<in> pending_ids (source_state (repair_run 0))"
    by (simp add: pending_ids_def repair_run_def repair_start_def mk_event_def dom_def)
  note completion = recovery_finishes_under_finite_interference[OF repair_run_occurs repair_run_takes_exact_repair(1)]
  from completion repair_run_takes_exact_repair(2) started show ?thesis by blast
qed

definition departure_grants :: "nat routing_grants" where
  "departure_grants = {(Leave_Domain 1 2, 3, 8)}"

definition moved_work :: "nat recovery_state" where
  "moved_work = repair_start\<lparr>active_domains := {2}, route_epoch := 3, work_owner := Map.empty(7 \<mapsto> 2)\<rparr>"

lemma actual_handoff_moves_the_same_job:
  "recovery_step departure_grants {} repair_start (Activate (Leave_Domain 1 2) 3 8 8) (Accepted (Left 1 2)) moved_work"
proof -
  have after: "carry_owner 1 2 (work_owner repair_start) = Map.empty(7 \<mapsto> 2)"
    by (rule ext) (simp add: repair_start_def carry_owner_def fun_upd_apply)
  have members: "active_domains repair_start - {1} = {2}"
    by (auto simp: repair_start_def)
  have "recovery_step departure_grants {} repair_start (Activate (Leave_Domain 1 2) 3 8 8)
    (Accepted (Left 1 2)) (repair_start\<lparr>active_domains := active_domains repair_start - {1},
      route_epoch := 3, work_owner := carry_owner 1 2 (work_owner repair_start)\<rparr>)"
    by (rule recovery_step.Leave_Route) (simp_all add: current_grant_def departure_grants_def repair_start_def)
  then show ?thesis unfolding moved_work_def by (simp only: after members)
qed

lemma early_handoff_is_rejected:
  "recovery_step departure_grants {} repair_start (Activate (Leave_Domain 1 2) 3 8 7) (Rejected Stale_Route) repair_start"
  by (rule recovery_step.Reject_Route) (simp add: current_grant_def)

definition moved_end :: "nat recovery_state" where
  "moved_end = install_replica moved_work 7 2"

definition after_interference_run :: "nat \<Rightarrow> nat repair_event" where
  "after_interference_run n =
    (if n = 0 then mk_event repair_start (Activate (Leave_Domain 1 2) 3 8 8) (Accepted (Left 1 2)) moved_work
     else if n = 1 then mk_event moved_work (Apply_Repair 7 20) (Accepted (Installed 7 2 20)) moved_end
     else mk_event moved_end Wait_For_Source (Internal ()) moved_end)"

lemma after_interference_steps:
  "infinite_run (recovery_step departure_grants {}) {repair_start} recovery_carrier after_interference_run"
proof -
  have install: "recovery_step departure_grants {} moved_work (Apply_Repair 7 20) (Accepted (Installed 7 2 20)) moved_end"
    by (unfold moved_end_def, rule recovery_step.Ordinary_Repair) (simp_all add: moved_work_def repair_start_def)
  have moved: "moved_work \<in> recovery_carrier"
    by (rule recovery_carrier_closed[OF actual_handoff_moves_the_same_job repair_start_well_formed])
  have completed: "moved_end \<in> recovery_carrier"
    by (rule recovery_carrier_closed[OF install moved])
  show ?thesis using install moved completed repair_start_well_formed actual_handoff_moves_the_same_job
    by (auto simp: infinite_run_def step_occurs_def after_interference_run_def mk_event_def
       split: if_splits intro: recovery_step.Idle)
qed

lemma after_interference_positions:
  "{n. affects_recovery (after_interference_run n)} = {0}"
  by (auto simp: after_interference_run_def mk_event_def affects_recovery_def repair_start_def split: if_splits)

theorem the_transferred_job_finishes_after_actual_interference:
  "\<exists>n. \<forall>i\<ge>n. 7 \<in> completion_log (source_state (after_interference_run i))"
proof -
  have bound: "finite {n. affects_recovery (after_interference_run n)}" by (simp add: after_interference_positions)
  have takes_repair:
    "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> affects_recovery (after_interference_run j)) \<Longrightarrow>
     pending_ids (source_state (after_interference_run i)) \<noteq> {} \<Longrightarrow>
     \<exists>j\<ge>i. \<exists>w d seq. step_outcome (after_interference_run j) = Accepted (Installed w d seq)"
  proof -
    fix i
    assume "pending_ids (source_state (after_interference_run i)) \<noteq> {}"
    then have "i \<le> 1"
      by (auto simp: after_interference_run_def moved_end_def install_replica_def moved_work_def
         repair_start_def mk_event_def pending_ids_def dom_def split: if_splits)
    then show "\<exists>j\<ge>i. \<exists>w d seq. step_outcome (after_interference_run j) = Accepted (Installed w d seq)"
      by (intro exI[of _ 1]) (auto simp: after_interference_run_def mk_event_def)
  qed
  have start: "7 \<in> pending_ids (source_state (after_interference_run 0))"
    by (simp add: after_interference_run_def mk_event_def repair_start_def pending_ids_def dom_def)
  show ?thesis using recovery_finishes_under_finite_interference[OF after_interference_steps bound takes_repair] start
    by blast
qed

lemma no_scheduler_counterexample:
  defines "stalled \<equiv> mk_event repair_start Wait_For_Source (Internal ()) repair_start"
  shows "infinite_run (recovery_step {} {}) {repair_start} recovery_carrier (\<lambda>_. stalled) \<and>
    (\<not> affects_recovery stalled) \<and> pending_ids (source_state stalled) = {7} \<and> 7 \<notin> completion_log (source_state stalled)"
  using repair_start_well_formed
  by (auto simp: stalled_def infinite_run_def step_occurs_def mk_event_def affects_recovery_def
    repair_start_def pending_ids_def dom_def intro: recovery_step.Idle)

definition one_release :: release_key where
  "one_release = (1, 3)"

definition queued_withdrawal :: catalog where
  "queued_withdrawal =
    \<lparr>mirrors = {1,2}, releases = {one_release}, tombstones = {one_release},
      raw_contents = (\<lambda>_. {one_release}), catalogue_pending = {(1,one_release)},
      catalogue_done = {}, host = id\<rparr>"

definition removed_from_mirror :: catalog where
  "removed_from_mirror = (record_copy queued_withdrawal (1,one_release))
    \<lparr>raw_contents := (raw_contents queued_withdrawal)(1 := {})\<rparr>"

definition catalogue_example :: "nat \<Rightarrow> catalogue_event" where
  "catalogue_example n =
    (if n = 0 then mk_event queued_withdrawal (Copy (1,one_release))
      (Accepted (Withdrew_From_Mirror (1,one_release))) removed_from_mirror
     else mk_event removed_from_mirror No_Catalogue_Work (Internal ()) removed_from_mirror)"

lemma actual_tombstone_install:
  "catalogue_step queued_withdrawal (Copy (1,one_release)) (Accepted (Withdrew_From_Mirror (1,one_release))) removed_from_mirror"
  unfolding removed_from_mirror_def
  using catalogue_step.Propagate_Withdrawal[of "(1,one_release)" queued_withdrawal 1 one_release]
  by (simp add: queued_withdrawal_def)

lemma stale_bytes_cannot_revive_withdrawn_release:
  "one_release \<in> raw_contents queued_withdrawal 2 \<and>
   catalogue_step queued_withdrawal (Read_Package 2 one_release) (Rejected ()) queued_withdrawal"
  by (simp add: queued_withdrawal_def; rule catalogue_step.Reject)
     (simp add: visible_catalogue_def queued_withdrawal_def)

lemma catalogue_example_run:
  "infinite_run catalogue_step {queued_withdrawal} catalogue_carrier catalogue_example"
  using actual_tombstone_install
  by (auto simp: infinite_run_def step_occurs_def catalogue_example_def mk_event_def catalogue_carrier_def
      queued_withdrawal_def removed_from_mirror_def record_copy_def split: if_splits intro: catalogue_step.Idle)

theorem recorded_withdrawal_activates_catalogue_completion:
  "\<exists>n. \<forall>i\<ge>n. (1,one_release) \<in> catalogue_done (source_state (catalogue_example i))"
proof -
  have "{} = {i. catalogue_interrupts (step_outcome (catalogue_example i))}"
    by (auto simp: catalogue_interrupts_def catalogue_example_def mk_event_def split: if_splits)
  then have finite: "finite {i. catalogue_interrupts (step_outcome (catalogue_example i))}" by simp
  have actual: "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> catalogue_interrupts (step_outcome (catalogue_example j))) \<Longrightarrow>
    catalogue_pending (source_state (catalogue_example i)) \<noteq> {} \<Longrightarrow>
    \<exists>j\<ge>i. \<exists>job. step_outcome (catalogue_example j) = Accepted (Copied job) \<or>
                      step_outcome (catalogue_example j) = Accepted (Withdrew_From_Mirror job)"
  proof -
    fix i assume "catalogue_pending (source_state (catalogue_example i)) \<noteq> {}"
    then have "i = 0"
      by (auto simp: catalogue_example_def mk_event_def removed_from_mirror_def record_copy_def
        queued_withdrawal_def split: if_splits)
    then show "\<exists>j\<ge>i. \<exists>job. step_outcome (catalogue_example j) = Accepted (Copied job) \<or>
                       step_outcome (catalogue_example j) = Accepted (Withdrew_From_Mirror job)"
      by (intro exI[of _ 0]) (auto simp: catalogue_example_def mk_event_def)
  qed
  have started: "(1,one_release) \<in> catalogue_pending (source_state (catalogue_example 0))"
    by (simp add: catalogue_example_def mk_event_def queued_withdrawal_def)
  show ?thesis
    using catalogue_drains_under_finite_interference[OF catalogue_example_run finite actual] started by blast
qed

end
