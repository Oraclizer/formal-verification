theory Quiet_Run_Examples
  imports Quiet_Run_Comparison
begin

definition leave_after_repair :: "nat recovery_state" where
  "leave_after_repair = repair_end\<lparr>active_domains := active_domains repair_end - {1},
      route_epoch := 3, work_owner := carry_owner 1 2 (work_owner repair_end)\<rparr>"

lemma repair_before_unowned_departure:
  "recovery_step departure_grants {} repair_start (Apply_Repair 7 20) (Accepted (Installed 7 1 20)) repair_end"
  by (unfold repair_end_def, rule recovery_step.Ordinary_Repair) (simp_all add: repair_start_def)

lemma unowned_departure_occurs_after_repair:
  "recovery_step departure_grants {} repair_end (Activate (Leave_Domain 1 2) 3 8 8)
    (Accepted (Left 1 2)) leave_after_repair"
  unfolding leave_after_repair_def
  by (rule recovery_step.Leave_Route)
     (simp_all add: current_grant_def departure_grants_def repair_end_def repair_start_def install_replica_def)

definition unowned_departure_run :: "nat \<Rightarrow> nat repair_event" where
  "unowned_departure_run i =
    (if i = 0 then mk_event repair_start (Apply_Repair 7 20) (Accepted (Installed 7 1 20)) repair_end
     else if i = 1 then mk_event repair_end (Activate (Leave_Domain 1 2) 3 8 8) (Accepted (Left 1 2)) leave_after_repair
     else mk_event leave_after_repair Wait_For_Source (Internal ()) leave_after_repair)"

lemma unowned_departure_run_is_actual:
  "infinite_run (recovery_step departure_grants {}) {repair_start} recovery_carrier unowned_departure_run"
proof -
  have final_valid: "leave_after_repair \<in> recovery_carrier"
    by (rule recovery_carrier_closed[OF unowned_departure_occurs_after_repair repair_end_well_formed])
  show ?thesis using final_valid repair_start_well_formed repair_end_well_formed
    repair_before_unowned_departure unowned_departure_occurs_after_repair
    by (auto simp: infinite_run_def step_occurs_def unowned_departure_run_def mk_event_def
        split: if_splits intro: recovery_step.Idle)
qed

lemma unowned_departure_run_has_no_recovery_interference:
  "\<not> affects_recovery (unowned_departure_run i)"
  by (auto simp: unowned_departure_run_def mk_event_def affects_recovery_def repair_end_def
    repair_start_def install_replica_def split: if_splits)

lemma unowned_departure_run_has_finite_interference:
  "finite {i. affects_recovery (unowned_departure_run i)}"
  by (simp add: unowned_departure_run_has_no_recovery_interference)

lemma unowned_departure_run_selects_repair:
  assumes "pending_ids (source_state (unowned_departure_run i)) \<noteq> {}"
  shows "\<exists>j\<ge>i. \<exists>w d seq. step_outcome (unowned_departure_run j) = Accepted (Installed w d seq)"
proof -
  from assms have "i = 0"
    by (auto simp: unowned_departure_run_def mk_event_def leave_after_repair_def repair_end_def repair_start_def
        carry_owner_def install_replica_def pending_ids_def dom_def split: if_splits)
  then show ?thesis by (intro exI[of _ 0]) (simp add: unowned_departure_run_def mk_event_def)
qed

lemma unowned_departure_run_has_an_atomic_replica_endpoint:
  "\<exists>k n. k \<le> n \<and> (\<forall>i\<ge>n. replica (source_state (unowned_departure_run i)) =
    update_cells (active_domains (source_state (unowned_departure_run k)))
      (\<lambda>_. primary_record (source_state (unowned_departure_run k)))
      (replica (source_state (unowned_departure_run k))))"
proof -
  have selected: "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> affects_recovery (unowned_departure_run j)) \<Longrightarrow>
      pending_ids (source_state (unowned_departure_run i)) \<noteq> {} \<Longrightarrow>
      \<exists>j\<ge>i. \<exists>w d seq. step_outcome (unowned_departure_run j) = Accepted (Installed w d seq)"
    by (rule unowned_departure_run_selects_repair)
  show ?thesis
  proof (rule finite_interference_reaches_the_atomic_replica_update[
      OF unowned_departure_run_is_actual unowned_departure_run_has_finite_interference selected])
    fix k n
    assume kn: "k \<le> n"
      and "\<And>j. k \<le> j \<Longrightarrow> \<not> affects_recovery (unowned_departure_run j)"
      and window: "\<And>i. n \<le> i \<Longrightarrow>
        finite_trace (recovery_step departure_grants {}) recovery_carrier
          (source_state (unowned_departure_run k)) (map unowned_departure_run [k..<i])
          (source_state (unowned_departure_run i)) \<and>
        pending_ids (source_state (unowned_departure_run i)) = {} \<and>
        replica (source_state (unowned_departure_run i)) =
          update_cells (active_domains (source_state (unowned_departure_run k)))
            (\<lambda>_. primary_record (source_state (unowned_departure_run k)))
            (replica (source_state (unowned_departure_run k))) \<and>
        active_domains (source_state (unowned_departure_run i)) \<subseteq>
          active_domains (source_state (unowned_departure_run k)) \<and>
        primary_record (source_state (unowned_departure_run i)) = primary_record (source_state (unowned_departure_run k)) \<and>
        primary_sequence (source_state (unowned_departure_run i)) = primary_sequence (source_state (unowned_departure_run k)) \<and>
        irreversible_facts (source_state (unowned_departure_run i)) = irreversible_facts (source_state (unowned_departure_run k)) \<and>
        (\<forall>j\<le>i. pending_ids (source_state (unowned_departure_run j)) \<union>
          completion_log (source_state (unowned_departure_run j)) \<subseteq> completion_log (source_state (unowned_departure_run i)))"
    have replicas: "\<forall>i\<ge>n. replica (source_state (unowned_departure_run i)) =
      update_cells (active_domains (source_state (unowned_departure_run k)))
        (\<lambda>_. primary_record (source_state (unowned_departure_run k)))
        (replica (source_state (unowned_departure_run k)))"
    proof (intro allI impI)
      fix i assume late: "n \<le> i"
      show "replica (source_state (unowned_departure_run i)) =
        update_cells (active_domains (source_state (unowned_departure_run k)))
          (\<lambda>_. primary_record (source_state (unowned_departure_run k)))
          (replica (source_state (unowned_departure_run k)))"
        by (rule conjunct1[OF conjunct2[OF conjunct2[OF window[OF late]]]])
    qed
    show ?thesis by (rule exI[of _ k], rule exI[of _ n], rule conjI[OF kn replicas])
  qed
qed

theorem completed_replica_is_preserved_after_unowned_departure:
  "finite_trace (recovery_step departure_grants {}) recovery_carrier repair_start
    (map unowned_departure_run [0..<2]) leave_after_repair"
  "replica leave_after_repair = update_cells (active_domains repair_start)
    (\<lambda>_. primary_record repair_start) (replica repair_start)"
  "active_domains leave_after_repair = {2} \<and> replica leave_after_repair 1 = 41"
  "replica leave_after_repair \<noteq> update_cells (active_domains leave_after_repair)
    (\<lambda>_. primary_record repair_start) (replica repair_start)"
proof -
  have start: "source_state (unowned_departure_run 0) = repair_start"
    and finish: "source_state (unowned_departure_run 2) = leave_after_repair"
    by (simp_all add: unowned_departure_run_def mk_event_def)
  have drained: "pending_ids (source_state (unowned_departure_run 2)) = {}"
    by (simp add: finish pending_ids_def leave_after_repair_def repair_end_def repair_start_def
      carry_owner_def install_replica_def dom_def)
  have bound: "0 \<le> (2::nat)" by simp
  have quiet: "\<And>j. 0 \<le> j \<Longrightarrow> j < 2 \<Longrightarrow> \<not> affects_recovery (unowned_departure_run j)"
    by (rule unowned_departure_run_has_no_recovery_interference)
  note window = quiet_drained_window_is_atomic_at_original_footprint[
    OF unowned_departure_run_is_actual bound quiet drained]
  show "finite_trace (recovery_step departure_grants {}) recovery_carrier repair_start
    (map unowned_departure_run [0..<2]) leave_after_repair"
    using window(1) by (simp add: start finish)
  show "replica leave_after_repair = update_cells (active_domains repair_start)
    (\<lambda>_. primary_record repair_start) (replica repair_start)"
    using window(2) by (simp add: start finish)
  show cells: "active_domains leave_after_repair = {2} \<and> replica leave_after_repair 1 = 41"
    by (auto simp: leave_after_repair_def repair_end_def repair_start_def install_replica_def)
  show "replica leave_after_repair \<noteq> update_cells (active_domains leave_after_repair)
    (\<lambda>_. primary_record repair_start) (replica repair_start)"
  proof
    assume equal: "replica leave_after_repair = update_cells (active_domains leave_after_repair)
      (\<lambda>_. primary_record repair_start) (replica repair_start)"
    from fun_cong[OF equal, of 1] cells show False
      by (simp add: update_cells_def repair_start_def)
  qed
qed

end
