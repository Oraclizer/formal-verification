theory Recovery_Observations
  imports DOSP_Recovery.Recovery_Examples
begin

definition client_recovery_view :: "'d recovery_state \<Rightarrow> bool \<times> nat \<times> nat set" where
  "client_recovery_view s =
    (pending_ids s = {} \<and> \<not> rollback_incomplete s, primary_record s, irreversible_facts s)"

lemma membership_activates_existing_replica_and_requires_a_job:
  assumes "recovery_step grants governance s (Activate (Join_Domain d job) epoch boundary time)
    (Accepted (Joined d job)) t"
  shows "active_domains t = insert d (active_domains s) \<and> d \<notin> active_domains s \<and>
    replica t = replica s \<and> work_owner t job = Some d \<and> primary_record t = primary_record s"
  using assms by (cases rule: recovery_step.cases) auto

lemma join_can_break_immediate_replica_agreement:
  assumes join: "recovery_step grants governance s (Activate (Join_Domain d job) epoch boundary time)
    (Accepted (Joined d job)) t"
    and stale: "replica s d \<noteq> primary_record s"
  shows "\<not> (\<forall>x\<in>active_domains t. replica t x = primary_record t)"
  using membership_activates_existing_replica_and_requires_a_job[OF join] stale by auto

definition stale_join_start :: "nat recovery_state" where
  "stale_join_start = repair_start\<lparr>replica := (replica repair_start)(3 := 0)\<rparr>"

definition stale_join_end :: "nat recovery_state" where
  "stale_join_end = stale_join_start\<lparr>active_domains := insert 3 (active_domains stale_join_start),
    route_epoch := 2, work_owner := (work_owner stale_join_start)(9 \<mapsto> 3)\<rparr>"

lemma actual_join_admits_a_stale_replica_with_its_own_job:
  "recovery_step {(Join_Domain 3 9, 2, 8)} {} stale_join_start (Activate (Join_Domain 3 9) 2 8 8)
    (Accepted (Joined 3 9)) stale_join_end \<and>
   work_owner stale_join_end 9 = Some 3 \<and>
   replica stale_join_end 3 \<noteq> primary_record stale_join_end"
proof -
  have joined: "recovery_step {(Join_Domain 3 9, 2, 8)} {} stale_join_start (Activate (Join_Domain 3 9) 2 8 8)
    (Accepted (Joined 3 9)) stale_join_end"
    unfolding stale_join_end_def
    by (rule recovery_step.Join_Route) (simp_all add: current_grant_def fresh_work_def stale_join_start_def repair_start_def)
  then show ?thesis by (simp add: stale_join_end_def stale_join_start_def repair_start_def)
qed

lemma leaving_preserves_all_replica_cells_including_retired_cells:
  assumes "recovery_step grants governance s (Activate (Leave_Domain old successor) epoch boundary time)
    (Accepted (Left old successor)) t"
  shows "active_domains t = active_domains s - {old} \<and>
     replica t = replica s \<and> irreversible_facts t = irreversible_facts s"
  using assms by (cases rule: recovery_step.cases) auto

lemma governance_can_install_during_rollback_recovery:
  assumes "work_owner s job = Some d" "d \<in> active_domains s" "source_ready s"
    "rollback_incomplete s" "approval \<in> governance"
  shows "\<exists>t. recovery_step grants governance s (Governance_Resync approval job (primary_sequence s))
    (Accepted (Installed job d (primary_sequence s))) t \<and>
    recovery_step grants governance s (Ordinary_Trade tx) (Rejected Recovery_Blocks_Trade) s"
proof -
  have authorized: "recovery_step grants governance s (Governance_Resync approval job (primary_sequence s))
    (Accepted (Installed job d (primary_sequence s)))
    ((install_replica s job d)\<lparr>rollback_incomplete := pending_ids (install_replica s job d) \<noteq> {}\<rparr>)"
    using assms by (intro recovery_step.Authorized_Resync) simp_all
  have blocked: "recovery_step grants governance s (Ordinary_Trade tx) (Rejected Recovery_Blocks_Trade) s"
    using assms by (intro recovery_step.Refuse_Trade) simp
  show ?thesis using authorized blocked by blast
qed

lemma nonfinal_stepwise_install_is_client_stutter:
  assumes step: "step_occurs (recovery_step grants governance) e"
    and installed: "step_outcome e = Accepted (Installed job d seq)"
    and pending: "pending_ids (target_state e) \<noteq> {}"
  shows "observational_stutter (\<lambda>(_::unit) (_::unit). client_recovery_view) () () e"
proof -
  have transition: "recovery_step grants governance
    (source_state e) (step_action e) (Accepted (Installed job d seq)) (target_state e)"
    using step installed by (simp add: step_occurs_def)
  have old_pending: "pending_ids (source_state e) \<noteq> {}"
     using actual_install_uses_primary_record[OF transition]
     by (auto simp: pending_ids_def)
  have unchanged: "primary_record (target_state e) = primary_record (source_state e)"
    using transition by (cases rule: recovery_step.cases) (simp_all add: install_replica_def)
  show ?thesis
    using old_pending pending unchanged recovery_never_changes_irreversible_facts[OF transition]
    by (simp add: observational_stutter_def client_recovery_view_def)
qed

lemma exposed_replica_breaks_stepwise_stutter:
  assumes step: "step_occurs (recovery_step grants governance) e"
    and installed: "step_outcome e = Accepted (Installed job d seq)"
    and was_diverged: "replica (source_state e) d \<noteq> primary_record (source_state e)"
  shows "\<not> observational_stutter (\<lambda>observer (_::unit) s. replica s observer) d () e"
proof -
  have transition: "recovery_step grants governance
    (source_state e) (step_action e) (Accepted (Installed job d seq)) (target_state e)"
    using step installed by (simp add: step_occurs_def)
  show ?thesis using actual_install_uses_primary_record[OF transition] was_diverged
    by (simp add: observational_stutter_def)
qed

theorem two_source_repair_effects_commute_exactly:
  fixes original :: "'d \<Rightarrow> nat"
  shows "((original(first_domain := first_value))(second_domain := second_value) =
          (original(second_domain := second_value))(first_domain := first_value))
    \<longleftrightarrow> first_domain \<noteq> second_domain \<or> first_value = second_value"
proof (cases "first_domain = second_domain")
  case True
  then show ?thesis by (auto simp: fun_eq_iff fun_upd_apply)
next
  case False
  then show ?thesis by (simp add: fun_upd_twist)
qed

end
