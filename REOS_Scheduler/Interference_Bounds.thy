theory Interference_Bounds
  imports Scheduler_Safety
begin

definition active_case_levels :: "nat set \<Rightarrow> scheduler_state \<Rightarrow> bool"
where
  "active_case_levels keys s \<longleftrightarrow> (\<forall>k \<in> keys. severity_now s k \<le> severity_limit s k)"

definition raises_a_case ::
  "nat set \<Rightarrow> (scheduler_state,scheduler_action,scheduler_result) transition \<Rightarrow> bool"
where
  "raises_a_case keys e \<longleftrightarrow>
    (\<exists>p q k level. next_regulation (source_state e) = Some p \<and>
      packet_contents p = Raise_Level k level \<and> k \<in> keys \<and>
      step_outcome e = Internal (Served_Regulation q k))"

definition escalation_slice ::
  "nat set \<Rightarrow> (scheduler_state,scheduler_action,scheduler_result) transition \<Rightarrow> bool"
where "escalation_slice keys e \<longleftrightarrow> (\<not> spends_priority e \<or> raises_a_case keys e)"

definition used_levels :: "nat set \<Rightarrow> scheduler_state \<Rightarrow> nat"
where "used_levels keys s = sum (severity_now s) keys"

definition level_capacity :: "nat set \<Rightarrow> scheduler_state \<Rightarrow> nat"
where "level_capacity keys s = sum (severity_limit s) keys"

definition priority_charge ::
  "(scheduler_state,scheduler_action,scheduler_result) transition \<Rightarrow> nat"
where "priority_charge e = (if spends_priority e then 1 else 0)"

lemma regulated_result_is_an_honest_service:
  assumes "scheduler_step s action (Internal (Served_Regulation q k)) t"
  shows "action = Honest_Service"
  using assms by (cases action)
    (auto simp: scheduler_step_def admit_def split: if_splits)

lemma unregulated_step_frame:
  assumes step: "scheduler_step s action result t"
    and not_regulation: "\<And>q k. result \<noteq> Internal (Served_Regulation q k)"
  shows "severity_now t = severity_now s \<and> severity_limit t = severity_limit s"
proof (cases action)
  case (Submit p)
  from step Submit show ?thesis
    by (auto simp: scheduler_step_def admit_def enqueue_packet_def Let_def split: if_splits)
next
  case Honest_Service
  with step have tick: "scheduler_step s Honest_Service result t" by simp
  show ?thesis
  proof (cases "next_regulation s")
    case None
    from tick None show ?thesis
      by (auto simp: scheduler_step_def schedule_contract serve_ordinary_def split: list.splits if_splits)
  next
    case (Some p)
    from selected_regulation_ready(1)[OF Some] obtain u where actual: "regulatory_effect s p = Some u"
      by (auto simp: ready_regulation_def)
    from tick Some actual have "result = Internal (Served_Regulation (packet_identity p) (regulatory_case (packet_contents p)))"
      by (simp add: scheduler_step_def schedule_contract)
    with not_regulation show ?thesis by blast
  qed
next
  case Unproductive_Turn
  with step show ?thesis by (simp add: scheduler_step_def)
next
  case (Rotate_Context time a k epoch)
  from step Rotate_Context show ?thesis by (auto simp: scheduler_step_def split: if_splits)
qed

lemma nonpriority_step_preserves_levels:
  assumes actual: "step_occurs scheduler_step e" and nocharge: "\<not> spends_priority e"
  shows "severity_now (target_state e) = severity_now (source_state e)"
    and "severity_limit (target_state e) = severity_limit (source_state e)"
proof -
  from actual have step: "scheduler_step (source_state e) (step_action e) (step_outcome e) (target_state e)"
    by (simp add: step_occurs_def)
  have no_regulated_result: "\<And>q k. step_outcome e \<noteq> Internal (Served_Regulation q k)"
    using nocharge by (simp add: spends_priority_def)
  from unregulated_step_frame[OF step no_regulated_result] show
    "severity_now (target_state e) = severity_now (source_state e)"
    "severity_limit (target_state e) = severity_limit (source_state e)" by simp_all
qed

lemma productive_raise_exact_update:
  assumes actual: "step_occurs scheduler_step e" and rise: "raises_a_case keys e"
  obtains k level where "k \<in> keys"
    "severity_now (source_state e) k < level" "level \<le> severity_limit (source_state e) k"
    "severity_now (target_state e) = (severity_now (source_state e))(k := level)"
    "severity_limit (target_state e) = severity_limit (source_state e)"
proof -
  let ?s = "source_state e"
  let ?t = "target_state e"
  from rise obtain p q k level where selected: "next_regulation ?s = Some p"
    and body: "packet_contents p = Raise_Level k level" and member: "k \<in> keys"
    and performed: "step_outcome e = Internal (Served_Regulation q k)"
    by (auto simp: raises_a_case_def)
  from actual performed have
    phase: "scheduler_step ?s (step_action e) (Internal (Served_Regulation q k)) ?t"
    by (simp add: step_occurs_def)
  from phase have "step_action e = Honest_Service" by (rule regulated_result_is_an_honest_service)
  with phase have svc: "scheduler_step ?s Honest_Service (Internal (Served_Regulation q k)) ?t" by simp
  from svc obtain selected_packet u where
    picked: "next_regulation ?s = Some selected_packet"
    and effect: "regulatory_effect ?s selected_packet = Some u"
    and post: "?t = u\<lparr>regulatory_queue := remove1 selected_packet (regulatory_queue ?s),
        regulation_receipts := (regulation_receipts ?s)(q \<mapsto> selected_packet)\<rparr>"
    by (elim honest_service_uses_selected_regulation)
  from picked selected have "selected_packet = p" by simp
  with effect body have strict: "severity_now ?s k < level" and within: "level \<le> severity_limit ?s k"
    and u: "u = ?s\<lparr>severity_now := (severity_now ?s)(k := level)\<rparr>"
    by (auto simp: regulatory_effect_def split: if_splits)
  show thesis
  proof (rule that[OF member strict within])
    show "severity_now ?t = (severity_now ?s)(k := level)" by (simp add: post u)
    show "severity_limit ?t = severity_limit ?s" by (simp add: post u)
  qed
qed

lemma one_escalation_step:
  assumes connected: "step_occurs scheduler_step e" and allowed: "escalation_slice keys e"
    and finite: "finite keys" and before: "active_case_levels keys (source_state e)"
  shows "active_case_levels keys (target_state e) \<and>
    level_capacity keys (target_state e) = level_capacity keys (source_state e) \<and>
    used_levels keys (source_state e) + priority_charge e \<le> used_levels keys (target_state e)"
proof (cases "spends_priority e")
  case False
  with nonpriority_step_preserves_levels[OF connected] before show ?thesis
    by (simp add: active_case_levels_def level_capacity_def used_levels_def priority_charge_def)
next
  case True
  with allowed have rise: "raises_a_case keys e" by (simp add: escalation_slice_def)
  let ?s = "source_state e"
  let ?t = "target_state e"
  from productive_raise_exact_update[OF connected rise] obtain k new_level where
    k: "k \<in> keys" and inc: "severity_now ?s k < new_level"
    and within: "new_level \<le> severity_limit ?s k"
    and changed: "severity_now ?t = (severity_now ?s)(k := new_level)"
    and cap: "severity_limit ?t = severity_limit ?s" by blast
  from before within changed cap have invariant: "active_case_levels keys ?t"
    by (auto simp: active_case_levels_def)
  have "sum (severity_now ?t) (keys - {k}) = sum (severity_now ?s) (keys - {k})"
    by (rule sum.cong[OF refl]) (simp add: changed)
  moreover have "sum (severity_now ?s) keys = severity_now ?s k + sum (severity_now ?s) (keys - {k})"
    by (rule sum.remove[OF finite k])
  moreover have "sum (severity_now ?t) keys = new_level + sum (severity_now ?t) (keys - {k})"
    by (subst sum.remove[OF finite k]) (simp add: changed)
  ultimately have budget: "used_levels keys ?s + 1 \<le> used_levels keys ?t"
    using inc by (simp add: used_levels_def; linarith)
  from True invariant cap budget show ?thesis by (simp add: level_capacity_def priority_charge_def)
qed

theorem prefix_of_escalations_consumes_capacity:
  assumes finite: "finite keys"
    and trace: "finite_trace scheduler_step carrier s es t"
    and start: "active_case_levels keys s"
    and coverage: "\<forall>e\<in>set es. escalation_slice keys e"
  shows "active_case_levels keys t \<and>
    level_capacity keys t = level_capacity keys s \<and>
    used_levels keys s + sum_list (map priority_charge es) \<le> used_levels keys t"
  using trace start coverage
proof (induction es arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  then have origin: "source_state e = s" and happens: "step_occurs scheduler_step e"
    and tail: "finite_trace scheduler_step carrier (target_state e) es t"
    and admissible: "escalation_slice keys e" and remaining: "\<forall>ev\<in>set es. escalation_slice keys ev"
    by auto
  with Cons.prems(2) have active: "active_case_levels keys (source_state e)" by simp
  from one_escalation_step[OF happens admissible finite active] origin have
    active_t: "active_case_levels keys (target_state e)"
    and cap: "level_capacity keys (target_state e) = level_capacity keys s"
    and cost: "used_levels keys s + priority_charge e \<le> used_levels keys (target_state e)"
    by auto
  from Cons.IH[OF tail active_t remaining] cap cost show ?case by (simp; linarith)
qed

theorem finite_escalation_interference_bound:
  assumes "finite keys" "finite_trace scheduler_step carrier s es t"
    "active_case_levels keys s" "\<forall>e\<in>set es. escalation_slice keys e"
  shows "sum_list (map priority_charge es) \<le> level_capacity keys s - used_levels keys s"
proof -
  from prefix_of_escalations_consumes_capacity[OF assms] have
    active: "active_case_levels keys t" and cap: "level_capacity keys t = level_capacity keys s"
    and charged: "used_levels keys s + sum_list (map priority_charge es) \<le> used_levels keys t" by blast+
  from active have "used_levels keys t \<le> level_capacity keys t"
    by (auto simp: used_levels_def level_capacity_def active_case_levels_def intro!: sum_mono)
  with cap charged show ?thesis by linarith
qed

theorem priority_beyond_the_ceiling_needs_a_non_escalation:
  assumes "finite keys" "finite_trace scheduler_step carrier s es t" "active_case_levels keys s"
    and excess: "level_capacity keys s - used_levels keys s < sum_list (map priority_charge es)"
  shows "\<exists>e\<in>set es. spends_priority e \<and> \<not> raises_a_case keys e"
  using finite_escalation_interference_bound[OF assms(1-3)] excess
  unfolding escalation_slice_def by fastforce

end
