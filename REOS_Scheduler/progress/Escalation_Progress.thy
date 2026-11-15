theory Escalation_Progress
  imports Request_Progress
begin

lemma bounded_severity_update:
  assumes "active_case_levels keys s"
    and "\<And>k. k \<in> keys \<Longrightarrow> k = changed_case \<Longrightarrow> new_level \<le> severity_limit s k"
  shows "active_case_levels keys (s\<lparr>severity_now := (severity_now s)(changed_case := new_level)\<rparr>)"
  using assms by (auto simp: active_case_levels_def)

lemma active_cases_stay_within_their_limits:
  assumes happens: "step_occurs scheduler_step e"
    and bound: "active_case_levels keys (source_state e)"
  shows "active_case_levels keys (target_state e)"
proof (cases "spends_priority e")
  case False
  from nonpriority_step_preserves_levels[OF happens False] bound show ?thesis
    by (simp add: active_case_levels_def)
next
  case True
  let ?s = "source_state e"
  let ?t = "target_state e"
  from True obtain q k where result: "step_outcome e = Internal (Served_Regulation q k)"
    by (auto simp: spends_priority_def)
  from happens result have step: "scheduler_step ?s (step_action e) (Internal (Served_Regulation q k)) ?t"
    by (simp add: step_occurs_def)
  from regulated_result_is_an_honest_service[OF step] step have
    service: "scheduler_step ?s Honest_Service (Internal (Served_Regulation q k)) ?t" by simp
  from service obtain p u where effect: "regulatory_effect ?s p = Some u"
    and final: "?t = u\<lparr>regulatory_queue := remove1 p (regulatory_queue ?s),
       regulation_receipts := (regulation_receipts ?s)(q \<mapsto> p)\<rparr>"
    by (elim honest_service_uses_selected_regulation)
  have "active_case_levels keys u"
  proof (cases "packet_contents p")
    case (Ordinary_Work n)
    with effect show ?thesis by (simp add: regulatory_effect_def split: if_splits)
  next
    case (Raise_Level j level)
    from effect Raise_Level have updated: "u = ?s\<lparr>severity_now := (severity_now ?s)(j := level)\<rparr>"
      and capped: "level \<le> severity_limit ?s j"
      by (auto simp: regulatory_effect_def split: if_splits)
    from bounded_severity_update[where changed_case=j and new_level=level, OF bound] capped updated
    show ?thesis by simp
  next
    case (Lower_Level j level)
    from effect Lower_Level have updated: "u = ?s\<lparr>severity_now := (severity_now ?s)(j := level)\<rparr>"
      and lower: "level < severity_now ?s j"
      by (auto simp: regulatory_effect_def split: if_splits)
    have "active_case_levels keys (?s\<lparr>severity_now := (severity_now ?s)(j := level)\<rparr>)"
    proof (rule bounded_severity_update[OF bound])
      fix k
      assume ki: "k \<in> keys" and same: "k = j"
      from bound ki have "severity_now ?s k \<le> severity_limit ?s k"
        by (simp add: active_case_levels_def)
      with same lower show "level \<le> severity_limit ?s k" by (simp; linarith)
    qed
    with updated show ?thesis by simp
  next
    case (Execute_Governed_Rollback r a pf)
    from effect Execute_Governed_Rollback obtain c where
      "u = ?s\<lparr>rollback_context := c\<rparr>"
      by (auto simp: regulatory_effect_def split: if_splits prod.splits transition_result.splits)
    with bound show ?thesis by (simp add: active_case_levels_def)
  qed
  then show ?thesis by (simp add: final active_case_levels_def)
qed

lemma finite_interference_when_only_fixed_cases_escalate:
  assumes run: "infinite_run scheduler_step initial carrier events"
    and finite_keys: "finite keys"
    and ready: "active_case_levels keys (source_state (events 0))"
    and raises_only: "\<And>i. escalation_slice keys (events i)"
  shows "finite {i. spends_priority (events i)}"
proof -
  let ?s = "\<lambda>i. source_state (events i)"
  let ?used = "\<lambda>i. used_levels keys (?s i)"
  let ?cap = "level_capacity keys (?s 0)"
  let ?paid = "{i. spends_priority (events i)}"
  have occurs: "\<And>i. step_occurs scheduler_step (events i)"
    and linked: "\<And>i. target_state (events i) = ?s (Suc i)"
    using run by (simp_all add: infinite_run_def)
  have invariant: "\<And>i. active_case_levels keys (?s i) \<and> level_capacity keys (?s i) = ?cap"
  proof -
    fix i
    show "active_case_levels keys (?s i) \<and> level_capacity keys (?s i) = ?cap"
    proof (induction i)
      case 0
      with ready show ?case by simp
    next
      case (Suc i)
      then have bound: "active_case_levels keys (?s i)" by simp
      from one_escalation_step[OF occurs raises_only finite_keys bound] linked[of i] Suc.IH show ?case by auto
    qed
  qed
  have charged: "\<And>i. ?used i + priority_charge (events i) \<le> ?used (Suc i)"
  proof -
    fix i
    from invariant[of i] have "active_case_levels keys (?s i)" by simp
    from one_escalation_step[OF occurs raises_only finite_keys this] linked[of i]
    show "?used i + priority_charge (events i) \<le> ?used (Suc i)" by auto
  qed
  have mono_one: "\<And>i. ?used i \<le> ?used (Suc i)"
  proof -
    fix i
    have "?used i \<le> ?used i + priority_charge (events i)" by simp
    then show "?used i \<le> ?used (Suc i)" using charged[of i] by (rule order_trans)
  qed
  have strict: "\<And>i j. i \<in> ?paid \<Longrightarrow> i < j \<Longrightarrow> ?used i < ?used j"
  proof -
    fix i j
    assume cost: "i \<in> ?paid" and later: "i < j"
    from cost charged[of i] have raise: "?used i < ?used (Suc i)"
      by (simp add: priority_charge_def)
    have "?used (Suc i) \<le> ?used j"
    proof (rule dosp_tail_order[where f="?used" and start=0])
      show "\<And>n. 0 \<le> n \<Longrightarrow> ?used n \<le> ?used (Suc n)" by (rule mono_one)
      show "0 \<le> Suc i" by simp
      show "Suc i \<le> j" using later by simp
    qed
    with raise show "?used i < ?used j" by (rule less_le_trans)
  qed
  have injective: "inj_on ?used ?paid"
  proof (rule inj_onI)
    fix i j
    assume costs: "i \<in> ?paid" "j \<in> ?paid" and same: "?used i = ?used j"
    from strict[OF costs(1), of j] strict[OF costs(2), of i] same
    show "i = j" by (cases i j rule: linorder_cases) auto
  qed
  have bound: "\<And>i. ?used i \<le> ?cap"
  proof -
    fix i
    from invariant[of i] have "active_case_levels keys (?s i)" by simp
    then have "used_levels keys (?s i) \<le> level_capacity keys (?s i)"
      by (auto simp: used_levels_def level_capacity_def active_case_levels_def intro!: sum_mono)
    with invariant[of i] show "?used i \<le> ?cap" by simp
  qed
  have "image ?used ?paid \<subseteq> {.. ?cap}" using bound by auto
  then have "finite (image ?used ?paid)" by (rule finite_subset) simp
  from this injective show ?thesis by (rule finite_imageD)
qed

theorem admitted_packet_is_served_under_fixed_case_escalation:
  assumes origin: "coherent_ordinary_queue before"
    and admitted: "scheduler_step before (Submit p) (Accepted (packet_identity p)) admitted_state"
    and ordinary: "ordinary_body (packet_contents p)"
    and run: "infinite_run scheduler_step {admitted_state} carrier events"
    and finite_keys: "finite keys"
    and ready: "active_case_levels keys (source_state (events 0))"
    and raises_only: "\<And>i. escalation_slice keys (events i)"
    and opportunities: "\<And>i. \<exists>j\<ge>i. step_action (events j) = Honest_Service"
  shows "\<exists>j. served_ordinary (packet_identity p) (events j) \<and>
    ordinary_receipts (target_state (events j)) (packet_identity p) = Some p"
  by (rule admitted_packet_is_served_under_finite_interference[OF origin admitted ordinary run
    finite_interference_when_only_fixed_cases_escalate[OF run finite_keys ready raises_only] opportunities])

theorem starvation_in_a_fixed_case_run_needs_infinitely_many_non_escalating_turns:
  assumes run: "infinite_run scheduler_step initial carrier events"
    and coherent0: "coherent_ordinary_queue (source_state (events 0))"
    and waiting0: "waiting q (source_state (events 0))"
    and levels0: "active_case_levels keys (source_state (events 0))"
    and finite_keys: "finite keys"
    and opportunities: "\<And>i. \<exists>j\<ge>i. step_action (events j) = Honest_Service"
    and starves: "\<And>i. \<not> served_ordinary q (events i)"
  shows "infinite {i. \<not> escalation_slice keys (events i)}"
proof
  let ?s = "\<lambda>i. source_state (events i)"
  let ?noise = "{i. \<not> escalation_slice keys (events i)}"
  assume countable_last: "finite ?noise"
  define offset where "offset = Suc (Max ?noise)"
  let ?tail = "\<lambda>i. events (offset+i)"
  have occurs: "\<And>i. step_occurs scheduler_step (events i)"
    and linked: "\<And>i. target_state (events i) = ?s (Suc i)"
    using run by (simp_all add: infinite_run_def)
  have waiting_everywhere: "\<And>i. waiting q (?s i)"
  proof -
    fix i
    show "waiting q (?s i)"
    proof (induction i)
      case 0
      show ?case by (rule waiting0)
    next
      case (Suc i)
      from waiting_persists_without_its_service[OF occurs[of i] Suc.IH starves[of i]]
        linked[of i] show ?case by simp
    qed
  qed
  have coherent_at_offset: "coherent_ordinary_queue (?s offset)"
    by (rule ordinary_state_along_run[where events=events and P=coherent_ordinary_queue,
        OF occurs linked coherent0])
      (auto simp: step_occurs_def intro: scheduler_ordinarily_coherent)
  have levels_at_offset: "active_case_levels keys (?s offset)"
    by (rule ordinary_state_along_run[where events=events and P="active_case_levels keys",
        OF occurs linked levels0])
      (rule active_cases_stay_within_their_limits)
  have escalation_tail: "\<And>i. escalation_slice keys (?tail i)"
  proof -
    fix i
    show "escalation_slice keys (?tail i)"
    proof (rule ccontr)
      assume "\<not> escalation_slice keys (?tail i)"
      then have "offset+i \<le> Max ?noise" by (intro Max_ge[OF countable_last]) simp
      then show False by (simp add: offset_def)
    qed
  qed
  have tail_run: "infinite_run scheduler_step {?s offset} carrier ?tail"
    using run by (simp add: infinite_run_def add_Suc_right)
  have tail_opportunities: "\<And>i. \<exists>j\<ge>i. step_action (?tail j) = Honest_Service"
  proof -
    fix i
    from opportunities[of "offset+i"] obtain j where "offset+i \<le> j"
      "step_action (events j) = Honest_Service" by blast
    then show "\<exists>j\<ge>i. step_action (?tail j) = Honest_Service"
      by (intro exI[of _ "j-offset"]) auto
  qed
  have levels_tail: "active_case_levels keys (source_state (?tail 0))" using levels_at_offset by simp
  have finite_tail: "finite {i. spends_priority (?tail i)}"
    by (rule finite_interference_when_only_fixed_cases_escalate[OF tail_run finite_keys levels_tail escalation_tail])
  from waiting_everywhere[of offset] obtain p where some_packet: "p \<in> set (ordinary_queue (?s offset))"
    and key: "packet_identity p = q" by (auto simp: waiting_def)
  have coherent_tail: "coherent_ordinary_queue (source_state (?tail 0))" using coherent_at_offset by simp
  have packet_tail: "p \<in> set (ordinary_queue (source_state (?tail 0)))" using some_packet by simp
  from queued_packet_is_served_under_finite_interference[OF tail_run coherent_tail packet_tail finite_tail tail_opportunities]
    starves key show False by blast
qed

definition lowers_a_case ::
  "nat set \<Rightarrow> (scheduler_state,scheduler_action,scheduler_result) transition \<Rightarrow> bool"
where
  "lowers_a_case keys e \<longleftrightarrow>
    (\<exists>p q k level. next_regulation (source_state e) = Some p \<and>
      packet_contents p = Lower_Level k level \<and> k \<in> keys \<and>
      step_outcome e = Internal (Served_Regulation q k))"

theorem starvation_with_only_fixed_case_level_changes_requires_infinite_lowering:
  assumes run: "infinite_run scheduler_step initial carrier events"
    and coherent0: "coherent_ordinary_queue (source_state (events 0))"
    and waiting0: "waiting q (source_state (events 0))"
    and levels0: "active_case_levels keys (source_state (events 0))"
    and finite_keys: "finite keys"
    and opportunities: "\<And>i. \<exists>j\<ge>i. step_action (events j) = Honest_Service"
    and starves: "\<And>i. \<not> served_ordinary q (events i)"
    and level_only: "\<And>i. spends_priority (events i) \<Longrightarrow>
      raises_a_case keys (events i) \<or> lowers_a_case keys (events i)"
  shows "infinite {i. lowers_a_case keys (events i)}"
proof
  assume finite_lower: "finite {i. lowers_a_case keys (events i)}"
  have "{i. \<not> escalation_slice keys (events i)} \<subseteq> {i. lowers_a_case keys (events i)}"
    using level_only by (auto simp: escalation_slice_def)
  from finite_subset[OF this finite_lower] show False
    using starvation_in_a_fixed_case_run_needs_infinitely_many_non_escalating_turns[
      OF run coherent0 waiting0 levels0 finite_keys opportunities starves] by blast
qed

end
