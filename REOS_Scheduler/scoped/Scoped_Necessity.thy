theory Scoped_Necessity
  imports Scoped_Budgets Scoped_Receipts
begin

lemma finite_priority_on_an_eventually_budgeted_scoped_run:
  assumes run: "infinite_run (machine_step E) initial carrier events"
    and finite: "finite K"
    and tail: "\<And>i. start_index \<le> i \<Longrightarrow> budgeted_priority K (events i)"
  shows "finite {i. used_priority_slot (events i)}"
proof -
  let ?f = "\<lambda>i. case_credits K (source_state (events i))"
  have step: "?f (Suc i) + (if used_priority_slot (events i) then 1 else 0) \<le> ?f i"
    if index: "start_index \<le> i" for i
  proof -
    from run have occ: "step_occurs (machine_step E) (events i)"
      and link: "target_state (events i) = source_state (events (Suc i))"
      by (simp_all add: infinite_run_def)
    from budgeted_step_spends_at_most_available_credits[OF finite occ tail[OF index]] link
    show ?thesis by simp
  qed
  define least where "least = (LEAST n. \<exists>i\<ge>start_index. ?f i = n)"
  have "\<exists>n. \<exists>i\<ge>start_index. ?f i = n" by blast
  from LeastI_ex[OF this] obtain m where first: "start_index \<le> m" and low: "?f m = least"
    unfolding least_def by blast
  have minimal: "least \<le> ?f i" if "start_index \<le> i" for i
    unfolding least_def using that by (intro Least_le) blast
  have later: "?f i \<le> least" if "m \<le> i" for i
    using that
  proof (induction i)
    case 0
    with low show ?case by simp
  next
    case (Suc i)
    show ?case
    proof (cases "m \<le> i")
      case True
      from first True have "start_index \<le> i" by arith
      from step[OF this] Suc.IH[OF True] show ?thesis by linarith
    next
      case False
      from False Suc.prems have "Suc i = m" by simp
      with low show ?thesis by simp
    qed
  qed
  have no_late: "\<not> used_priority_slot (events i)" if "m \<le> i" for i
  proof
    assume slot: "used_priority_slot (events i)"
    from that first have earlier: "start_index \<le> i" and next_index: "start_index \<le> Suc i" by arith+
    from step[OF earlier] slot have "?f (Suc i) + 1 \<le> ?f i" by simp
    with minimal[OF next_index] later[OF that] show False by linarith
  qed
  have "{i. used_priority_slot (events i)} \<subseteq> {..<m}"
  proof (rule subsetI)
    fix i assume "i \<in> {i. used_priority_slot (events i)}"
    then have used: "used_priority_slot (events i)" by simp
    have "i < m"
    proof (rule ccontr)
      assume "\<not> i < m"
      then have "m \<le> i" by simp
      from no_late[OF this] used show False by simp
    qed
    then show "i \<in> {..<m}" by simp
  qed
  then show ?thesis by (rule finite_subset) simp
qed

theorem starvation_requires_priority_outside_every_finite_case_budget_on_every_tail:
  assumes trace: "infinite_run (machine_step E) initial carrier events"
    and coherent: "coherent_ordinary_queue (scheduler_at (source_state (events 0)))"
    and pending: "p \<in> set (ordinary_queue (scheduler_at (source_state (events 0))))"
    and opportunity: "\<And>i. (\<And>j. i \<le> j \<Longrightarrow>
      ordinary_queue (scheduler_at (source_state (events j))) \<noteq> []) \<Longrightarrow>
      \<exists>j\<ge>i. receives_fresh_choice E (offered j) (events j)"
    and no_service: "\<And>i. ordinary_commit_id (step_outcome (events i)) \<noteq> Some (packet_identity p)"
    and cases: "finite K"
  shows "\<exists>j\<ge>start_index. used_priority_slot (events j) \<and> \<not> budgeted_priority K (events j)"
proof (rule ccontr)
  assume "\<not> (\<exists>j\<ge>start_index. used_priority_slot (events j) \<and> \<not> budgeted_priority K (events j))"
  then have suffix: "\<And>j. start_index \<le> j \<Longrightarrow> budgeted_priority K (events j)"
    by (auto simp: budgeted_priority_def)
  from finite_priority_on_an_eventually_budgeted_scoped_run[OF trace cases suffix]
  have finite: "finite {i. priority_commit (step_outcome (events i))}" by (simp add: used_priority_slot_def)
  have completed: "\<exists>j. ordinary_commit_id (step_outcome (events j)) = Some (packet_identity p)
      \<and> ordinary_receipts (scheduler_at (target_state (events j))) (packet_identity p) = Some p"
  proof (rule an_exact_ordinary_packet_completes_in_the_scoped_run[OF trace coherent pending finite, where offered=offered])
    fix i
    assume waiting: "\<And>j. i \<le> j \<Longrightarrow> ordinary_queue (scheduler_at (source_state (events j))) \<noteq> []"
    show "\<exists>j\<ge>i. receives_fresh_choice E (offered j) (events j)" by (rule opportunity[OF waiting])
  qed
  with no_service show False by blast
qed

corollary fixed_case_starvation_with_current_opportunities_requires_recurring_real_lowers:
  assumes trace: "infinite_run (machine_step E) initial carrier events"
    and coherent: "coherent_ordinary_queue (scheduler_at (source_state (events 0)))"
    and pending: "p \<in> set (ordinary_queue (scheduler_at (source_state (events 0))))"
    and opportunity: "\<And>i. (\<And>j. i \<le> j \<Longrightarrow>
      ordinary_queue (scheduler_at (source_state (events j))) \<noteq> []) \<Longrightarrow>
      \<exists>j\<ge>i. receives_fresh_choice E (offered j) (events j)"
    and no_service: "\<And>i. ordinary_commit_id (step_outcome (events i)) \<noteq> Some (packet_identity p)"
    and cases: "finite K"
    and closed: "\<And>i expected turn q. used_priority_slot (events i) \<Longrightarrow>
       step_action (events i) = Attempt_At expected turn q \<Longrightarrow> regulatory_case (packet_contents q) \<in> K"
  shows "\<exists>i\<ge>start_index. used_priority_slot (events i) \<and>
     (\<exists>expected turn q k level. step_action (events i) = Attempt_At expected turn q \<and>
         packet_contents q = Lower_Level k level)"
proof -
  from starvation_requires_priority_outside_every_finite_case_budget_on_every_tail[OF trace coherent pending opportunity no_service cases]
  obtain i where index: "start_index \<le> i" and used: "used_priority_slot (events i)"
    and escaped: "\<not> budgeted_priority K (events i)" by blast
  let ?e = "events i"
  let ?d = "source_state ?e"
  let ?t = "target_state ?e"
  from used obtain q k where label:
    "step_outcome ?e = Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Regulation q k))))"
    by (auto simp: used_priority_slot_def priority_commit_def)
  from trace have occurred: "step_occurs (machine_step E) ?e" by (simp add: infinite_run_def)
  from occurred label have happened:
    "machine_step E ?d (step_action ?e) (Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Regulation q k))))) ?t"
    by (simp add: step_occurs_def)
  obtain expected turn packet where selected: "step_action ?e = Attempt_At expected turn packet"
    by (rule a_service_observation_has_an_attempt[OF happened]) (rule that; assumption)
  with happened have attempt:
    "machine_step E ?d (Attempt_At expected turn packet)
      (Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Regulation q k))))) ?t"
    by simp
  from service_trace_consumes_checked_compare(1)[OF attempt] have observation:
    "observe_sequence (authority_facts E) (active_signer E) (order_at ?d) (retained_answer ?d)
      expected (committed_cut ?d) turn packet =
      (Compared_Attempt (Service_Result (Internal (Served_Regulation q k))),scheduler_at ?t)"
    by simp
  obtain u where effect:
    "regulatory_effect (authorized_view (authority_facts E) (scheduler_at ?d)) packet = Some u"
    by (rule scoped_regulatory_effect[OF compare_commit_uses_the_exact_current_order(4)[OF observation]])
      (rule that; assumption)
  have member: "regulatory_case (packet_contents packet) \<in> K" by (rule closed[OF used selected])
  from member selected escaped effect have "\<exists>k' level. packet_contents packet = Lower_Level k' level"
    by (cases "packet_contents packet") (auto simp: budgeted_priority_def regulatory_effect_def split: if_splits)
  with index used selected show ?thesis by blast
qed

end
