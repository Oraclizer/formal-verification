theory Fresh_Case_Interference
  imports REOS_Scheduler_Controls.Scheduler_Lasso
begin

text \<open>Every priority service in this trace raises a previously unused case.
The fixed-case bound requires a bound on all cases used along the run.
It does not follow from having only one pending regulatory packet at a time.\<close>

definition fresh_packet :: "nat \<Rightarrow> packet" where
  "fresh_packet n = urgent_packet\<lparr>packet_identity := 102+n,
    packet_contents := Raise_Level (9+n) 1\<rparr>"

definition fresh_log :: "nat \<Rightarrow> nat \<Rightarrow> packet option" where
  "fresh_log n j = (if 102 \<le> j \<and> j < 102+n then Some (fresh_packet (j-102)) else None)"

lemma fresh_log_step:
  "fresh_log (Suc n) = (fresh_log n)(102+n \<mapsto> fresh_packet n)"
proof (rule ext)
  fix j
  show "fresh_log (Suc n) j = ((fresh_log n)(102+n \<mapsto> fresh_packet n)) j"
  proof (cases "j = 102+n")
    case True
    then show ?thesis by (simp add: fresh_log_def)
  next
    case False
    then have "(j < 102 + Suc n) = (j < 102+n)" by linarith
    with False show ?thesis by (simp add: fresh_log_def)
  qed
qed

definition fresh_levels :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fresh_levels n k = (if 9 \<le> k \<and> k < 9+n then 1 else 0)"

lemma fresh_level_step:
  "fresh_levels (Suc n) = (fresh_levels n)(9+n := 1)"
proof (rule ext)
  fix k
  show "fresh_levels (Suc n) k = ((fresh_levels n)(9+n := 1)) k"
  proof (cases "k = 9+n")
    case True
    then show ?thesis by (simp add: fresh_levels_def)
  next
    case False
    then have "(k < 9 + Suc n) = (k < 9+n)" by linarith
    with False show ?thesis by (simp add: fresh_levels_def)
  qed
qed

definition fresh_initial :: scheduler_state where
  "fresh_initial = scheduler_example\<lparr>signed_packets := insert ordinary_packet (range fresh_packet),
    regulatory_grants := range fresh_packet\<rparr>"

definition fresh_state :: "nat \<Rightarrow> scheduler_state" where
  "fresh_state n = fresh_initial\<lparr>ordinary_queue := [ordinary_packet],
    dedup_ids := {101..101+n}, regulation_receipts := fresh_log n,
    severity_now := fresh_levels n\<rparr>"

definition fresh_pending :: "nat \<Rightarrow> scheduler_state" where
  "fresh_pending n = enqueue_packet (fresh_state n) (fresh_packet n)"

lemma initial_ordinary_is_really_admitted_in_fresh_case_trace:
  "scheduler_step fresh_initial (Submit ordinary_packet) (Accepted 101) (fresh_state 0)"
  by (simp add: scheduler_reduction fresh_initial_def fresh_state_def
      fresh_log_def fresh_levels_def packet_example fun_eq_iff)

lemma fresh_case_submitted:
  "scheduler_step (fresh_state n) (Submit (fresh_packet n)) (Accepted (102+n)) (fresh_pending n)"
proof -
  have "fresh_packet n \<in> range fresh_packet" by (rule rangeI)
  then show ?thesis
    by (simp add: fresh_state_def fresh_initial_def fresh_packet_def fresh_levels_def
        scheduler_reduction packet_example fresh_pending_def)
qed

lemma fresh_case_actually_served:
  "scheduler_step (fresh_pending n) Honest_Service
    (Internal (Served_Regulation (102+n) (9+n))) (fresh_state (Suc n))"
proof -
  have "fresh_packet n \<in> range fresh_packet" by (rule rangeI)
  then show ?thesis
    by (simp add: fresh_state_def fresh_initial_def fresh_packet_def
        fresh_pending_def fresh_log_step fresh_level_step cycle_checked_ids
        scheduler_reduction packet_example fresh_levels_def fun_eq_iff)
qed

definition fresh_event :: "nat \<Rightarrow> (scheduler_state,scheduler_action,scheduler_result) transition" where
  "fresh_event i = (let n = i div 2 in
    if even i then \<lparr>source_state = fresh_state n, step_action = Submit (fresh_packet n),
      step_outcome = Accepted (102+n), target_state = fresh_pending n\<rparr>
    else \<lparr>source_state = fresh_pending n, step_action = Honest_Service,
      step_outcome = Internal (Served_Regulation (102+n) (9+n)), target_state = fresh_state (Suc n)\<rparr>)"

lemma fresh_event_happens:
  "step_occurs scheduler_step (fresh_event i)"
  using fresh_case_submitted[of "i div 2"] fresh_case_actually_served[of "i div 2"]
  by (cases "even i") (simp_all add: fresh_event_def Let_def step_occurs_def)

lemma fresh_event_links:
  "target_state (fresh_event i) = source_state (fresh_event (Suc i))"
proof (cases "even i")
  case True
  then have "Suc i div 2 = i div 2" by presburger
  with True show ?thesis by (simp add: fresh_event_def Let_def)
next
  case False
  then have "Suc i div 2 = Suc (i div 2)" by presburger
  with False show ?thesis by (simp add: fresh_event_def Let_def)
qed

theorem recurring_honest_slots_can_be_spent_on_fresh_cases:
  "infinite_run scheduler_step {fresh_state 0} UNIV fresh_event"
  "\<And>i. \<exists>j\<ge>i. step_action (fresh_event j) = Honest_Service"
  "\<And>i. waiting 101 (source_state (fresh_event i)) \<and> \<not> served_ordinary 101 (fresh_event i)"
  "\<And>i k. severity_now (source_state (fresh_event i)) k \<le> severity_now (target_state (fresh_event i)) k"
proof -
  show "infinite_run scheduler_step {fresh_state 0} UNIV fresh_event"
    using fresh_event_happens fresh_event_links
    by (simp add: infinite_run_def) (simp add: fresh_event_def Let_def)
  fix i k
  show "\<exists>j\<ge>i. step_action (fresh_event j) = Honest_Service"
  proof (cases "even i")
    case True
    show ?thesis by (intro exI[of _ "Suc i"]) (simp add: fresh_event_def Let_def True)
  next
    case False
    show ?thesis by (intro exI[of _ i]) (simp add: fresh_event_def Let_def False)
  qed
  show "waiting 101 (source_state (fresh_event i)) \<and> \<not> served_ordinary 101 (fresh_event i)"
    by (cases "even i")
       (simp_all add: fresh_event_def Let_def fresh_state_def fresh_initial_def fresh_pending_def
           fresh_packet_def served_ordinary_def scheduler_reduction packet_example)
  show "severity_now (source_state (fresh_event i)) k \<le> severity_now (target_state (fresh_event i)) k"
    by (cases "even i")
       (auto simp: fresh_event_def Let_def fresh_state_def fresh_initial_def fresh_pending_def
         fresh_packet_def enqueue_packet_def fresh_levels_def)
qed

end
