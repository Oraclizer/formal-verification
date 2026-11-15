theory Scheduler_Lasso
  imports Scheduler_Examples
begin

section \<open>Genuine admission and service in the de-escalation cycle\<close>

definition cycle_packet :: "nat \<Rightarrow> packet"
where
  "cycle_packet n = urgent_packet\<lparr>packet_identity := 102+n,
    packet_contents := (if even n then Raise_Level 9 1 else Lower_Level 9 0)\<rparr>"

definition cycle_log :: "nat \<Rightarrow> nat \<Rightarrow> packet option"
where
  "cycle_log n j = (if 102 \<le> j \<and> j < 102+n then Some (cycle_packet (j-102)) else None)"

lemma cycle_log_add:
  "cycle_log (Suc n) = (cycle_log n)(102+n \<mapsto> cycle_packet n)"
proof (rule ext)
  fix j
  show "cycle_log (Suc n) j = ((cycle_log n)(102+n \<mapsto> cycle_packet n)) j"
  proof (cases "j = 102+n")
    case True
    then show ?thesis by (simp add: cycle_log_def)
  next
    case False
    then have "(j < 102 + Suc n) = (j < 102+n)" by linarith
    with False show ?thesis by (simp add: cycle_log_def)
  qed
qed

lemma cycle_checked_ids:
  "insert (102+n) {101..101+n} = {101..101+Suc n}"
  by (auto; linarith)

definition cycle_state :: "nat \<Rightarrow> scheduler_state"
where
  "cycle_state n = scheduler_example\<lparr>
    signed_packets := insert ordinary_packet (range cycle_packet),
    regulatory_grants := range cycle_packet, ordinary_queue := [ordinary_packet],
    dedup_ids := {101..101+n},
    regulation_receipts := cycle_log n,
    severity_now := (\<lambda>k. if k = 9 \<and> odd n then 1 else 0)\<rparr>"

definition cycle_queued :: "nat \<Rightarrow> scheduler_state"
where
  "cycle_queued n = enqueue_packet (cycle_state n) (cycle_packet n)"

lemma cycle_allows_actual_new_packet:
  "scheduler_step (cycle_state n) (Submit (cycle_packet n)) (Accepted (102+n)) (cycle_queued n)"
proof -
  have "cycle_packet n \<in> range cycle_packet" by (rule rangeI)
  then show ?thesis by (cases "even n")
    (simp_all add: cycle_state_def cycle_packet_def scheduler_reduction packet_example cycle_queued_def)
qed

lemma cycle_consumes_actual_priority_packet:
  "scheduler_step (cycle_queued n) Honest_Service (Internal (Served_Regulation (102+n) 9)) (cycle_state (Suc n))"
proof -
  have "cycle_packet n \<in> range cycle_packet" by (rule rangeI)
  then show ?thesis by (cases "even n")
    (simp_all add: cycle_state_def cycle_packet_def scheduler_reduction packet_example
      cycle_queued_def cycle_log_add cycle_checked_ids fun_eq_iff)
qed

definition cycle_event ::
  "nat \<Rightarrow> (scheduler_state,scheduler_action,scheduler_result) transition"
where
  "cycle_event i = (let n = i div 2 in
      if even i
      then \<lparr>source_state = cycle_state n, step_action = Submit (cycle_packet n),
        step_outcome = Accepted (102+n), target_state = cycle_queued n\<rparr>
      else \<lparr>source_state = cycle_queued n, step_action = Honest_Service,
        step_outcome = Internal (Served_Regulation (102+n) 9), target_state = cycle_state (Suc n)\<rparr>)"

lemma cycle_transition_happens:
  "step_occurs scheduler_step (cycle_event i)"
  using cycle_allows_actual_new_packet[of "i div 2"] cycle_consumes_actual_priority_packet[of "i div 2"]
  by (cases "even i") (simp_all add: cycle_event_def Let_def step_occurs_def)

lemma cycle_transitions_link:
  "target_state (cycle_event i) = source_state (cycle_event (Suc i))"
proof (cases "even i")
  case True
  then have "Suc i div 2 = i div 2" by presburger
  with True show ?thesis by (simp add: cycle_event_def Let_def)
next
  case False
  then have "Suc i div 2 = Suc (i div 2)" by presburger
  with False show ?thesis by (simp add: cycle_event_def Let_def)
qed

theorem repeated_legal_de_escalation_starves_the_pending_ordinary_packet:
  "infinite_run scheduler_step {cycle_state 0} UNIV cycle_event"
  "\<And>i. \<exists>j\<ge>i. step_action (cycle_event j) = Honest_Service"
  "\<And>i. waiting 101 (source_state (cycle_event i)) \<and> \<not> served_ordinary 101 (cycle_event i)"
proof -
  show "infinite_run scheduler_step {cycle_state 0} UNIV cycle_event"
    using cycle_transition_happens cycle_transitions_link
    by (simp add: infinite_run_def) (simp add: cycle_event_def Let_def)
  fix i
  show "\<exists>j\<ge>i. step_action (cycle_event j) = Honest_Service"
  proof (cases "even i")
    case True
    show ?thesis by (intro exI[of _ "Suc i"]) (simp add: cycle_event_def Let_def True)
  next
    case False
    show ?thesis by (intro exI[of _ i]) (simp add: cycle_event_def Let_def False)
  qed
  show "waiting 101 (source_state (cycle_event i)) \<and> \<not> served_ordinary 101 (cycle_event i)"
    by (cases "even i")
      (simp_all add: cycle_event_def Let_def cycle_state_def cycle_queued_def cycle_packet_def
        served_ordinary_def scheduler_reduction packet_example)
qed

end
