theory Scoped_Counting
  imports Scoped_Ordinary
begin

definition used_ordinary_slot :: "machine_event \<Rightarrow> bool" where
  "used_ordinary_slot e \<longleftrightarrow> ordinary_commit_id (step_outcome e) \<noteq> None"

definition used_priority_slot :: "machine_event \<Rightarrow> bool" where
  "used_priority_slot e \<longleftrightarrow> priority_commit (step_outcome e)"

definition used_service_slot :: "machine_event \<Rightarrow> bool" where
  "used_service_slot e \<longleftrightarrow> used_ordinary_slot e \<or> used_priority_slot e"

lemma the_two_service_charges_are_disjoint:
  assumes "used_priority_slot e"
  shows "\<not> used_ordinary_slot e"
  using assms by (auto simp: used_priority_slot_def used_ordinary_slot_def priority_commit_def)

lemma actual_service_slots_partition:
  "length (filter used_service_slot es) =
    length (filter used_ordinary_slot es) + length (filter used_priority_slot es)"
  by (induction es) (auto simp: used_service_slot_def dest: the_two_service_charges_are_disjoint)

lemma a_slot_before_this_request_decreases_its_fifo_rank:
  assumes step: "machine_step E d action reply t"
    and queued: "waiting q (scheduler_at d)" and other: "ordinary_commit_id reply \<noteq> Some q"
  shows "waiting q (scheduler_at t)"
    and "earlier_ordinary q (scheduler_at t) + (if ordinary_commit_id reply = None then 0 else 1)
       \<le> earlier_ordinary q (scheduler_at d)"
proof -
  obtain u v act out where
    before: "fifo_observation u = fifo_observation (scheduler_at d)"
    and after: "fifo_observation v = fifo_observation (scheduler_at t)"
    and model: "scheduler_step u act out v"
    and effect: "ordinary_commit_id reply = raw_ordinary_effect act out"
    by (rule scoped_ordinary_step_has_a_raw_fifo_witness[OF step]) (rule that; assumption)
  let ?e = "\<lparr>source_state = u, step_action = act, step_outcome = out, target_state = v\<rparr>"
  from model have occurs: "step_occurs scheduler_step ?e" by (simp add: step_occurs_def)
  from queued fifo_observation_preserves_lane_predicates(8)[OF before] have pending: "waiting q u" by simp
  from other effect have not_done: "\<not> served_ordinary q ?e" by (simp add: served_ordinary_def raw_service_id)
  from waiting_persists_without_its_service[OF occurs] pending not_done
    fifo_observation_preserves_lane_predicates(8)[OF after] show "waiting q (scheduler_at t)" by simp
  show "earlier_ordinary q (scheduler_at t) + (if ordinary_commit_id reply = None then 0 else 1)
       \<le> earlier_ordinary q (scheduler_at d)"
  proof (cases "ordinary_commit_id reply")
    case None
    with waiting_rank_nonincreasing[OF occurs] pending not_done
      fifo_observation_preserves_lane_predicates(7)[OF before]
      fifo_observation_preserves_lane_predicates(7)[OF after]
    show ?thesis by (simp add: rank_nonincreasing_def)
  next
    case (Some i)
    with effect have observed: "raw_ordinary_effect act out = Some i" by simp
    from iffD1[OF raw_service_id observed] Some other
    have iso: "act = Honest_Service" "out = Internal (Served_Ordinary i)" "i \<noteq> q" by simp_all
    from serving_an_earlier_ordinary_packet_decreases_rank[OF occurs] pending iso
    have "earlier_ordinary q v < earlier_ordinary q u"
      by (auto simp: rank_decreases_def)
    with Some fifo_observation_preserves_lane_predicates(7)[OF before]
      fifo_observation_preserves_lane_predicates(7)[OF after]
    show ?thesis by simp
  qed
qed

lemma a_prefix_without_the_target_cannot_exceed_its_ordinary_rank:
  assumes trace: "finite_trace (machine_step E) carrier d es t"
    and waiting: "waiting q (scheduler_at d)"
    and no_target: "\<And>e. e \<in> set es \<Longrightarrow> ordinary_commit_id (step_outcome e) \<noteq> Some q"
  shows "earlier_ordinary q (scheduler_at t) + length (filter used_ordinary_slot es)
    \<le> earlier_ordinary q (scheduler_at d)"
  using trace waiting no_target
proof (induction es arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  from Cons.prems obtain
    step: "machine_step E d (step_action e) (step_outcome e) (target_state e)"
    and more: "finite_trace (machine_step E) carrier (target_state e) es t"
    and other: "ordinary_commit_id (step_outcome e) \<noteq> Some q"
    by (auto simp: step_occurs_def)
  from a_slot_before_this_request_decreases_its_fifo_rank[OF step Cons.prems(2) other]
  have wait: "waiting q (scheduler_at (target_state e))"
    and raw_rank: "earlier_ordinary q (scheduler_at (target_state e)) +
      (if ordinary_commit_id (step_outcome e) = None then 0 else 1) \<le> earlier_ordinary q (scheduler_at d)"
    by simp_all
  have rank: "earlier_ordinary q (scheduler_at (target_state e)) +
      (if used_ordinary_slot e then 1 else 0) \<le> earlier_ordinary q (scheduler_at d)"
    using raw_rank by (cases "ordinary_commit_id (step_outcome e)") (simp_all add: used_ordinary_slot_def)
  from Cons.IH[OF more wait] Cons.prems(3) have tail:
    "earlier_ordinary q (scheduler_at t) + length (filter used_ordinary_slot es)
      \<le> earlier_ordinary q (scheduler_at (target_state e))" by simp
  from rank tail show ?case by (cases "used_ordinary_slot e") auto
qed

lemma first_matching_commit_records_the_original_pending_packet:
  assumes trace: "finite_trace (machine_step E) carrier d es t"
    and coherent: "coherent_ordinary_queue (scheduler_at d)"
    and pending: "p \<in> set (ordinary_queue (scheduler_at d))"
    and hit: "\<exists>e \<in> set es. ordinary_commit_id (step_outcome e) = Some (packet_identity p)"
  shows "\<exists>e \<in> set es. ordinary_commit_id (step_outcome e) = Some (packet_identity p)
    \<and> ordinary_receipts (scheduler_at (target_state e)) (packet_identity p) = Some p"
  using assms
proof (induction es arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  let ?q = "packet_identity p"
  from Cons.prems have origin: "source_state e = d" and step:
    "machine_step E d (step_action e) (step_outcome e) (target_state e)"
    and tail: "finite_trace (machine_step E) carrier (target_state e) es t"
    by (auto simp: step_occurs_def)
  show ?case
  proof (cases "ordinary_commit_id (step_outcome e) = Some ?q")
    case True
    from scoped_execution_writes_the_packet_that_was_served[OF step True] obtain h rest where
      head: "ordinary_queue (scheduler_at d) = h # rest"
      and id: "packet_identity h = ?q"
      and receipt: "ordinary_receipts (scheduler_at (target_state e)) ?q = Some h" by blast
    from Cons.prems(2,3) head id have "h = p"
      by (auto simp: coherent_ordinary_queue_def)
    with True receipt show ?thesis by (intro bexI[of _ e]) simp_all
  next
    case False
    from Cons.prems(2,3) have blank: "ordinary_receipts (scheduler_at d) ?q \<noteq> Some p"
      by (auto simp: coherent_ordinary_queue_def ordinary_ids_def dom_def)
    from scoped_responsibility_survives[OF step Cons.prems(2)] Cons.prems(3)
      new_scoped_receipt_requires_an_actual_commit[OF step blank] False
    have waiting: "p \<in> set (ordinary_queue (scheduler_at (target_state e)))" by blast
    with scoped_fifo_maintains_coherence[OF step Cons.prems(2)] False Cons.prems(4) Cons.IH[OF tail]
    show ?thesis by auto
  qed
qed

theorem scoped_request_is_served_by_its_fifo_rank_plus_actual_interference:
  assumes trace: "finite_trace (machine_step E) carrier d es t"
    and coherent: "coherent_ordinary_queue (scheduler_at d)"
    and pending: "p \<in> set (ordinary_queue (scheduler_at d))"
    and budget: "length (filter used_priority_slot es) \<le> B"
    and sufficient: "earlier_ordinary (packet_identity p) (scheduler_at d) + B < length (filter used_service_slot es)"
  shows "\<exists>e \<in> set es. ordinary_commit_id (step_outcome e) = Some (packet_identity p)
    \<and> ordinary_receipts (scheduler_at (target_state e)) (packet_identity p) = Some p"
proof -
  let ?q = "packet_identity p"
  from pending have waiting: "waiting ?q (scheduler_at d)" by (auto simp: waiting_def)
  have hit: "\<exists>e \<in> set es. ordinary_commit_id (step_outcome e) = Some ?q"
  proof (rule ccontr)
    assume absent: "\<not> (\<exists>e \<in> set es. ordinary_commit_id (step_outcome e) = Some ?q)"
    from absent have no_target: "\<And>e. e \<in> set es \<Longrightarrow> ordinary_commit_id (step_outcome e) \<noteq> Some ?q"
      by blast
    from a_prefix_without_the_target_cannot_exceed_its_ordinary_rank[OF trace waiting no_target]
      actual_service_slots_partition[of es] budget sufficient show False by linarith
  qed
  from hit show ?thesis
    by (rule first_matching_commit_records_the_original_pending_packet[OF trace coherent pending])
qed

end
