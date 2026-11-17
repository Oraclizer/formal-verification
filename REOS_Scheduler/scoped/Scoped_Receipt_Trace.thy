theory Scoped_Receipt_Trace
  imports Scoped_Receipts
begin

lemma a_commit_modifies_only_its_own_receipt_and_answer:
  assumes step: "machine_step E d (Attempt_At expected turn p) (Observed_Service obs) t"
    and wrote: "committed_service obs"
  shows "q \<noteq> packet_identity p \<Longrightarrow>
    ordinary_receipts (scheduler_at t) q = ordinary_receipts (scheduler_at d) q \<and>
    regulation_receipts (scheduler_at t) q = regulation_receipts (scheduler_at d) q"
    "other \<noteq> turn \<Longrightarrow> answer_at t other = answer_at d other"
proof -
  show "q \<noteq> packet_identity p \<Longrightarrow>
    ordinary_receipts (scheduler_at t) q = ordinary_receipts (scheduler_at d) q \<and>
    regulation_receipts (scheduler_at t) q = regulation_receipts (scheduler_at d) q"
  proof -
  assume different: "q \<noteq> packet_identity p"
  from wrote have cases:
    "(\<exists>j. obs = Compared_Attempt (Service_Result (Internal (Served_Ordinary j)))) \<or>
     (\<exists>j k. obs = Compared_Attempt (Service_Result (Internal (Served_Regulation j k))))"
    by (simp add: committed_service_replies)
  from cases show "ordinary_receipts (scheduler_at t) q = ordinary_receipts (scheduler_at d) q \<and>
    regulation_receipts (scheduler_at t) q = regulation_receipts (scheduler_at d) q"
  proof
    assume "\<exists>j. obs = Compared_Attempt (Service_Result (Internal (Served_Ordinary j)))"
    then obtain j where obs: "obs = Compared_Attempt (Service_Result (Internal (Served_Ordinary j)))" by blast
    from service_trace_consumes_checked_compare(1)[OF step wrote] obs have observation:
      "observe_sequence (authority_facts E) (active_signer E) (order_at d) (retained_answer d)
         expected (committed_cut d) turn p =
         (Compared_Attempt (Service_Result (Internal (Served_Ordinary j))),scheduler_at t)" by simp
    obtain rest where id: "j = packet_identity p"
      and after: "scheduler_at t = (scheduler_at d)\<lparr>ordinary_queue := rest,
            ordinary_receipts := (ordinary_receipts (scheduler_at d))(j \<mapsto> p)\<rparr>"
      by (rule scoped_ordinary_effect[OF compare_commit_uses_the_exact_current_order(4)[OF observation]])
        (rule that; assumption)
    from after different id show ?thesis by simp
  next
    assume "\<exists>j k. obs = Compared_Attempt (Service_Result (Internal (Served_Regulation j k)))"
    then obtain j k where obs: "obs = Compared_Attempt (Service_Result (Internal (Served_Regulation j k)))" by blast
    from service_trace_consumes_checked_compare(1)[OF step wrote] obs have observation:
      "observe_sequence (authority_facts E) (active_signer E) (order_at d) (retained_answer d)
         expected (committed_cut d) turn p =
         (Compared_Attempt (Service_Result (Internal (Served_Regulation j k))),scheduler_at t)" by simp
    let ?view = "authorized_view (authority_facts E) (scheduler_at d)"
    note executed = compare_commit_uses_the_exact_current_order(4)[OF observation]
    obtain u where id: "j = packet_identity p"
      and effect: "regulatory_effect ?view p = Some u"
      and post: "scheduler_at t = u\<lparr>regulatory_queue := remove1 p (regulatory_queue (scheduler_at d)),
           regulation_receipts := (regulation_receipts ?view)(j \<mapsto> p)\<rparr>"
      by (rule scoped_regulatory_effect[OF executed]) (rule that; assumption)
    from id post different every_regulatory_effect_keeps_ordinary_responsibility(2)[OF effect]
    show ?thesis by (simp add: authorized_view_def)
  qed
  qed
  show "other \<noteq> turn \<Longrightarrow> answer_at t other = answer_at d other"
    using step wrote by (auto simp: machine_step_def split: if_splits prod.splits)
qed

lemma each_step_keeps_previously_stored_answers_and_receipts:
  assumes step: "machine_step E d action reply t"
  shows "answer_at d turn = Some p \<longrightarrow> answer_at t turn = Some p"
    and "ordinary_receipts (scheduler_at d) q = Some p \<longrightarrow>
      ordinary_receipts (scheduler_at t) q = Some p"
    and "regulation_receipts (scheduler_at d) q = Some p \<longrightarrow>
      regulation_receipts (scheduler_at t) q = Some p"
proof -
  have all:
    "(answer_at d turn = Some p \<longrightarrow> answer_at t turn = Some p) \<and>
     (ordinary_receipts (scheduler_at d) q = Some p \<longrightarrow> ordinary_receipts (scheduler_at t) q = Some p) \<and>
     (regulation_receipts (scheduler_at d) q = Some p \<longrightarrow> regulation_receipts (scheduler_at t) q = Some p)"
    using step
  proof (cases action)
    case (Attempt_At expected t' p')
    from step Attempt_At obtain obs where reply: "reply = Observed_Service obs"
      by (auto simp: machine_step_def split: if_splits prod.splits)
    from step Attempt_At reply have attempt:
      "machine_step E d (Attempt_At expected t' p') (Observed_Service obs) t" by simp
    show ?thesis
    proof (cases "committed_service obs")
      case False
      with service_attempt_without_a_commit_is_a_read[OF attempt] show ?thesis by simp
    next
      case True
      note fresh = an_actual_service_is_fresh_in_turn_and_request[OF attempt True]
      note frame = a_commit_modifies_only_its_own_receipt_and_answer[OF attempt True]
      from fresh frame show ?thesis by (cases "turn = t'"; cases "q = packet_identity p'"; simp)
    qed
  next
    case (Receive_Packet p')
    with step show ?thesis
      by (auto simp: machine_step_def write_scheduler_def scoped_submit_def admit_def enqueue_packet_def Let_def
        split: prod.splits if_splits transition_result.splits)
  qed (auto simp: machine_step_def write_scheduler_def retire_stale_def Let_def
        split: prod.splits if_splits transition_result.splits rollback_internal.splits option.splits)
  from all show "answer_at d turn = Some p \<longrightarrow> answer_at t turn = Some p"
    "ordinary_receipts (scheduler_at d) q = Some p \<longrightarrow> ordinary_receipts (scheduler_at t) q = Some p"
    "regulation_receipts (scheduler_at d) q = Some p \<longrightarrow> regulation_receipts (scheduler_at t) q = Some p"
    by simp_all
qed

theorem exact_committed_receipt_is_replayed_after_intervening_operations:
  assumes first: "machine_step E d (Attempt_At expected turn p) (Observed_Service obs) t"
    and commit: "committed_service obs"
    and suffix: "finite_trace (machine_step E) carrier t events final_state"
  shows "run_machine E final_state (Attempt_At retry_cut turn p) =
    (Observed_Service (Replayed_Receipt p),final_state)"
proof -
  from machine_receipt_carries_the_exact_committed_order[OF first commit] have
    order: "order_at t turn = Some p" and answer: "answer_at t turn = Some p"
    and saved: "exact_saved_packet (scheduler_at t) p" by simp_all
  have retained: "answer_at final_state turn = Some p \<and> exact_saved_packet (scheduler_at final_state) p"
    if trace: "finite_trace (machine_step E) carrier s es final_state"
    and known: "answer_at s turn = Some p" "exact_saved_packet (scheduler_at s) p" for s es
    using trace known
  proof (induction es arbitrary: s)
    case Nil
    then show ?case by simp
  next
    case (Cons e es)
    from Cons.prems have step: "machine_step E s (step_action e) (step_outcome e) (target_state e)"
      and tail: "finite_trace (machine_step E) carrier (target_state e) es final_state"
      by (auto simp: step_occurs_def)
    from each_step_keeps_previously_stored_answers_and_receipts(1)[OF step, where turn=turn and p=p] Cons.prems(2)
    have answer: "answer_at (target_state e) turn = Some p" by simp
    from each_step_keeps_previously_stored_answers_and_receipts(2,3)[OF step, where q="packet_identity p" and p=p]
      Cons.prems(3) have saved: "exact_saved_packet (scheduler_at (target_state e)) p"
      by (auto simp: exact_saved_packet_def split: if_splits)
    show ?case by (rule Cons.IH[OF tail answer saved])
  qed
  from retained[OF suffix answer saved] have keep_answer: "answer_at final_state turn = Some p"
    and keep_receipt: "exact_saved_packet (scheduler_at final_state) p" by simp_all
  from registered_order_is_immutable_along_the_trace[OF suffix order] have keep_order: "order_at final_state turn = Some p" .
  from service_trace_consumes_checked_compare(3)[OF first commit] show ?thesis
    by (rule previously_committed_order_has_exact_replay[OF _ keep_order keep_answer keep_receipt])
qed

end
