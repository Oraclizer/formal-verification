theory Scoped_Order_Safety
  imports Scoped_Machine
begin

lemma registered_order_is_immutable_along_the_trace:
  assumes trace: "finite_trace (machine_step E) carrier d events t"
    and known: "order_at d turn = Some p"
  shows "order_at t turn = Some p"
  using assms
proof (induction events arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  from Cons.prems have step: "machine_step E d (step_action e) (step_outcome e) (target_state e)"
    and more: "finite_trace (machine_step E) carrier (target_state e) es t"
    by (auto simp: step_occurs_def)
  from binding_persists_across_operations[OF step Cons.prems(2)] show ?case
    by (rule Cons.IH[OF more])
qed

lemma machine_receipt_carries_the_exact_committed_order:
  assumes step: "machine_step E d (Attempt_At expected turn p) (Observed_Service obs) t"
    and committed: "committed_service obs"
  shows "expected = committed_cut d"
    "qualified_turn (active_signer E) {turn} (scheduler_at d) turn"
    "order_at d turn = Some p" "order_at t turn = Some p" "answer_at t turn = Some p"
    "exact_saved_packet (scheduler_at t) p"
proof -
  from service_trace_consumes_checked_compare[OF step committed] have obs:
    "observe_sequence (authority_facts E) (active_signer E) (order_at d) (retained_answer d)
     expected (committed_cut d) turn p = (obs,scheduler_at t)"
    and answer: "answer_at t turn = Some p" by blast+
  from committed have actual:
    "(\<exists>q. obs = Compared_Attempt (Service_Result (Internal (Served_Ordinary q)))) \<or>
     (\<exists>q k. obs = Compared_Attempt (Service_Result (Internal (Served_Regulation q k))))"
    by (simp add: committed_service_replies)
  then obtain effect where eff: "obs = Compared_Attempt (Service_Result (Internal effect))" by blast
  from obs eff have consumed:
    "observe_sequence (authority_facts E) (active_signer E) (order_at d) (retained_answer d)
     expected (committed_cut d) turn p = (Compared_Attempt (Service_Result (Internal effect)),scheduler_at t)" by simp
  from compare_commit_uses_the_exact_current_order[OF consumed] have bound: "order_at d turn = Some p"
    and cut: "expected = committed_cut d"
    and signer: "qualified_turn (active_signer E) {turn} (scheduler_at d) turn"
    and service: "scoped_service (authority_facts E) (active_signer E) (signed_packets_by_turn (order_at d))
      (scheduler_at d) turn p = (Internal effect,scheduler_at t)" by blast+
  show "expected = committed_cut d" "qualified_turn (active_signer E) {turn} (scheduler_at d) turn"
    "order_at d turn = Some p" "order_at t turn = Some p" "answer_at t turn = Some p"
    using cut signer bound binding_persists_across_operations[OF step bound] answer by simp_all
  from actual eff have "(\<exists>q. effect = Served_Ordinary q) \<or> (\<exists>q k. effect = Served_Regulation q k)" by simp
  then show "exact_saved_packet (scheduler_at t) p"
  proof
    assume "\<exists>q. effect = Served_Ordinary q"
    with service obtain q where applied:
      "scoped_service (authority_facts E) (active_signer E) (signed_packets_by_turn (order_at d)) (scheduler_at d) turn p =
       (Internal (Served_Ordinary q),scheduler_at t)" by blast
    from scoped_ordinary_effect[OF applied] obtain rest where
      "ordinary_body (packet_contents p)" "q = packet_identity p"
      "scheduler_at t = (scheduler_at d)\<lparr>ordinary_queue := rest,
        ordinary_receipts := (ordinary_receipts (scheduler_at d))(q \<mapsto> p)\<rparr>"
      by blast
    then show ?thesis by (simp add: exact_saved_packet_def)
  next
    assume "\<exists>q k. effect = Served_Regulation q k"
    with service obtain q k where applied:
      "scoped_service (authority_facts E) (active_signer E) (signed_packets_by_turn (order_at d)) (scheduler_at d) turn p =
       (Internal (Served_Regulation q k),scheduler_at t)" by blast
    from scoped_regulatory_effect[OF applied] obtain u where
      effect_present: "regulatory_effect (authorized_view (authority_facts E) (scheduler_at d)) p = Some u"
      and identity: "q = packet_identity p" by blast
    from effect_present have "\<not> ordinary_body (packet_contents p)"
      by (cases "packet_contents p") (auto simp: regulatory_effect_def split: if_splits)
    with identity scoped_regulatory_commit_preserves_fifo(4)[OF applied]
    show ?thesis by (simp add: exact_saved_packet_def)
  qed
qed

theorem service_commit_uses_an_attested_current_order_and_replays_at_the_next_read:
  assumes step: "machine_step E d (Attempt_At expected turn p) (Observed_Service obs) t"
    and commit: "committed_service obs"
  shows "(turn,p) \<in> certified_order_pairs E"
    "store_cut (committed_cut t) = Suc (store_cut (committed_cut d))"
    "run_machine E t (Attempt_At any_expected turn p) = (Observed_Service (Replayed_Receipt p),t)"
    "q \<noteq> p \<Longrightarrow> run_machine E t (Bind_Order turn q) = (Refused_Order,t)"
proof -
  from service_trace_consumes_checked_compare(3)[OF step commit]
  show certified: "(turn,p) \<in> certified_order_pairs E" .
  from machine_receipt_carries_the_exact_committed_order[OF step commit]
  have order: "order_at t turn = Some p" and answer: "answer_at t turn = Some p"
    and receipt: "exact_saved_packet (scheduler_at t) p"
    by simp_all
  from step commit show "store_cut (committed_cut t) = Suc (store_cut (committed_cut d))"
    by (auto simp: machine_step_def split: prod.splits if_splits)
  show "run_machine E t (Attempt_At any_expected turn p) = (Observed_Service (Replayed_Receipt p),t)"
    by (rule previously_committed_order_has_exact_replay[OF certified order answer receipt])
  show "q \<noteq> p \<Longrightarrow> run_machine E t (Bind_Order turn q) = (Refused_Order,t)"
    by (rule an_existing_turn_rejects_a_different_body[OF order])
qed

end
