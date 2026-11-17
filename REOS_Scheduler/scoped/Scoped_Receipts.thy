theory Scoped_Receipts
  imports Scoped_Order_Safety Scoped_Ordinary
begin

lemma each_event_in_a_machine_trace_occurs:
  assumes "finite_trace (machine_step E) carrier d es t" "e \<in> set es"
  shows "step_occurs (machine_step E) e"
  using assms by (induction es arbitrary: d) auto

lemma a_service_observation_has_an_attempt:
  assumes "machine_step E d action (Observed_Service obs) t"
  obtains expected turn p where "action = Attempt_At expected turn p"
  using assms by (cases action)
    (auto simp: machine_step_def Let_def split: prod.splits transition_result.splits
      rollback_internal.splits option.splits if_splits)

lemma a_committed_ordinary_receipt_names_the_certified_order_in_that_step:
  assumes occurrence: "step_occurs (machine_step E) e"
    and completed: "ordinary_commit_id (step_outcome e) = Some (packet_identity p)"
    and saved: "ordinary_receipts (scheduler_at (target_state e)) (packet_identity p) = Some p"
  obtains turn where
    "step_action e = Attempt_At (committed_cut (source_state e)) turn p"
    "(turn,p) \<in> certified_order_pairs E"
    "run_machine E (target_state e) (Attempt_At retry_cut turn p) =
      (Observed_Service (Replayed_Receipt p),target_state e)"
proof -
  let ?obs = "Compared_Attempt (Service_Result (Internal (Served_Ordinary (packet_identity p))))"
  let ?d = "source_state e"
  let ?t = "target_state e"
  from completed have reply: "step_outcome e = Observed_Service ?obs"
    by (cases "step_outcome e" rule: ordinary_commit_id.cases) auto
  from occurrence reply have "machine_step E ?d (step_action e) (Observed_Service ?obs) ?t"
    by (simp add: step_occurs_def)
  then obtain expected turn q where event: "step_action e = Attempt_At expected turn q"
    by (elim a_service_observation_has_an_attempt) assumption
  from event occurrence reply have step:
    "machine_step E ?d (Attempt_At expected turn q) (Observed_Service ?obs) ?t"
    by (simp add: step_occurs_def)
  have wrote: "committed_service ?obs" by simp
  from service_trace_consumes_checked_compare(1)[OF step wrote] have checked:
    "observe_sequence (authority_facts E) (active_signer E) (order_at ?d) (retained_answer ?d)
      expected (committed_cut ?d) turn q = (?obs,scheduler_at ?t)" .
  note commit = compare_commit_uses_the_exact_current_order[OF checked]
  obtain rest where ident: "packet_identity p = packet_identity q"
    and target: "scheduler_at ?t = (scheduler_at ?d)\<lparr>ordinary_queue := rest,
      ordinary_receipts := (ordinary_receipts (scheduler_at ?d))(packet_identity p \<mapsto> q)\<rparr>"
    by (rule scoped_ordinary_effect[OF commit(4)]) (rule that; assumption)
  from target saved have q: "q = p" by simp
  from event commit(1) q have action:
    "step_action e = Attempt_At (committed_cut ?d) turn p" by simp
  from service_commit_uses_an_attested_current_order_and_replays_at_the_next_read(1,3)[OF step wrote] q
  have signed: "(turn,p) \<in> certified_order_pairs E"
    and replay: "run_machine E ?t (Attempt_At retry_cut turn p) = (Observed_Service (Replayed_Receipt p),?t)"
    by simp_all
  show thesis by (rule that[OF action signed replay])
qed

theorem actual_scoped_progress_returns_the_original_order_and_its_retry:
  assumes trace: "infinite_run (machine_step E) initial carrier events"
    and shaped: "coherent_ordinary_queue (scheduler_at (source_state (events 0)))"
    and pending: "p \<in> set (ordinary_queue (scheduler_at (source_state (events 0))))"
    and finite_priority: "finite {i. priority_commit (step_outcome (events i))}"
    and opportunity: "\<And>i. (\<And>j. i \<le> j \<Longrightarrow>
      ordinary_queue (scheduler_at (source_state (events j))) \<noteq> []) \<Longrightarrow>
      \<exists>j\<ge>i. receives_fresh_choice E (offered j) (events j)"
  obtains j turn where
    "step_action (events j) = Attempt_At (committed_cut (source_state (events j))) turn p"
    "(turn,p) \<in> certified_order_pairs E"
    "ordinary_commit_id (step_outcome (events j)) = Some (packet_identity p)"
    "ordinary_receipts (scheduler_at (target_state (events j))) (packet_identity p) = Some p"
    "run_machine E (target_state (events j)) (Attempt_At retry_cut turn p) =
      (Observed_Service (Replayed_Receipt p),target_state (events j))"
proof -
  from an_exact_ordinary_packet_completes_in_the_scoped_run[OF trace shaped pending finite_priority opportunity]
  obtain j where committed: "ordinary_commit_id (step_outcome (events j)) = Some (packet_identity p)"
    and saved: "ordinary_receipts (scheduler_at (target_state (events j))) (packet_identity p) = Some p"
    by blast
  from trace have step: "step_occurs (machine_step E) (events j)" by (simp add: infinite_run_def)
  obtain turn where explicit: "step_action (events j) = Attempt_At (committed_cut (source_state (events j))) turn p"
    and signed: "(turn,p) \<in> certified_order_pairs E"
    and replay: "run_machine E (target_state (events j)) (Attempt_At retry_cut turn p) =
      (Observed_Service (Replayed_Receipt p),target_state (events j))"
    by (rule a_committed_ordinary_receipt_names_the_certified_order_in_that_step[OF step committed saved])
      (rule that; assumption)
  show thesis by (rule that[OF explicit signed committed saved replay])
qed

theorem the_same_certified_rollback_preserves_scope_at_commit_and_retry:
  assumes step: "machine_step E d (Attempt_At expected turn p)
    (Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Regulation q k))))) t"
    and body: "packet_contents p = Execute_Governed_Rollback request approval role_proof"
  shows "(turn,p) \<in> certified_order_pairs E \<and> expected = committed_cut d"
    "requested_role request = Governance \<or> verified_origin (authority_facts E) request = Some Regulatory_Review
       \<Longrightarrow> request \<in> collective_decisions (authority_facts E)"
    "request_scope request = Wide \<Longrightarrow>
      matches_certificate (rollback_context (scheduler_at d)) request Governance_Ratification Governance approval"
    "\<exists>previous. journal (rollback_context (scheduler_at d)) (undo_entry request) = Some previous
       \<and> request_authority_epoch request = authority_epoch (rollback_context (scheduler_at d))
       \<and> k = entry_case previous
       \<and> (\<forall>c \<in> footprint request. cell_value (rollback_context (scheduler_at t)) c = previous_value previous c)
       \<and> preserves_outside cell_value (footprint request)
         (rollback_context (scheduler_at d)) (rollback_context (scheduler_at t))"
    "run_machine E t (Attempt_At retry_cut turn p) = (Observed_Service (Replayed_Receipt p),t)"
proof -
  let ?obs = "Compared_Attempt (Service_Result (Internal (Served_Regulation q k)))"
  have committed: "committed_service ?obs" by simp
  note evidence = service_trace_consumes_checked_compare[OF step committed]
  note combined = committed_rollback_consumes_authority_frame_and_budget[OF evidence(1) body]
  show "(turn,p) \<in> certified_order_pairs E \<and> expected = committed_cut d"
    using evidence(3) compare_commit_uses_the_exact_current_order(1)[OF evidence(1)] by simp
  show "requested_role request = Governance \<or> verified_origin (authority_facts E) request = Some Regulatory_Review
       \<Longrightarrow> request \<in> collective_decisions (authority_facts E)"
    by (rule combined(3))
  show "request_scope request = Wide \<Longrightarrow>
      matches_certificate (rollback_context (scheduler_at d)) request Governance_Ratification Governance approval"
    by (rule combined(4))
  show "\<exists>previous. journal (rollback_context (scheduler_at d)) (undo_entry request) = Some previous
       \<and> request_authority_epoch request = authority_epoch (rollback_context (scheduler_at d))
       \<and> k = entry_case previous
       \<and> (\<forall>c \<in> footprint request. cell_value (rollback_context (scheduler_at t)) c = previous_value previous c)
       \<and> preserves_outside cell_value (footprint request)
         (rollback_context (scheduler_at d)) (rollback_context (scheduler_at t))"
    using combined(7) by blast
  show "run_machine E t (Attempt_At retry_cut turn p) = (Observed_Service (Replayed_Receipt p),t)"
    by (rule service_commit_uses_an_attested_current_order_and_replays_at_the_next_read(3)[OF step committed])
qed

end
