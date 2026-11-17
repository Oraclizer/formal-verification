theory Scoped_Starvation
  imports Scoped_Level_Boundaries Scoped_Ordinary
begin

locale scoped_priority_trace =
  fixes before :: "nat \<Rightarrow> scheduler_state" and queued :: "nat \<Rightarrow> scheduler_state"
    and packet_at :: "nat \<Rightarrow> packet" and ordinary :: packet
    and epoch :: nat
  assumes submit_ready: "\<And>n. scheduler_step (before n) (Submit (packet_at n)) (Accepted (packet_identity (packet_at n))) (queued n)"
    and service_ready: "\<And>n. scheduler_step (queued n) Honest_Service
      (Internal (Served_Regulation (packet_identity (packet_at n)) (regulatory_case (packet_contents (packet_at n)))))
      (before (Suc n))"
    and admissible: "\<And>I n. policy_allows I (rollback_context (before n)) (packet_contents (packet_at n))"
    and eligible: "\<And>I n. policy_allows I (rollback_context (queued n)) (packet_contents (packet_at n))"
    and registry: "\<And>n. authority_epoch (rollback_context (queued n)) = epoch"
    and one: "\<And>n. regulatory_queue (queued n) = [packet_at n]"
    and unused: "\<And>n. ordinary_receipts (queued n) (packet_identity (packet_at n)) = None"
      "\<And>n. regulation_receipts (queued n) (packet_identity (packet_at n)) = None"
    and zero: "\<And>n. regulatory_queue (before n) = []"
    and wait_before: "\<And>n. ordinary_queue (before n) = [ordinary]"
    and wait_queued: "\<And>n. ordinary_queue (queued n) = [ordinary]"
begin

definition offered_turn :: "nat \<Rightarrow> service_turn" where
  "offered_turn n = \<lparr>turn_actor = 0, turn_authority = epoch, turn_id = n\<rparr>"

definition permitted_orders :: "nat \<Rightarrow> service_turn \<Rightarrow> packet option" where
  "permitted_orders n turn = (if turn_id turn < n \<and> turn = offered_turn (turn_id turn)
    then Some (packet_at (turn_id turn)) else None)"

lemma offered_turn_number [simp]:
  "turn_id (offered_turn n) = n" by (simp add: offered_turn_def)

lemma extending_order_log:
  "permitted_orders (Suc n) = (permitted_orders n)(offered_turn n \<mapsto> packet_at n)"
proof (rule ext)
  fix turn
  show "permitted_orders (Suc n) turn = ((permitted_orders n)(offered_turn n \<mapsto> packet_at n)) turn"
    by (cases "turn = offered_turn n")
      (auto simp: permitted_orders_def less_Suc_eq split: if_splits)
qed

primrec known_admissions :: "nat \<Rightarrow> nat \<Rightarrow> packet option" where
  "known_admissions 0 = (\<lambda>q. if q = packet_identity ordinary then Some ordinary else None)"
| "known_admissions (Suc n) = (known_admissions n)(packet_identity (packet_at n) \<mapsto> packet_at n)"

definition source_evidence :: machine_evidence where
  "source_evidence = \<lparr>authority_facts = unapproved, active_signer = (\<lambda>_. Some 0),
     certified_order_pairs = range (\<lambda>n. (offered_turn n,packet_at n)),
     source_at_cut = (\<lambda>_ binding. (binding, Unavailable))\<rparr>"

definition cycle_start :: "nat \<Rightarrow> scoped_machine" where
  "cycle_start n = \<lparr>committed_cut = \<lparr>store_cut = 3*n, observed_scheduler = before n\<rparr>,
    order_at = permitted_orders n, answer_at = permitted_orders n, admitted_at = known_admissions n\<rparr>"

definition after_submit :: "nat \<Rightarrow> scoped_machine" where
  "after_submit n = (write_scheduler (cycle_start n) (queued n))\<lparr>admitted_at := known_admissions (Suc n)\<rparr>"

definition after_order :: "nat \<Rightarrow> scoped_machine" where
  "after_order n = (write_scheduler (after_submit n) (queued n))\<lparr>order_at := permitted_orders (Suc n)\<rparr>"

lemma real_cycle_submission:
  "run_machine source_evidence (cycle_start n) (Receive_Packet (packet_at n)) =
    (Admission (Accepted (packet_identity (packet_at n))),after_submit n)"
  using submit_ready[of n] admissible[of unapproved n]
  by (simp add: source_evidence_def cycle_start_def after_submit_def scoped_submit_def scheduler_step_def)

lemma real_cycle_registration:
  "run_machine source_evidence (after_submit n) (Bind_Order (offered_turn n) (packet_at n)) =
    (Registered_Order,after_order n)"
proof -
  have certified: "(offered_turn n,packet_at n) \<in> range (\<lambda>n. (offered_turn n,packet_at n))" by (rule rangeI)
  from certified registry[of n] show ?thesis
    by (simp add: after_order_def after_submit_def cycle_start_def source_evidence_def
        write_scheduler_def qualified_turn_def offered_turn_def extending_order_log permitted_orders_def)
qed

lemma real_cycle_service:
  "run_machine source_evidence (after_order n)
    (Attempt_At (committed_cut (after_order n)) (offered_turn n) (packet_at n)) =
    (Observed_Service (Compared_Attempt (Service_Result (Internal
      (Served_Regulation (packet_identity (packet_at n)) (regulatory_case (packet_contents (packet_at n))))))),
     cycle_start (Suc n))"
proof -
  have bound: "(offered_turn n,packet_at n) \<in> signed_packets_by_turn (permitted_orders (Suc n))"
    by (simp add: signed_packets_by_turn_def permitted_orders_def)
  have current: "qualified_turn (\<lambda>_. Some 0) {offered_turn n} (queued n) (offered_turn n)"
    by (simp add: offered_turn_def qualified_turn_def registry)
  have view: "authorized_view unapproved (queued n) = queued n"
    by (simp add: authorized_view_def one eligible)
  from real_level_step_is_reproduced_by_a_current_exact_signed_order[OF service_ready view bound current one]
  have service:
    "scoped_service unapproved (\<lambda>_. Some 0) (signed_packets_by_turn (permitted_orders (Suc n))) (queued n)
      (offered_turn n) (packet_at n) =
      (Internal (Served_Regulation (packet_identity (packet_at n)) (regulatory_case (packet_contents (packet_at n)))),before (Suc n))" .
  have certified: "(offered_turn n,packet_at n) \<in> range (\<lambda>n. (offered_turn n,packet_at n))" by (rule rangeI)
  from certified show ?thesis
    by (simp add: after_order_def after_submit_def cycle_start_def source_evidence_def write_scheduler_def
      retained_answer_def observe_sequence_def try_service_at_def conflicting_receipt_def
      permitted_orders_def service unused algebra_simps extending_order_log[symmetric])
qed

definition priority_trace_event :: "nat \<Rightarrow> machine_event" where
  "priority_trace_event i = (let n = i div 3 in
    if i mod 3 = 0 then
      \<lparr>source_state = cycle_start n, step_action = Receive_Packet (packet_at n),
       step_outcome = Admission (Accepted (packet_identity (packet_at n))), target_state = after_submit n\<rparr>
    else if i mod 3 = 1 then
      \<lparr>source_state = after_submit n, step_action = Bind_Order (offered_turn n) (packet_at n),
       step_outcome = Registered_Order, target_state = after_order n\<rparr>
    else
      \<lparr>source_state = after_order n, step_action = Attempt_At (committed_cut (after_order n)) (offered_turn n) (packet_at n),
       step_outcome = Observed_Service (Compared_Attempt (Service_Result (Internal
        (Served_Regulation (packet_identity (packet_at n)) (regulatory_case (packet_contents (packet_at n))))))),
       target_state = cycle_start (Suc n)\<rparr>)"

lemma actual_priority_trace_happens:
  "step_occurs (machine_step source_evidence) (priority_trace_event i)"
  by (simp add: priority_trace_event_def Let_def step_occurs_def machine_step_def
    real_cycle_submission real_cycle_registration real_cycle_service del: run_machine.simps)

lemma actual_priority_trace_links:
  "target_state (priority_trace_event i) = source_state (priority_trace_event (Suc i))"
proof -
  have arithmetic:
    "(i mod 3 = 0 \<and> Suc i mod 3 = 1 \<and> Suc i div 3 = i div 3) \<or>
     (i mod 3 = 1 \<and> Suc i mod 3 = 2 \<and> Suc i div 3 = i div 3) \<or>
     (i mod 3 = 2 \<and> Suc i mod 3 = 0 \<and> Suc i div 3 = Suc (i div 3))"
    by presburger
  from arithmetic show ?thesis by (auto simp: priority_trace_event_def Let_def)
qed

theorem supplied_priority_orders_do_not_force_ordinary_completion:
  "infinite_run (machine_step source_evidence) {cycle_start 0} UNIV priority_trace_event"
  "\<exists>j\<ge>i. priority_commit (step_outcome (priority_trace_event j))"
  "waiting (packet_identity ordinary) (scheduler_at (source_state (priority_trace_event i)))"
  "ordinary_commit_id (step_outcome (priority_trace_event i)) = None"
  "length (regulatory_queue (scheduler_at (source_state (priority_trace_event i)))) \<le> 1"
proof -
  show "infinite_run (machine_step source_evidence) {cycle_start 0} UNIV priority_trace_event"
    using actual_priority_trace_happens actual_priority_trace_links
    by (simp add: infinite_run_def) (simp add: priority_trace_event_def Let_def)
  have modulus: "(3*i+2) mod 3 = (2::nat)" by presburger
  have productive: "priority_commit (step_outcome (priority_trace_event (3*i+2)))"
    using modulus by (auto simp: priority_trace_event_def Let_def priority_commit_def)
  have "i \<le> 3*i+2" by arith
  with productive show "\<exists>j\<ge>i. priority_commit (step_outcome (priority_trace_event j))"
    by (intro exI[of _ "3*i+2"]) simp
  show "waiting (packet_identity ordinary) (scheduler_at (source_state (priority_trace_event i)))"
    "ordinary_commit_id (step_outcome (priority_trace_event i)) = None"
    "length (regulatory_queue (scheduler_at (source_state (priority_trace_event i)))) \<le> 1"
    by (simp_all add: priority_trace_event_def Let_def waiting_def cycle_start_def after_submit_def after_order_def
      wait_before wait_queued one zero)
qed

end

interpretation fresh_priority: scoped_priority_trace fresh_state fresh_pending fresh_packet ordinary_packet 4
proof unfold_locales
  show "scheduler_step (fresh_state n) (Submit (fresh_packet n))
      (Accepted (packet_identity (fresh_packet n))) (fresh_pending n)" for n
    using fresh_case_submitted[of n] by (simp add: fresh_packet_def)
  show "scheduler_step (fresh_pending n) Honest_Service
      (Internal (Served_Regulation (packet_identity (fresh_packet n)) (regulatory_case (packet_contents (fresh_packet n)))))
      (fresh_state (Suc n))" for n
    using fresh_case_actually_served[of n] by (simp add: fresh_packet_def)
qed (simp_all add: fresh_state_def fresh_initial_def fresh_pending_def fresh_packet_def
       fresh_log_def enqueue_packet_def packet_example)

interpretation repeated_lowering: scoped_priority_trace cycle_state cycle_queued cycle_packet ordinary_packet 4
proof unfold_locales
  show "scheduler_step (cycle_state n) (Submit (cycle_packet n))
      (Accepted (packet_identity (cycle_packet n))) (cycle_queued n)" for n
    using cycle_allows_actual_new_packet[of n] by (simp add: cycle_packet_def)
  show "scheduler_step (cycle_queued n) Honest_Service
      (Internal (Served_Regulation (packet_identity (cycle_packet n)) (regulatory_case (packet_contents (cycle_packet n)))))
      (cycle_state (Suc n))" for n
    using cycle_consumes_actual_priority_packet[of n] by (simp add: cycle_packet_def split: if_splits)
qed (simp_all add: cycle_state_def cycle_queued_def cycle_packet_def cycle_log_def
       enqueue_packet_def packet_example split: if_splits)

end
