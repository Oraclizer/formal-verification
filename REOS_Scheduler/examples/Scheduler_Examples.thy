theory Scheduler_Examples
  imports REOS_Request_Progress.Escalation_Progress REOS_Rollback_Examples.Rollback_Examples
begin

section \<open>Admission, rotation, and the authorized rollback consumer\<close>

definition ordinary_packet :: packet where
  "ordinary_packet = \<lparr>packet_identity = 101, packet_contents = Ordinary_Work 55,
      packet_authority_epoch = 4, packet_policy_epoch = 8, packet_order = 12\<rparr>"

definition urgent_packet :: packet where
  "urgent_packet = ordinary_packet\<lparr>packet_identity := 102, packet_contents := Raise_Level 9 1, packet_order := 0\<rparr>"

definition rollback_packet :: packet where
  "rollback_packet = urgent_packet\<lparr>packet_identity := 11,
     packet_contents := Execute_Governed_Rollback intent None None\<rparr>"

definition unsigned_alternate :: packet where
  "unsigned_alternate = ordinary_packet\<lparr>packet_contents := Raise_Level 9 2\<rparr>"

definition scheduler_example :: scheduler_state where
  "scheduler_example = \<lparr>rollback_context = fixture,
    signed_packets = {ordinary_packet, urgent_packet, rollback_packet, rollback_packet\<lparr>packet_identity := 160\<rparr>},
    regulatory_grants = {urgent_packet},
    verified_context_updates = {(5,5,9,8),(5,4,9,9)},
    ordinary_queue = [], regulatory_queue = [], dedup_ids = {},
    ordinary_receipts = (\<lambda>_. None), regulation_receipts = (\<lambda>_. None),
    severity_now = (\<lambda>_. 0), severity_limit = (\<lambda>_. 2)\<rparr>"

lemmas scheduler_reduction = scheduler_step_def admit_def enqueue_packet_def
  packet_fresh_def ready_regulation_def regulatory_effect_def priority_slots_def
  next_regulation_def schedule_contract serve_ordinary_def waiting_def

lemmas packet_example = scheduler_example_def ordinary_packet_def urgent_packet_def
  rollback_packet_def unsigned_alternate_def fixture_setup

definition ordinary_admitted :: scheduler_state where
  "ordinary_admitted = snd (admit scheduler_example ordinary_packet)"

definition priority_admitted :: scheduler_state where
  "priority_admitted = snd (admit ordinary_admitted urgent_packet)"

definition priority_handled :: scheduler_state where
  "priority_handled = snd (schedule priority_admitted)"

definition ordinary_handled :: scheduler_state where
  "ordinary_handled = snd (schedule priority_handled)"

lemma rejected_spam_does_not_poison_the_real_id:
  "scheduler_step scheduler_example (Submit unsigned_alternate) (Rejected Signature_Failed) scheduler_example"
  "packet_identity unsigned_alternate = packet_identity ordinary_packet"
  "scheduler_step scheduler_example (Submit ordinary_packet) (Accepted 101) ordinary_admitted"
  "priority_slots scheduler_example = 0"
  by (simp_all add: scheduler_reduction packet_example ordinary_admitted_def)

lemma regulation_then_exact_ordinary_completion:
  "scheduler_step ordinary_admitted (Submit urgent_packet) (Accepted 102) priority_admitted"
  "priority_slots priority_admitted = 1"
  "scheduler_step priority_admitted Honest_Service (Internal (Served_Regulation 102 9)) priority_handled"
  "severity_now priority_handled 9 = 1"
  "regulation_receipts priority_handled 102 = Some urgent_packet"
  "waiting 101 priority_handled"
  "scheduler_step priority_handled Honest_Service (Internal (Served_Ordinary 101)) ordinary_handled"
  "ordinary_receipts ordinary_handled 101 = Some ordinary_packet"
  "\<not> waiting 101 ordinary_handled"
  "scheduler_step ordinary_handled (Submit ordinary_packet) (Rejected Reused_ID) ordinary_handled"
  by (simp_all add: scheduler_reduction packet_example
      ordinary_admitted_def priority_admitted_def priority_handled_def ordinary_handled_def)

definition new_authority :: scheduler_state where
  "new_authority = snd (run_scheduler priority_admitted (Rotate_Context 5 5 9 8))"

definition new_policy :: scheduler_state where
  "new_policy = snd (run_scheduler priority_admitted (Rotate_Context 5 4 9 9))"

lemma real_epoch_changes_remove_old_priority:
  "scheduler_step priority_admitted (Rotate_Context 5 5 9 8) (Internal Snapshot_Changed) new_authority"
  "scheduler_step priority_admitted (Rotate_Context 5 4 9 9) (Internal Snapshot_Changed) new_policy"
  "priority_slots new_authority = 0"
  "priority_slots new_policy = 0"
  "ordinary_queue new_authority = [ordinary_packet]"
  "ordinary_queue new_policy = [ordinary_packet]"
  "scheduler_step priority_admitted (Rotate_Context 5 7 9 8) (Rejected Invalid_Update) priority_admitted"
  by (simp_all add: scheduler_reduction packet_example ordinary_admitted_def priority_admitted_def
      new_authority_def new_policy_def)

theorem after_a_rotation_with_no_eligible_regulation_the_next_honest_turn_serves_the_head:
  assumes rotated: "scheduler_step s (Rotate_Context time a k epoch) (Internal Snapshot_Changed) t"
    and queue: "ordinary_queue s = p # rest"
    and ordinary: "ordinary_body (packet_contents p)"
    and priority: "priority_slots t = 0"
  shows "scheduler_step t Honest_Service (Internal (Served_Ordinary (packet_identity p)))
     (t\<lparr>ordinary_queue := rest, ordinary_receipts := (ordinary_receipts t)(packet_identity p \<mapsto> p)\<rparr>)"
proof -
  from rotated have kept: "ordinary_queue t = ordinary_queue s"
    by (cases rule: ordinary_queue_update) auto
  from priority have no_priority: "next_regulation t = None"
    by (simp add: no_regulation_selected_iff_no_priority_slot)
  from kept queue ordinary no_priority show ?thesis
    by (simp add: scheduler_step_def schedule_contract serve_ordinary_def)
qed

lemma rotated_fixtures_actually_service_the_waiting_ordinary_packet:
  "scheduler_step new_authority Honest_Service (Internal (Served_Ordinary 101)) (snd (schedule new_authority))"
  "scheduler_step new_policy Honest_Service (Internal (Served_Ordinary 101)) (snd (schedule new_policy))"
  "ordinary_receipts (snd (schedule new_authority)) 101 = Some ordinary_packet"
  "ordinary_receipts (snd (schedule new_policy)) 101 = Some ordinary_packet"
  by (simp_all add: scheduler_reduction packet_example ordinary_admitted_def priority_admitted_def
      new_authority_def new_policy_def)

lemma malformed_ordinary_input_is_a_nonservice_fault:
  "scheduler_step (scheduler_example\<lparr>ordinary_queue := [urgent_packet]\<rparr>) Honest_Service
    (Operational_Failure Invalid_Queue_State) (scheduler_example\<lparr>ordinary_queue := [urgent_packet]\<rparr>)"
  by (simp add: scheduler_reduction packet_example)

definition rollback_admitted :: scheduler_state where
  "rollback_admitted = snd (admit scheduler_example rollback_packet)"

definition rollback_handled :: scheduler_state where
  "rollback_handled = snd (schedule rollback_admitted)"

lemma scheduled_regulatory_rollback_uses_the_exact_assured_intent:
  "scheduler_step scheduler_example (Submit rollback_packet) (Accepted 11) rollback_admitted"
  "scheduler_step rollback_admitted Honest_Service (Internal (Served_Regulation 11 9)) rollback_handled"
  "regulation_receipts rollback_handled 11 = Some rollback_packet"
  "cell_value (rollback_context rollback_handled) chosen = 2"
  "cell_value (rollback_context rollback_handled) sibling = 9"
  "scheduler_step scheduler_example (Submit (rollback_packet\<lparr>packet_identity := 160\<rparr>))
    (Rejected Regulation_Ineligible) scheduler_example"
  by (simp_all add: scheduler_reduction packet_example decision_rules
      rollback_admitted_def rollback_handled_def)

section \<open>Counterexample without an effective worker opportunity\<close>

definition blocked_turn ::
  "scheduler_state \<Rightarrow> (scheduler_state,scheduler_action,scheduler_result) transition"
where
  "blocked_turn s = \<lparr>source_state = s, step_action = Unproductive_Turn,
      step_outcome = Operational_Failure No_Effective_Opportunity, target_state = s\<rparr>"

theorem finite_interference_alone_cannot_force_service:
  assumes "waiting q s"
  shows "infinite_run scheduler_step {s} UNIV (\<lambda>_. blocked_turn s)"
    "finite {i. spends_priority ((\<lambda>_. blocked_turn s) (i::nat))}"
    "\<forall>i::nat. waiting q (source_state ((\<lambda>_. blocked_turn s) i)) \<and>
      \<not> served_ordinary q ((\<lambda>_. blocked_turn s) i)"
  using assms
  by (simp_all add: infinite_run_def step_occurs_def scheduler_step_def blocked_turn_def
    spends_priority_def served_ordinary_def)

end
