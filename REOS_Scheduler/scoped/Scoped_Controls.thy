theory Scoped_Controls
  imports Scoped_Record Scoped_Order_Safety
begin

definition machine_start :: scoped_machine where
  "machine_start =
    \<lparr>committed_cut = \<lparr>store_cut = 0, observed_scheduler = governed_with_fifo\<rparr>,
     order_at = (\<lambda>_. None), answer_at = (\<lambda>_. None),
     admitted_at = (\<lambda>q. if q = 11 then Some proposed_governance else if q = 101 then Some ordinary_packet else None)\<rparr>"

definition case_evidence :: machine_evidence where
  "case_evidence = \<lparr>authority_facts = approved_governance, active_signer = (\<lambda>_. Some 2),
     certified_order_pairs = {(local_governance_turn, proposed_governance),
       (local_governance_turn, ordinary_packet), (ordinary_turn, ordinary_packet)},
     source_at_cut = (\<lambda>_ binding.
       if binding = expected_lookup then (binding, Verified_Finality expected_lookup receipt)
       else (binding, Unavailable))\<rparr>"

definition paired_governance :: scoped_machine where
  "paired_governance = snd (run_machine case_evidence machine_start (Bind_Order local_governance_turn proposed_governance))"

definition completed_governance :: scoped_machine where
  "completed_governance = snd (run_machine case_evidence paired_governance
    (Attempt_At (committed_cut paired_governance) local_governance_turn proposed_governance))"

definition paired_ordinary :: scoped_machine where
  "paired_ordinary = snd (run_machine case_evidence completed_governance (Bind_Order ordinary_turn ordinary_packet))"

definition completed_ordinary :: scoped_machine where
  "completed_ordinary = snd (run_machine case_evidence paired_ordinary
    (Attempt_At (committed_cut paired_ordinary) ordinary_turn ordinary_packet))"

lemmas local_machine_cases = machine_start_def case_evidence_def paired_governance_def
  completed_governance_def paired_ordinary_def completed_ordinary_def write_scheduler_def
  signed_packets_by_turn_def retained_answer_def matches_plan_order_def

lemma two_raw_observation_calls_allow_the_same_turn_to_change_its_body:
  defines "orders1 \<equiv> (\<lambda>turn. if turn = local_governance_turn then Some proposed_governance else None)"
    and "orders2 \<equiv> (\<lambda>turn. if turn = local_governance_turn then Some ordinary_packet else None)"
    and "first \<equiv> \<lparr>store_cut = 1, observed_scheduler = governed_with_fifo\<rparr>"
    and "second \<equiv> \<lparr>store_cut = 2, observed_scheduler = governed_effect\<rparr>"
  shows "observe_sequence approved_governance (\<lambda>_. Some 2) orders1 (\<lambda>_. None) first first
     local_governance_turn proposed_governance =
     (Compared_Attempt (Service_Result (Internal (Served_Regulation 11 9))), governed_effect)"
    "\<exists>s. observe_sequence approved_governance (\<lambda>_. Some 2) orders2 orders1 second second
       local_governance_turn ordinary_packet =
       (Compared_Attempt (Service_Result (Internal (Served_Ordinary 101))), s)
       \<and> ordinary_receipts s 101 = Some ordinary_packet"
  by (simp_all add: observe_sequence_def try_service_at_def orders1_def orders2_def first_def second_def
       signed_packets_by_turn_def governed_with_fifo_def governed_effect_def
       approved_governance_def governance_execution)

lemma durable_dispatch_consumes_two_distinct_orders_and_exactly_two_effects:
  "run_machine case_evidence machine_start (Bind_Order local_governance_turn proposed_governance)
       = (Registered_Order, paired_governance)"
  "run_machine case_evidence paired_governance
     (Attempt_At (committed_cut paired_governance) local_governance_turn proposed_governance)
       = (Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Regulation 11 9)))), completed_governance)"
  "run_machine case_evidence completed_governance (Bind_Order local_governance_turn ordinary_packet)
       = (Refused_Order, completed_governance)"
  "run_machine case_evidence completed_governance
     (Attempt_At (committed_cut machine_start) local_governance_turn proposed_governance)
       = (Observed_Service (Replayed_Receipt proposed_governance), completed_governance)"
  "run_machine case_evidence paired_ordinary
     (Attempt_At (committed_cut completed_governance) ordinary_turn ordinary_packet)
       = (Observed_Service (Compared_Attempt Compare_Conflict), paired_ordinary)"
  "run_machine case_evidence paired_ordinary
     (Attempt_At (committed_cut paired_ordinary) ordinary_turn ordinary_packet)
       = (Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Ordinary 101)))), completed_ordinary)"
  "cell_value (rollback_context (scheduler_at completed_ordinary)) chosen = 2"
  "ordinary_receipts (scheduler_at completed_ordinary) 101 = Some ordinary_packet"
  "answer_at completed_ordinary local_governance_turn = Some proposed_governance"
  "answer_at completed_ordinary ordinary_turn = Some ordinary_packet"
  "ordinary_queue (scheduler_at paired_ordinary) = [ordinary_packet]"
  "order_at paired_ordinary ordinary_turn = Some ordinary_packet"
  "ordinary_receipts (scheduler_at paired_ordinary) 101 = None"
proof -
  let ?g = local_governance_turn
  let ?gp = proposed_governance
  let ?o = ordinary_turn
  let ?op = ordinary_packet
  let ?E = case_evidence
  let ?one = "(\<lambda>_::service_turn. None)(?g \<mapsto> ?gp)"
  let ?both = "?one(?o \<mapsto> ?op)"
  let ?signed1 = "{(?g,?gp)}"
  let ?signed2 = "{(?g,?gp),(?o,?op)}"
  have initially_empty:
    "ordinary_receipts governed_with_fifo (packet_identity ?gp) = None"
    "regulation_receipts governed_with_fifo (packet_identity ?gp) = None"
    by (simp_all add: governed_with_fifo_def governance_execution)
  have ordinary_unserved:
    "ordinary_receipts governed_effect (packet_identity ?op) = None"
    "regulation_receipts governed_effect (packet_identity ?op) = None"
    by (simp_all add: governed_with_fifo_def governed_effect_def approved_governance_def governance_execution)
  have distinct: "?o \<noteq> ?g" by (simp add: ordinary_turn_def local_governance_turn_def)
  have reverse: "?g \<noteq> ?o" by (simp add: ordinary_turn_def local_governance_turn_def)
  have signed1: "signed_packets_by_turn ?one = ?signed1"
    by (auto simp: signed_packets_by_turn_def split: if_splits)
  have signed2: "signed_packets_by_turn ?both = ?signed2"
    using distinct by (auto simp: signed_packets_by_turn_def split: if_splits)
  note governance = checked_rollback_and_ordinary_service_share_the_same_model_run(3)
  obtain ordinary_state where ordinary:
    "scoped_service approved_governance (\<lambda>_. Some 2) {(?o,?op)} governed_effect ?o ?op =
      (Internal (Served_Ordinary 101),ordinary_state)"
    "ordinary_receipts ordinary_state 101 = Some ?op" "cell_value (rollback_context ordinary_state) chosen = 2"
    using checked_rollback_and_ordinary_service_share_the_same_model_run(6) by blast
  have governance_current: "qualified_turn (\<lambda>_. Some 2) {?g} governed_with_fifo ?g"
    by (rule scoped_commit_runs_the_approved_view[OF governance]) assumption
  have ordinary_current: "qualified_turn (\<lambda>_. Some 2) {?o} governed_effect ?o"
    by (rule scoped_commit_runs_the_approved_view[OF ordinary(1)]) assumption
  have same_selection:
    "scoped_service approved_governance (\<lambda>_. Some 2) ?signed2 governed_effect ?o ?op =
      scoped_service approved_governance (\<lambda>_. Some 2) {(?o,?op)} governed_effect ?o ?op"
    by (simp add: scoped_service_def Let_def)
  let ?g_ready = "(write_scheduler machine_start governed_with_fifo)\<lparr>order_at := ?one\<rparr>"
  have g_bind: "run_machine ?E machine_start (Bind_Order ?g ?gp) = (Registered_Order, ?g_ready)"
    using governance_current by (simp add: machine_start_def case_evidence_def write_scheduler_def)
  from g_bind have g_ready: "paired_governance = ?g_ready" by (simp add: paired_governance_def)
  from g_bind g_ready show "run_machine ?E machine_start (Bind_Order ?g ?gp) = (Registered_Order, paired_governance)" by simp
  let ?g_done = "(write_scheduler ?g_ready governed_effect)\<lparr>answer_at := ?one\<rparr>"
  let ?g_reply = "Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Regulation 11 9))))"
  have g_commit: "run_machine ?E paired_governance (Attempt_At (committed_cut paired_governance) ?g ?gp) = (?g_reply,?g_done)"
    by (simp add: g_ready case_evidence_def machine_start_def write_scheduler_def signed1
       observe_sequence_def try_service_at_def conflicting_receipt_def initially_empty retained_answer_def governance)
  from g_commit have g_done: "completed_governance = ?g_done" by (simp add: completed_governance_def)
  with g_commit show "run_machine ?E paired_governance (Attempt_At (committed_cut paired_governance) ?g ?gp)
       = (?g_reply, completed_governance)" by simp
  then have committed: "machine_step ?E paired_governance (Attempt_At (committed_cut paired_governance) ?g ?gp)
       ?g_reply completed_governance" by (simp add: machine_step_def)
  show "run_machine ?E completed_governance (Bind_Order ?g ?op) = (Refused_Order, completed_governance)"
    by (rule service_commit_uses_an_attested_current_order_and_replays_at_the_next_read(4)[OF committed])
      (simp_all add: ordinary_packet_def proposed_governance_def urgent_packet_def)
  show "run_machine ?E completed_governance (Attempt_At (committed_cut machine_start) ?g ?gp)
       = (Observed_Service (Replayed_Receipt ?gp), completed_governance)"
    by (rule service_commit_uses_an_attested_current_order_and_replays_at_the_next_read(3)[OF committed]) simp
  let ?o_ready = "(write_scheduler ?g_done governed_effect)\<lparr>order_at := ?both\<rparr>"
  have o_bind: "run_machine ?E completed_governance (Bind_Order ?o ?op) = (Registered_Order, ?o_ready)"
    using ordinary_current distinct by (simp add: g_done case_evidence_def write_scheduler_def)
  from o_bind have o_ready: "paired_ordinary = ?o_ready" by (simp add: paired_ordinary_def)
  show "run_machine ?E paired_ordinary (Attempt_At (committed_cut completed_governance) ?o ?op)
       = (Observed_Service (Compared_Attempt Compare_Conflict), paired_ordinary)"
    using distinct by (simp add: g_done o_ready case_evidence_def write_scheduler_def
       observe_sequence_def try_service_at_def conflicting_receipt_def ordinary_unserved retained_answer_def)
  let ?o_reply = "Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Ordinary 101))))"
  let ?o_done = "(write_scheduler ?o_ready ordinary_state)\<lparr>answer_at := ?both\<rparr>"
  have ordinary_step:
    "scoped_service approved_governance (\<lambda>_. Some 2) ?signed2 governed_effect ?o ?op =
      (Internal (Served_Ordinary 101),ordinary_state)" using same_selection ordinary by simp
  have o_commit: "run_machine ?E paired_ordinary (Attempt_At (committed_cut paired_ordinary) ?o ?op) = (?o_reply,?o_done)"
    using distinct by (simp add: o_ready case_evidence_def write_scheduler_def observe_sequence_def try_service_at_def
       conflicting_receipt_def ordinary_unserved retained_answer_def signed2 ordinary_step)
  from o_commit have o_done: "completed_ordinary = ?o_done" by (simp add: completed_ordinary_def)
  show "run_machine ?E paired_ordinary (Attempt_At (committed_cut paired_ordinary) ?o ?op) = (?o_reply,completed_ordinary)"
    by (simp only: o_commit o_done)
  have executed: "scheduler_at completed_ordinary = ordinary_state" by (simp add: o_done write_scheduler_def)
  show "cell_value (rollback_context (scheduler_at completed_ordinary)) chosen = 2"
    by (simp only: executed ordinary(3))
  show "ordinary_receipts (scheduler_at completed_ordinary) 101 = Some ?op"
    by (simp only: executed ordinary(2))
  show "answer_at completed_ordinary ?g = Some ?gp" "answer_at completed_ordinary ?o = Some ?op"
    by (simp_all add: o_done reverse write_scheduler_def)
  show "ordinary_queue (scheduler_at paired_ordinary) = [ordinary_packet]"
    "order_at paired_ordinary ordinary_turn = Some ordinary_packet"
    by (simp_all add: o_ready write_scheduler_def checked_rollback_and_ordinary_service_share_the_same_model_run(5))
  have "ordinary_receipts governed_with_fifo 101 = None"
    by (simp add: governed_with_fifo_def governance_execution)
  with scoped_regulatory_commit_preserves_fifo(2)[OF governance]
  show "ordinary_receipts (scheduler_at paired_ordinary) 101 = None"
    by (simp add: o_ready write_scheduler_def)
qed

definition source_machine :: scoped_machine where
  "source_machine = machine_start\<lparr>committed_cut :=
    \<lparr>store_cut = 30, observed_scheduler = (scheduler_at machine_start)\<lparr>rollback_context := pending_ledger\<rparr>\<rparr>\<rparr>"

definition published_finality :: scoped_machine where
  "published_finality = snd (run_machine case_evidence source_machine (Import_At (committed_cut source_machine) expected_lookup))"

definition repaired_finality :: scoped_machine where
  "repaired_finality = snd (run_machine case_evidence published_finality (Repair_At (committed_cut published_finality) 77 4))"

lemma authenticated_finality_import_is_seen_by_the_replica_consumer:
  "run_machine case_evidence source_machine (Import_At (committed_cut source_machine) expected_lookup) =
    (Imported_Record (Internal (Recorded_Finality 77)),published_finality)"
  "run_machine case_evidence published_finality (Repair_At (committed_cut source_machine) 77 4) =
    (Obsolete_Read,published_finality)"
  "run_machine case_evidence published_finality (Repair_At (committed_cut published_finality) 77 4) =
    (Repaired_Replica (Internal (Repaired_From_Record 77 4)),repaired_finality)"
  "cell_value (rollback_context (scheduler_at repaired_finality)) terminal = 13"
  "replica_value (rollback_context (scheduler_at repaired_finality)) 4 terminal = 13"
  "cell_value (rollback_context (scheduler_at repaired_finality)) other_resource = 9"
  by (simp_all add: source_machine_def published_finality_def repaired_finality_def local_machine_cases
      expected_lookup_def pending_ledger_def scoped_finality_def fixture_setup decision_rules
      commit_internal_def at_commit_def agrees_with_known_finality_def)

definition initial_spam_cut :: scoped_machine where
  "initial_spam_cut = machine_start\<lparr>committed_cut :=
     \<lparr>store_cut = 0, observed_scheduler = scheduler_example\<rparr>, admitted_at := (\<lambda>_. None)\<rparr>"

lemma unsigned_spam_cannot_consume_the_later_admission:
  "run_machine case_evidence initial_spam_cut (Receive_Packet unsigned_alternate) =
    (Admission (Rejected Signature_Failed), initial_spam_cut)"
  "packet_identity unsigned_alternate = packet_identity ordinary_packet"
  "\<exists>t. run_machine case_evidence initial_spam_cut (Receive_Packet ordinary_packet) = (Admission (Accepted 101),t)
    \<and> admitted_at t 101 = Some ordinary_packet \<and> ordinary_queue (scheduler_at t) = [ordinary_packet]"
  by (simp_all add: initial_spam_cut_def local_machine_cases scoped_submit_def scheduler_reduction packet_example)

definition endlessly_stale :: "nat \<Rightarrow> (scoped_machine,machine_action,machine_reply) transition" where
  "endlessly_stale _ = \<lparr>source_state = paired_ordinary,
     step_action = Attempt_At (committed_cut completed_governance) ordinary_turn ordinary_packet,
     step_outcome = Observed_Service (Compared_Attempt Compare_Conflict),
     target_state = paired_ordinary\<rparr>"

lemma a_current_order_with_only_stale_compares_never_services_the_packet:
  "infinite_run (machine_step case_evidence) {paired_ordinary} UNIV endlessly_stale"
  "waiting 101 (scheduler_at (source_state (endlessly_stale n)))"
  "order_at (source_state (endlessly_stale n)) ordinary_turn = Some ordinary_packet"
  "ordinary_receipts (scheduler_at (target_state (endlessly_stale n))) 101 = None"
proof -
  show "infinite_run (machine_step case_evidence) {paired_ordinary} UNIV endlessly_stale"
    using durable_dispatch_consumes_two_distinct_orders_and_exactly_two_effects(5)
    by (simp add: infinite_run_def endlessly_stale_def step_occurs_def machine_step_def)
  show "waiting 101 (scheduler_at (source_state (endlessly_stale n)))"
    "order_at (source_state (endlessly_stale n)) ordinary_turn = Some ordinary_packet"
    "ordinary_receipts (scheduler_at (target_state (endlessly_stale n))) 101 = None"
    by (simp_all add: endlessly_stale_def waiting_def ordinary_packet_def
      durable_dispatch_consumes_two_distinct_orders_and_exactly_two_effects(11-13))
qed

end
