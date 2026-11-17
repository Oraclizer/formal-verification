theory Scoped_Rotation
  imports Scoped_Controls
begin

definition before_rotation_turn :: service_turn where
  "before_rotation_turn = \<lparr>turn_actor = 2, turn_authority = 4, turn_id = 20\<rparr>"

definition after_rotation_turn :: service_turn where
  "after_rotation_turn = \<lparr>turn_actor = 3, turn_authority = 5, turn_id = 21\<rparr>"

definition rotation_evidence :: machine_evidence where
  "rotation_evidence = case_evidence\<lparr>
    authority_facts := approved_governance\<lparr>exact_context_updates := {(5,5,9,8)}\<rparr>,
    active_signer := (\<lambda>epoch. if epoch = 4 then Some 2 else if epoch = 5 then Some 3 else None),
    certified_order_pairs := {(before_rotation_turn,urgent_packet),(after_rotation_turn,ordinary_packet)}\<rparr>"

definition before_rotation :: scoped_machine where
  "before_rotation = machine_start\<lparr>committed_cut := \<lparr>store_cut = 0, observed_scheduler = priority_admitted\<rparr>,
    order_at := (\<lambda>turn. if turn = before_rotation_turn then Some urgent_packet else None),
    admitted_at := (\<lambda>q. if q = 102 then Some urgent_packet else if q = 101 then Some ordinary_packet else None)\<rparr>"

definition changed_epoch :: scoped_machine where
  "changed_epoch = snd (run_machine rotation_evidence before_rotation (Change_Context 5 5 9 8))"

definition retirement :: scoped_machine where
  "retirement = snd (run_machine rotation_evidence changed_epoch Retire_Expired)"

definition new_order :: scoped_machine where
  "new_order = snd (run_machine rotation_evidence retirement (Bind_Order after_rotation_turn ordinary_packet))"

lemmas rotation_fixture = rotation_evidence_def before_rotation_def changed_epoch_def retirement_def new_order_def
  before_rotation_turn_def after_rotation_turn_def machine_start_def case_evidence_def checked_advance_def
  local_machine_cases priority_admitted_def ordinary_admitted_def scheduler_reduction packet_example

lemma rotated_authority_retires_only_the_old_priority_and_serves_the_original_fifo:
  "run_machine rotation_evidence before_rotation (Change_Context 5 6 9 8) =
    (Applied_Context (Rejected Invalid_Context),before_rotation)"
  "run_machine rotation_evidence before_rotation (Change_Context 5 5 9 8) =
    (Applied_Context (Internal Context_Advanced),changed_epoch)"
  "run_machine rotation_evidence changed_epoch
    (Attempt_At (committed_cut changed_epoch) before_rotation_turn urgent_packet) =
    (Observed_Service (Compared_Attempt (Service_Result (Operational_Failure No_Effective_Opportunity))),changed_epoch)"
  "run_machine rotation_evidence retirement (Read_Superseded 102) = (Superseded True,retirement)"
  "run_machine rotation_evidence retirement (Read_Superseded 101) = (Superseded False,retirement)"
  "ordinary_queue (scheduler_at retirement) = [ordinary_packet]"
  "\<exists>t. run_machine rotation_evidence new_order
     (Attempt_At (committed_cut new_order) after_rotation_turn ordinary_packet) =
     (Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Ordinary 101)))),t)
     \<and> ordinary_receipts (scheduler_at t) 101 = Some ordinary_packet
     \<and> regulation_receipts (scheduler_at t) 102 = None"
proof -
  let ?I = "authority_facts rotation_evidence"
  let ?sg = "active_signer rotation_evidence"
  let ?old = before_rotation_turn
  let ?fresh = after_rotation_turn
  note state = before_rotation_def machine_start_def write_scheduler_def
  have init: "scheduler_at before_rotation = priority_admitted" by (simp add: state)
  show "run_machine rotation_evidence before_rotation (Change_Context 5 6 9 8) =
    (Applied_Context (Rejected Invalid_Context),before_rotation)"
    by (simp add: rotation_evidence_def checked_advance_def)
  obtain r where advanced: "execute (rollback_context priority_admitted) (Advance_Context 5 5 9 8) = (Internal Context_Advanced,r)"
    and updated: "new_authority = priority_admitted\<lparr>rollback_context := r\<rparr>"
    using real_epoch_changes_remove_old_priority(1)
    by (auto simp: scheduler_step_def split: if_splits)
  have actual: "run_machine rotation_evidence before_rotation (Change_Context 5 5 9 8) =
    (Applied_Context (Internal Context_Advanced), write_scheduler before_rotation new_authority)"
    using advanced updated by (simp add: init rotation_evidence_def checked_advance_def)
  then have turned: "changed_epoch = write_scheduler before_rotation new_authority"
    by (simp add: changed_epoch_def)
  show "run_machine rotation_evidence before_rotation (Change_Context 5 5 9 8) =
    (Applied_Context (Internal Context_Advanced),changed_epoch)" by (simp only: turned actual)
  from advanced have epoch_r: "authority_epoch r = 5" by (auto split: if_splits)
  then have epoch: "authority_epoch (rollback_context new_authority) = 5" by (simp add: updated)
  have unqualified: "\<not> qualified_turn ?sg {?old} new_authority ?old"
    by (simp add: qualified_turn_def before_rotation_turn_def epoch)
  show "run_machine rotation_evidence changed_epoch
    (Attempt_At (committed_cut changed_epoch) ?old urgent_packet) =
    (Observed_Service (Compared_Attempt (Service_Result (Operational_Failure No_Effective_Opportunity))),changed_epoch)"
    using unqualified by (simp add: turned state scoped_service_def
      observe_sequence_def try_service_at_def retained_answer_def Let_def)
  have original_fields:
    "ordinary_queue priority_admitted = [ordinary_packet]" "regulatory_queue priority_admitted = [urgent_packet]"
    "ordinary_receipts priority_admitted = (\<lambda>_. None)" "regulation_receipts priority_admitted = (\<lambda>_. None)"
    "dedup_ids priority_admitted = {101,102}"
    by (simp_all add: Scheduler_Examples.priority_admitted_def Scheduler_Examples.ordinary_admitted_def
      scheduler_reduction packet_example insert_commute)
  have stale: "permanently_stale new_authority urgent_packet"
    by (simp add: permanently_stale_def epoch urgent_packet_def ordinary_packet_def)
  let ?r = "new_authority\<lparr>regulatory_queue := []\<rparr>"
  have empty: "retire_stale new_authority = ?r"
    using original_fields stale by (simp add: updated retire_stale_def)
  have reduced: "?r \<noteq> new_authority"
  proof
    assume "?r = new_authority"
    then have "regulatory_queue ?r = regulatory_queue new_authority" by (rule arg_cong)
    with original_fields show False by (simp add: updated)
  qed
  have retired: "retirement = write_scheduler changed_epoch ?r"
    using empty reduced by (simp add: retirement_def turned Let_def)
  have retired_queue: "ordinary_queue (scheduler_at retirement) = [ordinary_packet]"
    by (simp add: retired updated original_fields)
  show "ordinary_queue (scheduler_at retirement) = [ordinary_packet]" by (rule retired_queue)
  show "run_machine rotation_evidence retirement (Read_Superseded 102) = (Superseded True,retirement)"
    "run_machine rotation_evidence retirement (Read_Superseded 101) = (Superseded False,retirement)"
    by (simp_all add: retired turned state read_superseded_def updated original_fields
      permanently_stale_def epoch epoch_r packet_example)
  have distinct: "?fresh \<noteq> ?old" by (simp add: after_rotation_turn_def before_rotation_turn_def)
  let ?ind = "(write_scheduler retirement ?r)\<lparr>order_at := (order_at retirement)(?fresh \<mapsto> ordinary_packet)\<rparr>"
  have "run_machine rotation_evidence retirement (Bind_Order ?fresh ordinary_packet) = (Registered_Order, ?ind)"
    by (simp add: retired turned state rotation_evidence_def qualified_turn_def after_rotation_turn_def
      before_rotation_turn_def epoch epoch_r distinct)
  then have bound: "new_order = ?ind" by (simp add: new_order_def)
  let ?t = "?r\<lparr>ordinary_queue := [], ordinary_receipts := (ordinary_receipts ?r)(101 \<mapsto> ordinary_packet)\<rparr>"
  have selected: "scoped_service ?I ?sg (signed_packets_by_turn (order_at new_order)) ?r ?fresh ordinary_packet =
      (Internal (Served_Ordinary 101),?t)"
    by (simp add: bound retired turned state rotation_evidence_def signed_packets_by_turn_def qualified_turn_def
       scoped_service_def authorized_view_def planned_def schedule_contract next_regulation_def serve_ordinary_def
       original_fields updated after_rotation_turn_def before_rotation_turn_def epoch epoch_r ordinary_packet_def Let_def)
  let ?reply = "Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Ordinary 101))))"
  let ?done = "(write_scheduler new_order ?t)\<lparr>answer_at := (answer_at new_order)(?fresh \<mapsto> ordinary_packet)\<rparr>"
  have ready: "scheduler_at new_order = ?r" by (simp add: bound)
  have no_answer: "answer_at new_order ?fresh = None" by (simp add: bound retired turned state)
  have clear: "\<not> conflicting_receipt new_order ?fresh ordinary_packet"
    by (simp add: conflicting_receipt_def no_answer ready updated original_fields)
  have signed: "(?fresh,ordinary_packet) \<in> certified_order_pairs rotation_evidence"
    by (simp add: rotation_evidence_def)
  have ran: "run_machine rotation_evidence new_order (Attempt_At (committed_cut new_order) ?fresh ordinary_packet) = (?reply,?done)"
    by (simp add: clear no_answer ready signed observe_sequence_def try_service_at_def retained_answer_def selected)
  show "\<exists>t. run_machine rotation_evidence new_order
     (Attempt_At (committed_cut new_order) ?fresh ordinary_packet) = (?reply,t)
     \<and> ordinary_receipts (scheduler_at t) 101 = Some ordinary_packet \<and> regulation_receipts (scheduler_at t) 102 = None"
    by (intro exI[of _ ?done] conjI) (rule ran, simp_all add: updated original_fields)
qed

end
