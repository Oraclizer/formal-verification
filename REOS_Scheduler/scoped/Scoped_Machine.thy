theory Scoped_Machine
  imports Scoped_Dispatch
begin

record scoped_machine =
  committed_cut :: service_snapshot
  order_at :: "service_turn \<Rightarrow> packet option"
  answer_at :: "service_turn \<Rightarrow> packet option"
  admitted_at :: "nat \<Rightarrow> packet option"

record machine_evidence =
  authority_facts :: verified_inputs
  active_signer :: "nat \<Rightarrow> nat option"
  certified_order_pairs :: "(service_turn \<times> packet) set"
  source_at_cut :: "nat \<Rightarrow> source_binding \<Rightarrow> source_binding \<times> verified_source"

datatype machine_action =
    Receive_Packet packet
  | Bind_Order service_turn packet
  | Attempt_At service_snapshot service_turn packet
  | Change_Context nat nat nat nat
  | Import_At service_snapshot source_binding
  | Repair_At service_snapshot nat nat
  | Retire_Expired
  | Read_Superseded nat

datatype machine_reply =
    Admission scheduler_result
  | Registered_Order | Kept_Order | Refused_Order
  | Observed_Service sequence_observation
  | Applied_Context rollback_result
  | Imported_Record rollback_result
  | Repaired_Replica rollback_result
  | Obsolete_Read | Retired_Expired | Superseded bool

abbreviation scheduler_at :: "scoped_machine \<Rightarrow> scheduler_state" where
  "scheduler_at d \<equiv> observed_scheduler (committed_cut d)"

definition write_scheduler :: "scoped_machine \<Rightarrow> scheduler_state \<Rightarrow> scoped_machine" where
  "write_scheduler d s =
    d\<lparr>committed_cut := \<lparr>store_cut = Suc (store_cut (committed_cut d)), observed_scheduler = s\<rparr>\<rparr>"

fun committed_service :: "sequence_observation \<Rightarrow> bool" where
  "committed_service (Compared_Attempt (Service_Result (Internal (Served_Ordinary _)))) = True"
| "committed_service (Compared_Attempt (Service_Result (Internal (Served_Regulation _ _)))) = True"
| "committed_service _ = False"

lemma committed_service_replies:
  "committed_service obs \<longleftrightarrow>
    (\<exists>q. obs = Compared_Attempt (Service_Result (Internal (Served_Ordinary q)))) \<or>
    (\<exists>q k. obs = Compared_Attempt (Service_Result (Internal (Served_Regulation q k))))"
  by (cases obs rule: committed_service.cases) auto

definition retained_answer :: "scoped_machine \<Rightarrow> service_turn \<Rightarrow> packet option" where
  "retained_answer d turn =
    (if answer_at d turn = order_at d turn then answer_at d turn else None)"

definition conflicting_receipt :: "scoped_machine \<Rightarrow> service_turn \<Rightarrow> packet \<Rightarrow> bool" where
  "conflicting_receipt d turn p \<longleftrightarrow>
    (case answer_at d turn of
       None \<Rightarrow> ordinary_receipts (scheduler_at d) (packet_identity p) \<noteq> None
           \<or> regulation_receipts (scheduler_at d) (packet_identity p) \<noteq> None
     | Some _ \<Rightarrow> retained_answer d turn \<noteq> Some p \<or> \<not> exact_saved_packet (scheduler_at d) p)"

fun run_machine :: "machine_evidence \<Rightarrow> scoped_machine \<Rightarrow> machine_action \<Rightarrow> machine_reply \<times> scoped_machine" where
  "run_machine E d (Receive_Packet p) =
    (case scoped_submit (authority_facts E) (scheduler_at d) p of
       (Accepted q, s) \<Rightarrow> (Admission (Accepted q),
         (write_scheduler d s)\<lparr>admitted_at := (admitted_at d)(q \<mapsto> p)\<rparr>)
     | (r,_) \<Rightarrow> (Admission r,d))"
| "run_machine E d (Bind_Order turn p) =
    (if (turn,p) \<in> certified_order_pairs E \<and> qualified_turn (active_signer E) {turn} (scheduler_at d) turn
     then case order_at d turn of
       None \<Rightarrow> (Registered_Order,
         (write_scheduler d (scheduler_at d))\<lparr>order_at := (order_at d)(turn \<mapsto> p)\<rparr>)
     | Some q \<Rightarrow> (if q = p then Kept_Order else Refused_Order, d)
     else (Refused_Order,d))"
| "run_machine E d (Attempt_At expected turn p) =
    (if (turn,p) \<notin> certified_order_pairs E \<or> conflicting_receipt d turn p then
      (Observed_Service (Compared_Attempt (Service_Result (Operational_Failure No_Effective_Opportunity))), d)
     else case observe_sequence (authority_facts E) (active_signer E) (order_at d)
      (retained_answer d) expected (committed_cut d) turn p of (reply,s) \<Rightarrow>
      (Observed_Service reply, if committed_service reply then
        (write_scheduler d s)\<lparr>answer_at := (answer_at d)(turn \<mapsto> p)\<rparr> else d))"
| "run_machine E d (Change_Context time authority k policy) =
    (case checked_advance (authority_facts E) (rollback_context (scheduler_at d)) time authority k policy of
       (Internal Context_Advanced, r) \<Rightarrow> (Applied_Context (Internal Context_Advanced),
         write_scheduler d ((scheduler_at d)\<lparr>rollback_context := r\<rparr>))
     | (reply,_) \<Rightarrow> (Applied_Context reply,d))"
| "run_machine E d (Import_At expected binding) =
    (if expected \<noteq> committed_cut d then (Obsolete_Read,d)
     else case source_at_cut E (store_cut (committed_cut d)) binding of (current, certified) \<Rightarrow>
       (case import_verified (rollback_context (scheduler_at d)) binding current certified of
          (Internal effect, r) \<Rightarrow> (Imported_Record (Internal effect),
            write_scheduler d ((scheduler_at d)\<lparr>rollback_context := r\<rparr>))
        | (reply,_) \<Rightarrow> (Imported_Record reply,d)))"
| "run_machine E d (Repair_At expected i replica) =
    (if expected \<noteq> committed_cut d then (Obsolete_Read,d)
     else case execute (rollback_context (scheduler_at d)) (Repair_From_Record i replica) of
        (Internal effect, r) \<Rightarrow> (Repaired_Replica (Internal effect),
          write_scheduler d ((scheduler_at d)\<lparr>rollback_context := r\<rparr>))
      | (reply,_) \<Rightarrow> (Repaired_Replica reply,d))"
| "run_machine E d Retire_Expired =
    (let s = retire_stale (scheduler_at d) in
      (Retired_Expired, if s = scheduler_at d then d else write_scheduler d s))"
| "run_machine E d (Read_Superseded q) =
    (Superseded (read_superseded (admitted_at d) (scheduler_at d) q (scheduler_at d)), d)"

definition machine_step :: "machine_evidence \<Rightarrow> (scoped_machine, machine_action, machine_reply) step_rel" where
  "machine_step E d action reply t \<longleftrightarrow> run_machine E d action = (reply,t)"

lemma current_cut_after_a_write [simp]:
  "scheduler_at (write_scheduler d s) = s"
  "store_cut (committed_cut (write_scheduler d s)) = Suc (store_cut (committed_cut d))"
  by (simp_all add: write_scheduler_def)

lemma commit_cut_advances_on_any_store_change:
  assumes "machine_step E d action reply t" "t \<noteq> d"
  shows "store_cut (committed_cut t) = Suc (store_cut (committed_cut d))"
  using assms by (cases action)
    (auto simp: machine_step_def Let_def split: prod.splits option.splits if_splits
      transition_result.splits rollback_internal.splits)

lemma binding_persists_across_operations:
  assumes "machine_step E d action reply t" "order_at d turn = Some p"
  shows "order_at t turn = Some p"
  using assms by (cases action)
    (auto simp: machine_step_def write_scheduler_def Let_def split: prod.splits option.splits if_splits
      transition_result.splits rollback_internal.splits)

lemma an_existing_turn_rejects_a_different_body:
  assumes "order_at d turn = Some original" "p \<noteq> original"
  shows "run_machine E d (Bind_Order turn p) = (Refused_Order,d)"
  using assms by simp

lemma service_trace_consumes_checked_compare:
  assumes "machine_step E d (Attempt_At expected turn p) (Observed_Service obs) t"
    and "committed_service obs"
  shows "observe_sequence (authority_facts E) (active_signer E) (order_at d) (retained_answer d)
       expected (committed_cut d) turn p = (obs,scheduler_at t)"
    and "answer_at t turn = Some p"
    and "(turn,p) \<in> certified_order_pairs E"
proof -
  obtain result s where observation:
    "observe_sequence (authority_facts E) (active_signer E) (order_at d) (retained_answer d)
         expected (committed_cut d) turn p = (result,s)"
    by (cases "observe_sequence (authority_facts E) (active_signer E) (order_at d) (retained_answer d)
         expected (committed_cut d) turn p") blast
  from assms observation have "result = obs"
    "t = (write_scheduler d s)\<lparr>answer_at := (answer_at d)(turn \<mapsto> p)\<rparr>"
    "(turn,p) \<in> certified_order_pairs E"
    by (auto simp: machine_step_def split: if_splits)
  with observation show
    "observe_sequence (authority_facts E) (active_signer E) (order_at d) (retained_answer d)
       expected (committed_cut d) turn p = (obs,scheduler_at t)"
    "answer_at t turn = Some p"
    "(turn,p) \<in> certified_order_pairs E"
    by simp_all
qed

lemma service_attempt_without_a_commit_is_a_read:
  assumes "machine_step E d (Attempt_At expected turn p) (Observed_Service obs) t"
    and "\<not> committed_service obs"
  shows "t = d"
  using assms by (auto simp: machine_step_def split: prod.splits if_splits)

lemma previously_committed_order_has_exact_replay:
  assumes "(turn,p) \<in> certified_order_pairs E"
    "order_at d turn = Some p" "answer_at d turn = Some p" "exact_saved_packet (scheduler_at d) p"
  shows "run_machine E d (Attempt_At expected turn p) = (Observed_Service (Replayed_Receipt p),d)"
  using assms by (simp add: conflicting_receipt_def retained_answer_def observe_sequence_def)

lemma a_missing_receipt_cannot_reexecute_a_previously_answered_order:
  assumes "answer_at d turn \<noteq> None" "\<not> exact_saved_packet (scheduler_at d) p"
  shows "run_machine E d (Attempt_At expected turn p) =
    (Observed_Service (Compared_Attempt (Service_Result (Operational_Failure No_Effective_Opportunity))),d)"
  using assms by (cases "answer_at d turn") (simp_all add: conflicting_receipt_def)

lemma an_unattested_order_cannot_be_committed_or_replayed:
  assumes "(turn,p) \<notin> certified_order_pairs E"
  shows "run_machine E d (Attempt_At expected turn p) =
    (Observed_Service (Compared_Attempt (Service_Result (Operational_Failure No_Effective_Opportunity))),d)"
  using assms by simp

lemma an_actual_service_is_fresh_in_turn_and_request:
  assumes step: "machine_step E d (Attempt_At expected turn p) (Observed_Service obs) t"
    and committed: "committed_service obs"
  shows "answer_at d turn = None"
    "ordinary_receipts (scheduler_at d) (packet_identity p) = None"
    "regulation_receipts (scheduler_at d) (packet_identity p) = None"
proof -
  have clear: "\<not> conflicting_receipt d turn p"
  proof
    assume "conflicting_receipt d turn p"
    with step have "obs = Compared_Attempt (Service_Result (Operational_Failure No_Effective_Opportunity))"
      by (auto simp: machine_step_def)
    with committed show False by simp
  qed
  have fresh: "answer_at d turn = None"
  proof (cases "answer_at d turn")
    case None
    then show ?thesis .
  next
    case (Some prior)
    with clear have "retained_answer d turn = Some p" "exact_saved_packet (scheduler_at d) p"
      by (simp_all add: conflicting_receipt_def)
    with service_trace_consumes_checked_compare(1)[OF step committed] have "obs = Replayed_Receipt p"
      by (auto simp: observe_sequence_def)
    with committed show ?thesis by simp
  qed
  from fresh clear show "answer_at d turn = None"
    "ordinary_receipts (scheduler_at d) (packet_identity p) = None"
    "regulation_receipts (scheduler_at d) (packet_identity p) = None"
    by (simp_all add: conflicting_receipt_def)
qed

lemma supersession_has_the_admitted_packet:
  assumes "run_machine E d (Read_Superseded q) = (Superseded True,t)"
  obtains p where
    "admitted_at d q = Some p"
    "packet_identity p = q"
    "\<not> ordinary_body (packet_contents p)" "permanently_stale (scheduler_at d) p"
    "regulation_receipts (scheduler_at d) q = None" "t = d"
proof -
  have result: "read_superseded (admitted_at d) (scheduler_at d) q (scheduler_at d) \<and> t = d"
    using assms by (simp only: run_machine.simps prod.inject machine_reply.inject) blast
  from result obtain p where
    "admitted_at d q = Some p" "packet_identity p = q"
    "\<not> ordinary_body (packet_contents p)" "permanently_stale (scheduler_at d) p"
    "regulation_receipts (scheduler_at d) q = None"
    unfolding read_superseded_def by blast
  moreover from result have "t = d" by simp
  ultimately show thesis by (rule that)
qed

end
