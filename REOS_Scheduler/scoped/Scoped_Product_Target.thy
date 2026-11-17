theory Scoped_Product_Target
  imports Scoped_Integration
begin

section \<open>Admission feeds the exact FIFO progress result\<close>

theorem rejected_same_id_spam_leaves_the_original_request_eligible_for_exact_service:
  fixes E :: machine_evidence
  assumes coherent: "coherent_ordinary_queue (scheduler_at d)"
    and attack: "spoof \<notin> signed_packets (scheduler_at d)" "packet_identity spoof = packet_identity p"
    and real: "p \<in> signed_packets (scheduler_at d)"
       "packet_identity p \<notin> dedup_ids (scheduler_at d)" "packet_fresh (scheduler_at d) p" "ordinary_body (packet_contents p)"
    and begin_tail: "source_state (events 0) =
      snd (run_machine E (snd (run_machine E d (Receive_Packet spoof))) (Receive_Packet p))"
    and trace: "infinite_run (machine_step E) initial carrier events"
    and finite_priority: "finite {i. priority_commit (step_outcome (events i))}"
    and available: "\<And>i. (\<And>j. i \<le> j \<Longrightarrow>
      ordinary_queue (scheduler_at (source_state (events j))) \<noteq> []) \<Longrightarrow>
      \<exists>j\<ge>i. receives_fresh_choice E (offered j) (events j)"
  obtains j turn where
    "run_machine E d (Receive_Packet spoof) = (Admission (Rejected Signature_Failed),d)"
    "admitted_at (source_state (events 0)) (packet_identity spoof) = Some p"
    "ordinary_commit_id (step_outcome (events j)) = Some (packet_identity spoof)"
    "ordinary_receipts (scheduler_at (target_state (events j))) (packet_identity spoof) = Some p"
    "run_machine E (target_state (events j)) (Attempt_At retry_cut turn p) =
      (Observed_Service (Replayed_Receipt p),target_state (events j))"
proof -
  let ?d0 = "source_state (events 0)"
  let ?s = "scheduler_at d"
  let ?id = "packet_identity p"
  have refused: "run_machine E d (Receive_Packet spoof) = (Admission (Rejected Signature_Failed),d)"
    using failed_signature_leaves_the_id_available[OF attack(1)] by (simp add: scheduler_step_def scoped_submit_def)
  from real have admitted: "admit ?s p = (Accepted ?id, enqueue_packet ?s p)"
    by (simp add: admit_def)
  from real(4) have allowed: "policy_allows (authority_facts E) (rollback_context ?s) (packet_contents p)"
    by (cases "packet_contents p") simp_all
  let ?after = "(write_scheduler d (enqueue_packet ?s p))\<lparr>admitted_at := (admitted_at d)(?id \<mapsto> p)\<rparr>"
  have accepted: "run_machine E d (Receive_Packet p) = (Admission (Accepted ?id),?after)"
    by (simp add: admitted allowed scoped_submit_def)
  from begin_tail have state: "?d0 = ?after"
    by (simp only: refused snd_conv accepted)
  have bound: "admitted_at ?d0 (packet_identity spoof) = Some p" by (simp add: state attack(2))
  have scoped_admit: "machine_step E d (Receive_Packet p) (Admission (Accepted ?id)) ?d0"
    by (simp only: accepted state machine_step_def)
  have coh: "coherent_ordinary_queue (scheduler_at ?d0)" by (rule scoped_fifo_maintains_coherence[OF scoped_admit coherent])
  have pending: "p \<in> set (ordinary_queue (scheduler_at ?d0))"
    by (simp add: state real(4) enqueue_packet_def Let_def)
  obtain j turn where hit: "ordinary_commit_id (step_outcome (events j)) = Some ?id"
    and saved: "ordinary_receipts (scheduler_at (target_state (events j))) ?id = Some p"
    and replay: "run_machine E (target_state (events j)) (Attempt_At retry_cut turn p) =
      (Observed_Service (Replayed_Receipt p),target_state (events j))"
  proof (rule actual_scoped_progress_returns_the_original_order_and_its_retry[OF trace coh pending finite_priority, where offered=offered])
    fix i
    assume work: "\<And>k. i \<le> k \<Longrightarrow> ordinary_queue (scheduler_at (source_state (events k))) \<noteq> []"
    show "\<exists>k\<ge>i. receives_fresh_choice E (offered k) (events k)" by (rule available[OF work])
  next
    fix j turn
    assume "step_action (events j) = Attempt_At (committed_cut (source_state (events j))) turn p"
      "(turn,p) \<in> certified_order_pairs E"
    assume observed: "ordinary_commit_id (step_outcome (events j)) = Some ?id"
      "ordinary_receipts (scheduler_at (target_state (events j))) ?id = Some p"
      "run_machine E (target_state (events j)) (Attempt_At retry_cut turn p) =
        (Observed_Service (Replayed_Receipt p),target_state (events j))"
    show thesis by (rule that[OF observed])
  qed
  show thesis using hit saved by (intro that[OF refused bound _ _ replay]) (simp_all add: attack(2))
qed

theorem the_actual_rollback_commit_checks_validator_and_emergency_certificates:
  assumes step: "machine_step E d (Attempt_At expected turn p)
    (Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Regulation q k))))) t"
    and body: "packet_contents p = Execute_Governed_Rollback r ratification role_proof"
  shows "requested_role r = Validator \<Longrightarrow>
    matches_certificate (rollback_context (scheduler_at d)) r Validation_Failure Validator role_proof"
    "requested_role r = Emergency \<Longrightarrow>
    matches_certificate (rollback_context (scheduler_at d)) r Emergency_Activation Emergency role_proof"
    "requested_role r = Governance \<or> verified_origin (authority_facts E) r = Some Regulatory_Review
      \<Longrightarrow> r \<in> collective_decisions (authority_facts E)"
    "request_scope r = Wide \<Longrightarrow>
      matches_certificate (rollback_context (scheduler_at d)) r Governance_Ratification Governance ratification"
    "run_machine E t (Attempt_At retry_cut turn p) = (Observed_Service (Replayed_Receipt p),t)"
proof -
  let ?obs = "Compared_Attempt (Service_Result (Internal (Served_Regulation q k)))"
  have wrote: "committed_service ?obs" by simp
  note observed = service_trace_consumes_checked_compare(1)[OF step wrote]
  note actual = compare_commit_uses_the_exact_current_order(4)[OF observed]
  note rollback = a_scoped_governed_commit_uses_the_same_checked_rollback(5)[OF actual body]
  have live: "role_proof_ok (rollback_context (scheduler_at d)) r (requested_role r) role_proof"
    by (rule rollback_authority_contract[OF rollback]) assumption
  from live show "requested_role r = Validator \<Longrightarrow>
    matches_certificate (rollback_context (scheduler_at d)) r Validation_Failure Validator role_proof"
    "requested_role r = Emergency \<Longrightarrow>
    matches_certificate (rollback_context (scheduler_at d)) r Emergency_Activation Emergency role_proof"
    by simp_all
  note combined = the_same_certified_rollback_preserves_scope_at_commit_and_retry[OF step body]
  show "requested_role r = Governance \<or> verified_origin (authority_facts E) r = Some Regulatory_Review
      \<Longrightarrow> r \<in> collective_decisions (authority_facts E)" by (rule combined(2))
  show "request_scope r = Wide \<Longrightarrow>
      matches_certificate (rollback_context (scheduler_at d)) r Governance_Ratification Governance ratification"
    by (rule combined(3))
  show "run_machine E t (Attempt_At retry_cut turn p) = (Observed_Service (Replayed_Receipt p),t)"
    by (rule combined(5))
qed

theorem a_checked_context_change_preserves_receipts_and_fences_stale_selection:
  assumes wrote: "machine_step E d (Change_Context time authority k policy)
      (Applied_Context (Internal Context_Advanced)) t"
  shows "(time, authority, k, policy) \<in> exact_context_updates (authority_facts E)"
    "authority_epoch (rollback_context (scheduler_at t)) = authority"
    "policy_epoch (rollback_context (scheduler_at t)) k = policy"
    "ordinary_queue (scheduler_at t) = ordinary_queue (scheduler_at d)"
    "ordinary_receipts (scheduler_at t) = ordinary_receipts (scheduler_at d)"
    "packet_authority_epoch p \<noteq> authority \<or>
       (regulatory_case (packet_contents p) = k \<and> packet_policy_epoch p \<noteq> policy)
       \<Longrightarrow> next_regulation (authorized_view (authority_facts E) (scheduler_at t)) \<noteq> Some p"
proof -
  let ?s = "scheduler_at d"
  let ?r = "rollback_context ?s"
  obtain u where did: "checked_advance (authority_facts E) ?r time authority k policy =
      (Internal Context_Advanced,u)"
    and post: "scheduler_at t = ?s\<lparr>rollback_context := u\<rparr>"
    using wrote by (auto simp: machine_step_def split: prod.splits transition_result.splits rollback_internal.splits)
  from did show "(time, authority, k, policy) \<in> exact_context_updates (authority_facts E)"
    by (auto simp: checked_advance_def split: if_splits)
  from did have "authority_epoch u = authority" "policy_epoch u k = policy"
    by (auto simp: checked_advance_def split: if_splits)
  then have live: "authority_epoch (rollback_context (scheduler_at t)) = authority"
    "policy_epoch (rollback_context (scheduler_at t)) k = policy" by (simp_all add: post)
  then show "authority_epoch (rollback_context (scheduler_at t)) = authority"
    "policy_epoch (rollback_context (scheduler_at t)) k = policy" by simp_all
  show "ordinary_queue (scheduler_at t) = ordinary_queue ?s"
    "ordinary_receipts (scheduler_at t) = ordinary_receipts ?s" by (simp_all add: post)
  show "packet_authority_epoch p \<noteq> authority \<or>
       (regulatory_case (packet_contents p) = k \<and> packet_policy_epoch p \<noteq> policy)
       \<Longrightarrow> next_regulation (authorized_view (authority_facts E) (scheduler_at t)) \<noteq> Some p"
  proof -
    assume stale: "packet_authority_epoch p \<noteq> authority \<or>
      (regulatory_case (packet_contents p) = k \<and> packet_policy_epoch p \<noteq> policy)"
    with live have "\<not> ready_regulation (authorized_view (authority_facts E) (scheduler_at t)) p"
      by (auto simp: ready_regulation_def regulatory_effect_def packet_fresh_def authorized_view_def)
    then show "next_regulation (authorized_view (authority_facts E) (scheduler_at t)) \<noteq> Some p"
      by (auto dest: selected_regulation_ready(1))
  qed
qed

definition policy_only_evidence :: machine_evidence where
  "policy_only_evidence = rotation_evidence\<lparr>authority_facts :=
    (authority_facts rotation_evidence)\<lparr>exact_context_updates := {(5,4,9,9)}\<rparr>\<rparr>"

lemma exact_policy_only_rotation_uses_the_same_run_and_preserves_the_original_fifo:
  obtains t where "run_machine policy_only_evidence before_rotation (Change_Context 5 4 9 9) =
    (Applied_Context (Internal Context_Advanced), t)"
    "authority_epoch (rollback_context (scheduler_at t)) = 4"
    "policy_epoch (rollback_context (scheduler_at t)) 9 = 9"
    "next_regulation (authorized_view (authority_facts policy_only_evidence) (scheduler_at t)) \<noteq> Some urgent_packet"
    "ordinary_queue (scheduler_at t) = [ordinary_packet]"
proof -
  let ?E = policy_only_evidence
  let ?d = before_rotation
  have advance: "run_machine ?E ?d (Change_Context 5 4 9 9) =
    (Applied_Context (Internal Context_Advanced), write_scheduler ?d new_policy)"
    by (simp add: policy_only_evidence_def rotation_evidence_def case_evidence_def before_rotation_def
      checked_advance_def new_policy_def scheduler_reduction Scheduler_Examples.priority_admitted_def
      Scheduler_Examples.ordinary_admitted_def packet_example)
  then have step: "machine_step ?E ?d (Change_Context 5 4 9 9)
    (Applied_Context (Internal Context_Advanced)) (write_scheduler ?d new_policy)"
    by (simp only: machine_step_def)
  have ordinary: "ordinary_queue (scheduler_at ?d) = [ordinary_packet]"
    by (simp add: before_rotation_def Scheduler_Examples.priority_admitted_def
      Scheduler_Examples.ordinary_admitted_def scheduler_reduction packet_example)
  have old: "regulatory_case (packet_contents urgent_packet) = 9 \<and> packet_policy_epoch urgent_packet \<noteq> 9"
    by (simp add: urgent_packet_def ordinary_packet_def)
  from a_checked_context_change_preserves_receipts_and_fences_stale_selection[OF step] ordinary old
  show thesis by (intro that[OF advance]) auto
qed

theorem a_waiting_request_after_an_actual_checked_rotation_finishes_with_its_original_receipt:
  assumes rotated: "machine_step E d (Change_Context time authority k policy)
      (Applied_Context (Internal Context_Advanced)) t"
    and initial: "source_state (events 0) = t"
    and coherent: "coherent_ordinary_queue (scheduler_at d)"
    and pending: "p \<in> set (ordinary_queue (scheduler_at d))"
    and trace: "infinite_run (machine_step E) entry carrier events"
    and finite_priority: "finite {i. priority_commit (step_outcome (events i))}"
    and available: "\<And>i. (\<And>j. i \<le> j \<Longrightarrow>
      ordinary_queue (scheduler_at (source_state (events j))) \<noteq> []) \<Longrightarrow>
      \<exists>j\<ge>i. receives_fresh_choice E (offered j) (events j)"
  shows "\<exists>j. ordinary_commit_id (step_outcome (events j)) = Some (packet_identity p)
    \<and> ordinary_receipts (scheduler_at (target_state (events j))) (packet_identity p) = Some p"
proof -
  have same: "ordinary_queue (scheduler_at t) = ordinary_queue (scheduler_at d)"
    by (rule a_checked_context_change_preserves_receipts_and_fences_stale_selection(4)[OF rotated])
  from scoped_fifo_maintains_coherence[OF rotated coherent] initial
  have coh: "coherent_ordinary_queue (scheduler_at (source_state (events 0)))" by simp
  from same pending initial have wait: "p \<in> set (ordinary_queue (scheduler_at (source_state (events 0))))" by simp
  show ?thesis
  proof (rule an_exact_ordinary_packet_completes_in_the_scoped_run[OF trace coh wait finite_priority, where offered=offered])
    fix i
    assume work: "\<And>j. i \<le> j \<Longrightarrow> ordinary_queue (scheduler_at (source_state (events j))) \<noteq> []"
    show "\<exists>j\<ge>i. receives_fresh_choice E (offered j) (events j)" by (rule available[OF work])
  qed
qed

section \<open>The implementation refinement target\<close>

text \<open>The comparison token below is the logical projection of an exact
decoded store observation. Native revision and exact compared bytes must
jointly identify that observation. Extracting views from a deployed Rust
image, authenticating bytes, associating external ledger facts, and
linearizing a native compare are separate producer obligations.\<close>

record sequencing_image_view =
  comparison_token :: nat
  image_authority_epoch :: nat
  image_policy_epoch :: "nat \<Rightarrow> nat"
  image_consensus_time :: nat
  pending_ordinary_ids :: "nat list"
  pending_priority_ids :: "nat list"
  verified_packet_bodies :: "packet set"
  known_request_ids :: "nat set"
  image_case_level :: "nat \<Rightarrow> nat"
  image_case_limit :: "nat \<Rightarrow> nat"
  image_rollback_credit :: "nat \<Rightarrow> nat"
  accepted_packet_index :: "nat \<Rightarrow> packet option"
  verified_order_index :: "service_turn \<Rightarrow> packet option"
  committed_order_index :: "service_turn \<Rightarrow> packet option"
  ordinary_receipt_index :: "nat \<Rightarrow> packet option"
  regulation_receipt_index :: "nat \<Rightarrow> packet option"
  verified_cell_view :: "ledger_cell \<Rightarrow> nat"

definition projected_image :: "scoped_machine \<Rightarrow> sequencing_image_view" where
  "projected_image d =
   \<lparr>comparison_token = store_cut (committed_cut d),
    image_authority_epoch = authority_epoch (rollback_context (scheduler_at d)),
    image_policy_epoch = policy_epoch (rollback_context (scheduler_at d)),
    image_consensus_time = consensus_time (rollback_context (scheduler_at d)),
    pending_ordinary_ids = map packet_identity (ordinary_queue (scheduler_at d)),
    pending_priority_ids = map packet_identity (regulatory_queue (scheduler_at d)),
    verified_packet_bodies = signed_packets (scheduler_at d),
    known_request_ids = dedup_ids (scheduler_at d),
    image_case_level = severity_now (scheduler_at d), image_case_limit = severity_limit (scheduler_at d),
    image_rollback_credit = case_remaining (rollback_context (scheduler_at d)),
    accepted_packet_index = admitted_at d, verified_order_index = order_at d, committed_order_index = answer_at d,
    ordinary_receipt_index = ordinary_receipts (scheduler_at d), regulation_receipt_index = regulation_receipts (scheduler_at d),
    verified_cell_view = cell_value (rollback_context (scheduler_at d))\<rparr>"

definition indexing_preserves_the_queue_payloads :: "sequencing_image_view \<Rightarrow> scoped_machine \<Rightarrow> bool" where
  "indexing_preserves_the_queue_payloads view d \<longleftrightarrow>
    (\<forall>p \<in> set (ordinary_queue (scheduler_at d)) \<union> set (regulatory_queue (scheduler_at d)).
       accepted_packet_index view (packet_identity p) = Some p)"

definition dquencer_image_relation :: "sequencing_image_view \<Rightarrow> scoped_machine \<Rightarrow> bool" where
  "dquencer_image_relation view d \<longleftrightarrow> view = projected_image d \<and> indexing_preserves_the_queue_payloads view d"

datatype projected_service_reply =
    Stored_Ordinary packet | Stored_Regulation packet | Read_Receipt packet
  | Failed_Compare | Denied_Action
  | Stored_Admission packet | Denied_Admission scheduler_denial
  | Verified_Context nat "nat \<Rightarrow> nat" nat | No_Context_Write
  | Source_Reply rollback_result | Replica_Reply rollback_result
  | Order_Registered | Order_Kept | Outdated_Order | Pending_Expired | Supersession bool

fun recorded_service_reply :: "sequencing_image_view \<Rightarrow> machine_reply \<Rightarrow> projected_service_reply" where
  "recorded_service_reply view (Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Ordinary q))))) =
    (case ordinary_receipt_index view q of Some p \<Rightarrow> Stored_Ordinary p | None \<Rightarrow> Denied_Action)"
| "recorded_service_reply view (Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Regulation q k))))) =
    (case regulation_receipt_index view q of Some p \<Rightarrow> Stored_Regulation p | None \<Rightarrow> Denied_Action)"
| "recorded_service_reply _ (Observed_Service (Replayed_Receipt p)) = Read_Receipt p"
| "recorded_service_reply _ (Observed_Service (Compared_Attempt Compare_Conflict)) = Failed_Compare"
| "recorded_service_reply view (Admission (Accepted q)) =
    (case accepted_packet_index view q of Some p \<Rightarrow> Stored_Admission p | None \<Rightarrow> Denied_Action)"
| "recorded_service_reply _ (Admission (Rejected reason)) = Denied_Admission reason"
| "recorded_service_reply view (Applied_Context (Internal Context_Advanced)) =
    Verified_Context (image_authority_epoch view) (image_policy_epoch view) (image_consensus_time view)"
| "recorded_service_reply _ (Applied_Context _) = No_Context_Write"
| "recorded_service_reply _ (Imported_Record reply) = Source_Reply reply"
| "recorded_service_reply _ (Repaired_Replica reply) = Replica_Reply reply"
| "recorded_service_reply _ Registered_Order = Order_Registered"
| "recorded_service_reply _ Kept_Order = Order_Kept"
| "recorded_service_reply _ Refused_Order = Outdated_Order"
| "recorded_service_reply _ Retired_Expired = Pending_Expired"
| "recorded_service_reply _ (Superseded status) = Supersession status"
| "recorded_service_reply _ _ = Denied_Action"

definition dquencer_service_relation ::
  "machine_evidence \<Rightarrow> sequencing_image_view \<Rightarrow> machine_action \<Rightarrow> projected_service_reply \<Rightarrow> sequencing_image_view \<Rightarrow> bool" where
  "dquencer_service_relation E before action wire_reply after \<longleftrightarrow>
    (\<exists>d t obs expected turn p.
      dquencer_image_relation before d \<and> dquencer_image_relation after t
      \<and> action = Attempt_At expected turn p \<and> machine_step E d action (Observed_Service obs) t
      \<and> wire_reply = recorded_service_reply after (Observed_Service obs))"

definition dquencer_history_relation ::
  "machine_evidence \<Rightarrow> scoped_machine set \<Rightarrow> scoped_machine \<Rightarrow> machine_event list
    \<Rightarrow> scoped_machine \<Rightarrow> sequencing_image_view list \<Rightarrow> projected_service_reply list \<Rightarrow> bool" where
  "dquencer_history_relation E carrier d events t frames replies \<longleftrightarrow>
    (finite_trace (machine_step E) carrier d events t \<and> length frames = Suc (length events)
      \<and> length replies = length events
      \<and> dquencer_image_relation (hd frames) d \<and> dquencer_image_relation (last frames) t
      \<and> (\<forall>i < length events.
        dquencer_image_relation (frames ! i) (source_state (events ! i))
        \<and> dquencer_image_relation (frames ! Suc i) (target_state (events ! i))
        \<and> replies ! i = recorded_service_reply (frames ! Suc i) (step_outcome (events ! i))))"

lemma a_compare_failure_does_not_report_a_new_image:
  assumes "dquencer_service_relation E before action Failed_Compare after"
  shows "before = after"
proof -
  from assms obtain d t obs expected turn p where image:
    "dquencer_image_relation before d" "dquencer_image_relation after t"
    and step: "machine_step E d (Attempt_At expected turn p) (Observed_Service obs) t"
    and failed: "recorded_service_reply after (Observed_Service obs) = Failed_Compare"
    by (auto simp: dquencer_service_relation_def)
  from failed have obs: "obs = Compared_Attempt Compare_Conflict"
    by (cases obs rule: committed_service.cases) (auto split: option.splits)
  from step obs have "t = d" by (auto intro: service_attempt_without_a_commit_is_a_read)
  from image this show ?thesis by (simp add: dquencer_image_relation_def)
qed

lemma projected_served_request_names_the_same_attested_order:
  assumes run: "step_occurs (machine_step E) e"
    and served: "ordinary_commit_id (step_outcome e) = Some (packet_identity p)"
    and saved: "ordinary_receipts (scheduler_at (target_state e)) (packet_identity p) = Some p"
    and before: "dquencer_image_relation first (source_state e)"
    and after: "dquencer_image_relation next_image (target_state e)"
  obtains turn where "(turn,p) \<in> certified_order_pairs E"
    "dquencer_service_relation E first (step_action e) (Stored_Ordinary p) next_image"
proof -
  obtain turn where action:
    "step_action e = Attempt_At (committed_cut (source_state e)) turn p"
    and certified: "(turn,p) \<in> certified_order_pairs E"
    by (rule a_committed_ordinary_receipt_names_the_certified_order_in_that_step[OF run served saved])
      (rule that; assumption)
  from served have outcome: "step_outcome e =
    Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Ordinary (packet_identity p)))))"
    by (cases "step_outcome e" rule: ordinary_commit_id.cases) auto
  from after saved have "ordinary_receipt_index next_image (packet_identity p) = Some p"
    by (simp add: dquencer_image_relation_def projected_image_def)
  with action run outcome before after have
    "dquencer_service_relation E first (step_action e) (Stored_Ordinary p) next_image"
    unfolding dquencer_service_relation_def
    by (intro exI[of _ "source_state e"] exI[of _ "target_state e"]) (auto simp: step_occurs_def)
  from certified this show thesis by (rule that)
qed

theorem the_recorded_history_names_the_attested_commit_and_exact_receipt:
  assumes trace: "dquencer_history_relation E carrier d events t frames replies"
    and index: "i < length events"
    and served: "ordinary_commit_id (step_outcome (events ! i)) = Some (packet_identity p)"
    and exact: "ordinary_receipts (scheduler_at (target_state (events ! i))) (packet_identity p) = Some p"
  obtains turn where "replies ! i = Stored_Ordinary p"
    "(turn,p) \<in> certified_order_pairs E"
    "dquencer_service_relation E (frames ! i) (step_action (events ! i)) (replies ! i) (frames ! Suc i)"
proof -
  let ?e = "events ! i"
  from trace index have native: "finite_trace (machine_step E) carrier d events t"
    and before: "dquencer_image_relation (frames ! i) (source_state ?e)"
    and after: "dquencer_image_relation (frames ! Suc i) (target_state ?e)"
    and appears: "replies ! i = recorded_service_reply (frames ! Suc i) (step_outcome ?e)"
    by (auto simp: dquencer_history_relation_def)
  from each_event_in_a_machine_trace_occurs[OF native nth_mem[OF index]]
  have happened: "step_occurs (machine_step E) ?e" .
  obtain turn where attested: "(turn,p) \<in> certified_order_pairs E"
    and wire: "dquencer_service_relation E (frames ! i) (step_action ?e) (Stored_Ordinary p) (frames ! Suc i)"
    by (rule projected_served_request_names_the_same_attested_order[OF happened served exact before after])
      (rule that; assumption)
  from served have response: "step_outcome ?e =
      Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Ordinary (packet_identity p)))))"
    by (cases "step_outcome ?e" rule: ordinary_commit_id.cases) auto
  from after exact have receipt: "ordinary_receipt_index (frames ! Suc i) (packet_identity p) = Some p"
    by (simp add: dquencer_image_relation_def projected_image_def)
  have projected: "replies ! i = Stored_Ordinary p" by (simp add: appears response receipt)
  from attested wire projected show thesis by (intro that[of turn]) simp_all
qed

definition target_fixture_pending :: scoped_machine where
  "target_fixture_pending = initial_spam_cut\<lparr>
    committed_cut := \<lparr>store_cut = 2, observed_scheduler = Scheduler_Examples.ordinary_admitted\<rparr>,
    order_at := (\<lambda>turn. if turn = ordinary_turn then Some ordinary_packet else None),
    admitted_at := (\<lambda>q. if q = 101 then Some ordinary_packet else None)\<rparr>"

definition target_fixture_done :: scoped_machine where
  "target_fixture_done = snd (run_machine case_evidence target_fixture_pending
    (Attempt_At (committed_cut target_fixture_pending) ordinary_turn ordinary_packet))"

lemma a_valid_index_image_distinguishes_a_commit_from_a_failed_comparison:
  "dquencer_service_relation case_evidence (projected_image target_fixture_pending)
    (Attempt_At (committed_cut target_fixture_pending) ordinary_turn ordinary_packet)
    (Stored_Ordinary ordinary_packet) (projected_image target_fixture_done)"
  "dquencer_service_relation case_evidence (projected_image target_fixture_pending)
    (Attempt_At ((committed_cut target_fixture_pending)\<lparr>store_cut := 1\<rparr>) ordinary_turn ordinary_packet)
    Failed_Compare (projected_image target_fixture_pending)"
proof -
  let ?d = target_fixture_pending
  let ?p = ordinary_packet
  let ?turn = ordinary_turn
  let ?s = Scheduler_Examples.ordinary_admitted
  let ?t = "?s\<lparr>ordinary_queue := [], ordinary_receipts := (ordinary_receipts ?s)(101 \<mapsto> ?p)\<rparr>"
  let ?obs = "Compared_Attempt (Service_Result (Internal (Served_Ordinary 101)))"
  have fields: "ordinary_queue ?s = [?p]" "regulatory_queue ?s = []"
    "ordinary_receipts ?s 101 = None" "regulation_receipts ?s 101 = None" "authority_epoch (rollback_context ?s) = 4"
    by (simp_all add: Scheduler_Examples.ordinary_admitted_def scheduler_reduction packet_example)
  have plan: "scoped_service (authority_facts case_evidence) (active_signer case_evidence)
      (signed_packets_by_turn (order_at ?d)) ?s ?turn ?p = (Internal (Served_Ordinary 101),?t)"
    by (simp add: target_fixture_pending_def case_evidence_def ordinary_turn_def local_governance_turn_def
      signed_packets_by_turn_def scoped_service_def authorized_view_def planned_def qualified_turn_def
      schedule_contract next_regulation_def serve_ordinary_def ordinary_packet_def fields Let_def)
  have ready: "scheduler_at ?d = ?s" by (simp add: target_fixture_pending_def)
  have fresh: "answer_at ?d ?turn = None"
    by (simp add: target_fixture_pending_def initial_spam_cut_def machine_start_def)
  have valid: "(?turn,?p) \<in> certified_order_pairs case_evidence" by (simp add: case_evidence_def)
  have clean: "\<not> conflicting_receipt ?d ?turn ?p"
    by (simp add: conflicting_receipt_def fresh ready ordinary_packet_def fields)
  let ?done = "(write_scheduler ?d ?t)\<lparr>answer_at := (answer_at ?d)(?turn \<mapsto> ?p)\<rparr>"
  have commit: "run_machine case_evidence ?d (Attempt_At (committed_cut ?d) ?turn ?p) =
      (Observed_Service ?obs,?done)"
    by (simp add: plan ready fresh valid clean observe_sequence_def try_service_at_def retained_answer_def)
  from commit have installed: "target_fixture_done = ?done" by (simp add: target_fixture_done_def)
  have before_image: "dquencer_image_relation (projected_image ?d) ?d"
    by (simp add: dquencer_image_relation_def indexing_preserves_the_queue_payloads_def projected_image_def
      target_fixture_pending_def ordinary_packet_def fields)
  have after_image: "dquencer_image_relation (projected_image target_fixture_done) target_fixture_done"
    by (simp add: dquencer_image_relation_def indexing_preserves_the_queue_payloads_def projected_image_def installed fields)
  have actual_step: "machine_step case_evidence ?d (Attempt_At (committed_cut ?d) ?turn ?p)
      (Observed_Service ?obs) target_fixture_done"
    by (simp only: machine_step_def commit installed)
  have projected: "recorded_service_reply (projected_image target_fixture_done) (Observed_Service ?obs) = Stored_Ordinary ?p"
    by (simp add: projected_image_def installed)
  show "dquencer_service_relation case_evidence (projected_image ?d)
      (Attempt_At (committed_cut ?d) ?turn ?p) (Stored_Ordinary ?p) (projected_image target_fixture_done)"
    unfolding dquencer_service_relation_def
    apply (rule exI[of _ ?d])
    apply (rule exI[of _ target_fixture_done])
    apply (rule exI[of _ ?obs])
    apply (rule exI[of _ "committed_cut ?d"])
    apply (rule exI[of _ ?turn])
    apply (rule exI[of _ ?p])
    by (simp add: before_image after_image actual_step projected del: recorded_service_reply.simps)
  let ?old = "(committed_cut ?d)\<lparr>store_cut := 1\<rparr>"
  have stale: "?old \<noteq> committed_cut ?d" by (simp add: target_fixture_pending_def)
  have compare: "try_service_at (authority_facts case_evidence) (active_signer case_evidence) (order_at ?d)
     ?old (committed_cut ?d) ?turn ?p = (Compare_Conflict,scheduler_at ?d)"
    by (rule changed_read_cut_compares_before_service[OF stale])
  have no_replay: "retained_answer ?d ?turn = None" by (simp add: retained_answer_def fresh)
  have observation: "observe_sequence (authority_facts case_evidence) (active_signer case_evidence) (order_at ?d)
     (retained_answer ?d) ?old (committed_cut ?d) ?turn ?p =
       (Compared_Attempt Compare_Conflict,scheduler_at ?d)"
    unfolding observe_sequence_def
    apply (subst compare)
    by (simp add: no_replay)
  have conflict: "run_machine case_evidence ?d (Attempt_At ?old ?turn ?p) =
      (Observed_Service (Compared_Attempt Compare_Conflict),?d)"
    apply (simp only: run_machine.simps)
    apply (subst observation)
    by (simp add: valid clean)
  have failed_step: "machine_step case_evidence ?d (Attempt_At ?old ?turn ?p)
      (Observed_Service (Compared_Attempt Compare_Conflict)) ?d"
    by (simp only: machine_step_def conflict)
  show "dquencer_service_relation case_evidence (projected_image ?d)
      (Attempt_At ?old ?turn ?p) Failed_Compare (projected_image ?d)"
    unfolding dquencer_service_relation_def
    apply (rule exI[of _ ?d])
    apply (rule exI[of _ ?d])
    apply (rule exI[of _ "Compared_Attempt Compare_Conflict"])
    apply (rule exI[of _ ?old])
    apply (rule exI[of _ ?turn])
    apply (rule exI[of _ ?p])
    apply (intro conjI)
    apply (rule before_image)
    apply (rule before_image)
    apply (rule refl)
    apply (rule failed_step)
    by simp
qed

end
