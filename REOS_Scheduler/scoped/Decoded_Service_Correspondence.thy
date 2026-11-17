theory Decoded_Service_Correspondence
  imports Scoped_Product_Target
begin

text \<open>Checked observations associate decoded queue indexes with the
  verified grant, rollback and context-update facts at the same read.
  The latter are inputs to the implementation target. A product adapter
  must verify their authority and their binding to the native compare
  token before constructing this view.\<close>

record decoded_cut =
  decoded_image :: sequencing_image_view
  current_priority_grants :: "packet set"
  current_rollback_facts :: rollback_state
  available_context_updates :: "(nat \<times> nat \<times> nat \<times> nat) set"

definition decoded_snapshot :: "decoded_cut \<Rightarrow> service_snapshot" where
  "decoded_snapshot view = (let image = decoded_image view;
      packet_at = (\<lambda>q. the (accepted_packet_index image q)) in
    \<lparr>store_cut = comparison_token image, observed_scheduler =
      \<lparr>rollback_context = current_rollback_facts view, signed_packets = verified_packet_bodies image,
         regulatory_grants = current_priority_grants view, verified_context_updates = available_context_updates view,
         ordinary_queue = map packet_at (pending_ordinary_ids image),
         regulatory_queue = map packet_at (pending_priority_ids image),
         dedup_ids = known_request_ids image, ordinary_receipts = ordinary_receipt_index image,
         regulation_receipts = regulation_receipt_index image,
         severity_now = image_case_level image, severity_limit = image_case_limit image\<rparr>\<rparr>)"

definition a_decoded_cut_represents :: "decoded_cut \<Rightarrow> scoped_machine \<Rightarrow> bool" where
  "a_decoded_cut_represents view d \<longleftrightarrow>
    dquencer_image_relation (decoded_image view) d \<and> decoded_snapshot view = committed_cut d"

lemma before_and_compare_use_the_same_exact_snapshot:
  assumes "a_decoded_cut_represents view d" "a_decoded_cut_represents view t"
  shows "committed_cut d = committed_cut t"
  using assms by (simp add: a_decoded_cut_represents_def)

datatype decoded_request =
    Incoming_Packet packet
  | Authenticated_Order service_turn packet
  | Current_Attempt decoded_cut service_turn packet
  | Context_Update nat nat nat nat
  | Read_Primary decoded_cut source_binding
  | Repair_Replica decoded_cut nat nat
  | Expire_Priority | Inspect_Supersession nat

fun decoded_request_action :: "decoded_request \<Rightarrow> machine_action" where
  "decoded_request_action (Incoming_Packet p) = Receive_Packet p"
| "decoded_request_action (Authenticated_Order t p) = Bind_Order t p"
| "decoded_request_action (Current_Attempt seen t p) = Attempt_At (decoded_snapshot seen) t p"
| "decoded_request_action (Context_Update time a k policy) = Change_Context time a k policy"
| "decoded_request_action (Read_Primary seen binding) = Import_At (decoded_snapshot seen) binding"
| "decoded_request_action (Repair_Replica seen i replica) = Repair_At (decoded_snapshot seen) i replica"
| "decoded_request_action Expire_Priority = Retire_Expired"
| "decoded_request_action (Inspect_Supersession i) = Read_Superseded i"

fun comparison_input_has_an_exact_snapshot :: "decoded_request \<Rightarrow> bool" where
  "comparison_input_has_an_exact_snapshot (Current_Attempt seen t p) =
    (\<exists>d. a_decoded_cut_represents seen d)"
| "comparison_input_has_an_exact_snapshot (Read_Primary seen binding) =
    (\<exists>d. a_decoded_cut_represents seen d)"
| "comparison_input_has_an_exact_snapshot (Repair_Replica seen i replica) =
    (\<exists>d. a_decoded_cut_represents seen d)"
| "comparison_input_has_an_exact_snapshot _ = True"

record observed_exchange =
  before_exchange :: decoded_cut
  submitted_operation :: decoded_request
  completed_observation :: projected_service_reply
  after_exchange :: decoded_cut

definition observed_exchange_represents ::
  "machine_evidence \<Rightarrow> observed_exchange \<Rightarrow> machine_event \<Rightarrow> bool" where
  "observed_exchange_represents E native e \<longleftrightarrow>
    a_decoded_cut_represents (before_exchange native) (source_state e)
    \<and> a_decoded_cut_represents (after_exchange native) (target_state e)
    \<and> comparison_input_has_an_exact_snapshot (submitted_operation native)
    \<and> decoded_request_action (submitted_operation native) = step_action e
    \<and> step_occurs (machine_step E) e
    \<and> completed_observation native = recorded_service_reply (decoded_image (after_exchange native)) (step_outcome e)"

definition observed_exchanges_are_a_machine_trace ::
  "machine_evidence \<Rightarrow> scoped_machine set \<Rightarrow> scoped_machine \<Rightarrow>
   observed_exchange list \<Rightarrow> machine_event list \<Rightarrow> scoped_machine \<Rightarrow> bool" where
  "observed_exchanges_are_a_machine_trace E carrier d observed events t \<longleftrightarrow>
    list_all2 (observed_exchange_represents E) observed events
    \<and> finite_trace (machine_step E) carrier d events t"

lemma every_decoded_exchange_in_the_history_is_a_checked_step:
  assumes "observed_exchanges_are_a_machine_trace E carrier d observed events t"
    "i < length events"
  shows "observed_exchange_represents E (observed ! i) (events ! i)"
  using assms by (auto simp: observed_exchanges_are_a_machine_trace_def intro: list_all2_nthD2)

lemma accepted_decoded_ingress_consumes_signature_and_unused_identity:
  assumes "observed_exchange_represents E native e"
    "submitted_operation native = Incoming_Packet p"
    "step_outcome e = Admission (Accepted q)"
  shows "p \<in> verified_packet_bodies (decoded_image (before_exchange native))"
    "packet_identity p \<notin> known_request_ids (decoded_image (before_exchange native))"
    "packet_fresh (scheduler_at (source_state e)) p"
    "accepted_packet_index (decoded_image (after_exchange native)) q = Some p"
    "completed_observation native = Stored_Admission p"
proof -
  from assms have received: "machine_step E (source_state e) (Receive_Packet p) (Admission (Accepted q)) (target_state e)"
    and image: "decoded_image (before_exchange native) = projected_image (source_state e)"
      "decoded_image (after_exchange native) = projected_image (target_state e)"
    and out: "completed_observation native =
      recorded_service_reply (decoded_image (after_exchange native)) (Admission (Accepted q))"
    by (auto simp: observed_exchange_represents_def a_decoded_cut_represents_def dquencer_image_relation_def step_occurs_def)
  from received obtain u where accepted: "scoped_submit (authority_facts E) (scheduler_at (source_state e)) p = (Accepted q,u)"
    and post: "target_state e = (write_scheduler (source_state e) u)
      \<lparr>admitted_at := (admitted_at (source_state e))(q \<mapsto> p)\<rparr>"
    by (auto simp: machine_step_def split: prod.splits transition_result.splits)
  from admitted_packet[OF scoped_acceptance_uses_normal_admission[OF accepted]] image(1)
  show "p \<in> verified_packet_bodies (decoded_image (before_exchange native))"
    "packet_identity p \<notin> known_request_ids (decoded_image (before_exchange native))"
    "packet_fresh (scheduler_at (source_state e)) p" by (simp_all add: projected_image_def)
  have saved: "accepted_packet_index (decoded_image (after_exchange native)) q = Some p"
    by (simp add: image(2) projected_image_def post)
  then show "accepted_packet_index (decoded_image (after_exchange native)) q = Some p" .
  from out saved show "completed_observation native = Stored_Admission p" by simp
qed

lemma unsigned_decoded_ingress_cannot_occupy_the_accepted_index:
  assumes "observed_exchange_represents E native e"
    "submitted_operation native = Incoming_Packet p"
    "p \<notin> verified_packet_bodies (decoded_image (before_exchange native))"
  shows "completed_observation native = Denied_Admission Signature_Failed"
    "decoded_image (after_exchange native) = decoded_image (before_exchange native)"
proof -
  from assms(1,2) have step:
    "machine_step E (source_state e) (Receive_Packet p) (step_outcome e) (target_state e)"
    and image: "decoded_image (before_exchange native) = projected_image (source_state e)"
      "decoded_image (after_exchange native) = projected_image (target_state e)"
    and reported: "completed_observation native =
      recorded_service_reply (decoded_image (after_exchange native)) (step_outcome e)"
    by (auto simp: observed_exchange_represents_def step_occurs_def a_decoded_cut_represents_def dquencer_image_relation_def)
  from image(1) assms(3) have "p \<notin> signed_packets (scheduler_at (source_state e))"
    by (simp add: projected_image_def)
  from failed_signature_leaves_the_id_available[OF this] have
    "run_machine E (source_state e) (Receive_Packet p) = (Admission (Rejected Signature_Failed),source_state e)"
    by (simp add: scheduler_step_def scoped_submit_def)
  from step this have "step_outcome e = Admission (Rejected Signature_Failed)" "target_state e = source_state e"
    by (auto simp: machine_step_def)
  with image reported show "completed_observation native = Denied_Admission Signature_Failed"
    "decoded_image (after_exchange native) = decoded_image (before_exchange native)" by simp_all
qed

lemma decoded_governed_commit_matches_the_current_approved_ledger_write:
  assumes "observed_exchange_represents E native e"
    "submitted_operation native = Current_Attempt seen turn p"
    "step_outcome e = Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Regulation q k))))"
    "packet_contents p = Execute_Governed_Rollback r ratification role_proof"
  shows "decoded_snapshot seen = decoded_snapshot (before_exchange native)"
    "next_regulation (authorized_view (authority_facts E) (observed_scheduler (decoded_snapshot seen))) = Some p"
    "checked_rollback (authority_facts E) (current_rollback_facts (before_exchange native)) r ratification role_proof =
      (Accepted q,current_rollback_facts (after_exchange native))"
    "completed_observation native = Stored_Regulation p"
proof -
  let ?d = "source_state e"
  let ?t = "target_state e"
  let ?obs = "Compared_Attempt (Service_Result (Internal (Served_Regulation q k)))"
  from assms have step: "machine_step E ?d (Attempt_At (decoded_snapshot seen) turn p) (Observed_Service ?obs) ?t"
    and image: "a_decoded_cut_represents (before_exchange native) ?d" "a_decoded_cut_represents (after_exchange native) ?t"
    and out: "completed_observation native =
      recorded_service_reply (decoded_image (after_exchange native)) (Observed_Service ?obs)"
    by (auto simp: observed_exchange_represents_def step_occurs_def)
  from service_trace_consumes_checked_compare(1)[OF step] have observed:
    "observe_sequence (authority_facts E) (active_signer E) (order_at ?d) (retained_answer ?d)
     (decoded_snapshot seen) (committed_cut ?d) turn p = (?obs,scheduler_at ?t)" by simp
  note actual = compare_commit_uses_the_exact_current_order[OF observed]
  show "decoded_snapshot seen = decoded_snapshot (before_exchange native)"
    using actual(1) image(1) by (simp add: a_decoded_cut_represents_def)
  obtain u where selected:
    "next_regulation (authorized_view (authority_facts E) (scheduler_at ?d)) = Some p"
    by (rule scoped_regulatory_effect[OF actual(4)]) (rule that; assumption)
  show "next_regulation (authorized_view (authority_facts E) (observed_scheduler (decoded_snapshot seen))) = Some p"
    using selected by (simp add: actual(1))
  from image have cuts: "decoded_snapshot (before_exchange native) = committed_cut ?d"
    "decoded_snapshot (after_exchange native) = committed_cut ?t"
    by (simp_all add: a_decoded_cut_represents_def)
  have rollback:
    "current_rollback_facts (before_exchange native) = rollback_context (scheduler_at ?d)"
    "current_rollback_facts (after_exchange native) = rollback_context (scheduler_at ?t)"
    using arg_cong[OF cuts(1), where f="\<lambda>s. rollback_context (observed_scheduler s)"]
      arg_cong[OF cuts(2), where f="\<lambda>s. rollback_context (observed_scheduler s)"]
    by (simp_all add: decoded_snapshot_def Let_def)
  show "checked_rollback (authority_facts E) (current_rollback_facts (before_exchange native)) r ratification role_proof =
      (Accepted q,current_rollback_facts (after_exchange native))"
    by (simp add: rollback a_scoped_governed_commit_uses_the_same_checked_rollback(4)[OF actual(4) assms(4)])
  from image(2) scoped_regulatory_commit_preserves_fifo(4)[OF actual(4)]
  have "regulation_receipt_index (decoded_image (after_exchange native)) q = Some p"
    by (simp add: a_decoded_cut_represents_def dquencer_image_relation_def projected_image_def)
  with out show "completed_observation native = Stored_Regulation p" by simp
qed

lemma decoded_checked_rotation_exposes_the_new_epoch_and_the_same_pending_packets:
  assumes "observed_exchange_represents E native e"
    "submitted_operation native = Context_Update time a k policy"
    "step_outcome e = Applied_Context (Internal Context_Advanced)"
  shows "image_authority_epoch (decoded_image (after_exchange native)) = a"
    "image_policy_epoch (decoded_image (after_exchange native)) k = policy"
    "pending_ordinary_ids (decoded_image (after_exchange native)) =
       pending_ordinary_ids (decoded_image (before_exchange native))"
proof -
  from assms have step: "machine_step E (source_state e) (Change_Context time a k policy)
      (Applied_Context (Internal Context_Advanced)) (target_state e)"
    and images: "decoded_image (before_exchange native) = projected_image (source_state e)"
      "decoded_image (after_exchange native) = projected_image (target_state e)"
    by (auto simp: observed_exchange_represents_def step_occurs_def a_decoded_cut_represents_def dquencer_image_relation_def)
  from a_checked_context_change_preserves_receipts_and_fences_stale_selection(2,3,4)[OF step]
  show "image_authority_epoch (decoded_image (after_exchange native)) = a"
    "image_policy_epoch (decoded_image (after_exchange native)) k = policy"
    "pending_ordinary_ids (decoded_image (after_exchange native)) =
       pending_ordinary_ids (decoded_image (before_exchange native))"
    by (simp_all add: images projected_image_def)
qed

definition decoded_view_for :: "scoped_machine \<Rightarrow> decoded_cut" where
  "decoded_view_for d = \<lparr>decoded_image = projected_image d,
    current_priority_grants = regulatory_grants (scheduler_at d),
    current_rollback_facts = rollback_context (scheduler_at d),
    available_context_updates = verified_context_updates (scheduler_at d)\<rparr>"

lemma the_decoded_comparison_rejects_a_different_grant_with_the_same_visible_image:
  defines "actual \<equiv> decoded_view_for before_rotation"
    and "substituted \<equiv> (decoded_view_for before_rotation)\<lparr>current_priority_grants := {}\<rparr>"
  shows "a_decoded_cut_represents actual before_rotation"
    "decoded_image substituted = decoded_image actual"
    "\<not> a_decoded_cut_represents substituted before_rotation"
proof -
  let ?s = Scheduler_Examples.priority_admitted
  have base: "scheduler_at before_rotation = ?s" by (simp add: before_rotation_def)
  have fields: "ordinary_queue ?s = [ordinary_packet]" "regulatory_queue ?s = [urgent_packet]"
    "regulatory_grants ?s = {urgent_packet}"
    by (simp_all add: Scheduler_Examples.priority_admitted_def Scheduler_Examples.ordinary_admitted_def
      scheduler_reduction packet_example)
  show "a_decoded_cut_represents actual before_rotation"
    by (simp add: a_decoded_cut_represents_def dquencer_image_relation_def indexing_preserves_the_queue_payloads_def
      decoded_snapshot_def decoded_view_for_def projected_image_def actual_def fields before_rotation_def
      ordinary_packet_def urgent_packet_def Let_def scheduler_state.surjective)
  show "decoded_image substituted = decoded_image actual" by (simp add: substituted_def actual_def)
  show "\<not> a_decoded_cut_represents substituted before_rotation"
  proof
    assume "a_decoded_cut_represents substituted before_rotation"
    then have "decoded_snapshot substituted = committed_cut before_rotation" by (simp add: a_decoded_cut_represents_def)
    then have "regulatory_grants (observed_scheduler (decoded_snapshot substituted)) = regulatory_grants (scheduler_at before_rotation)"
      by simp
    with base fields show False
      by (simp add: decoded_snapshot_def substituted_def Let_def)
  qed
qed

end
