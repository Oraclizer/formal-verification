theory Exactly_Once
  imports Propagation_Queue
begin

datatype collection_reply = Collected product_outcome | Collection_Waiting | Collection_Rejected

definition observe_collection where
  "observe_collection verified who call_id payload s =
    (if \<not> result_access_bound verified who call_id payload s then Collection_Rejected
     else if call_local_status (product_calls (outcome_source s)) \<noteq> Endpoint_Up then Collection_Waiting
     else case outcome_entries s call_id of None \<Rightarrow> Collection_Waiting
      | Some recorded \<Rightarrow> if result_payload recorded \<noteq> payload then Collection_Rejected
        else if result_completion_ready recorded s then Collected (result_outcome recorded) else Collection_Waiting)"

lemma conflicting_payload_is_observably_rejected:
  assumes "outcome_entries s call_id = Some recorded" "result_payload recorded \<noteq> payload"
    "call_local_status (product_calls (outcome_source s)) = Endpoint_Up"
  shows "observe_collection verified who call_id payload s = Collection_Rejected"
  using assms by (simp add: observe_collection_def)

definition settlement_snapshot where
  "settlement_snapshot s = (authoritative_outcome_snapshot (origin_outcomes (settlement_primary s)),
    origin_debits (settlement_primary s), origin_decisions (settlement_primary s),
    settlement_target s, settlement_jobs s)"

definition update_settlement_outcomes where
  "update_settlement_outcomes outcomes s = s\<lparr>settlement_primary := (settlement_primary s)
    \<lparr>origin_outcomes := outcomes\<rparr>\<rparr>"

datatype exact_action =
    Exact_Submit lock_entry product_principal client_call_id product_call_payload
  | Exact_Collect product_principal client_call_id product_call_payload
  | Exact_Install product_principal nat "(nat \<times> lock_context) list" "product_session_id \<Rightarrow> product_session_binding option"
  | Exact_Link authority_connection
  | Exact_Crash
  | Exact_Recover "settlement_world option"
  | Exact_Enqueue source_key
  | Exact_Dispatch_Secondary settlement_identity
  | Exact_Secondary_Failed settlement_identity
  | Exact_Acknowledge product_secondary_ack

context source_attestation
begin

definition apply_non_submit_lock_action where
  "apply_non_submit_lock_action permitted maintainers registered action s =
    (let old = origin_outcomes (settlement_primary s);
         next = lock_product_step permitted (\<lambda>_ _ _ _. True) maintainers registered action (outcome_source old)
     in update_settlement_outcomes (old\<lparr>outcome_source := next\<rparr>) s)"

fun exact_step where
  "exact_step permitted verified maintainers registered verified_ack (Exact_Submit entry who call_id payload) s =
    s\<lparr>settlement_primary := submit_origin_call permitted verified maintainers registered entry who call_id payload
      (settlement_primary s)\<rparr>"
| "exact_step permitted verified maintainers registered verified_ack (Exact_Collect who call_id payload) s =
    update_settlement_outcomes (fst (complete_authoritative_result verified who call_id payload
      (origin_outcomes (settlement_primary s)))) s"
| "exact_step permitted verified maintainers registered verified_ack (Exact_Install who epoch changes sessions) s =
    apply_non_submit_lock_action permitted maintainers registered (Lock_Install who epoch changes sessions) s"
| "exact_step permitted verified maintainers registered verified_ack (Exact_Link connection) s =
    apply_non_submit_lock_action permitted maintainers registered (Lock_Driver_Connection connection) s"
| "exact_step permitted verified maintainers registered verified_ack Exact_Crash s =
    update_settlement_outcomes (crash_outcome_world (origin_outcomes (settlement_primary s))) s"
| "exact_step permitted verified maintainers registered verified_ack (Exact_Recover candidate) s =
    (case candidate of None \<Rightarrow> s | Some restored \<Rightarrow>
       if settlement_snapshot restored = settlement_snapshot s
       then let old = origin_outcomes (settlement_primary s) in update_settlement_outcomes
         (recover_outcome_world (Some (authoritative_outcome_snapshot old)) old) s
       else s)"
| "exact_step permitted verified maintainers registered verified_ack (Exact_Enqueue key) s = enqueue_secondary key s"
| "exact_step permitted verified maintainers registered verified_ack (Exact_Dispatch_Secondary key) s = dispatch_secondary key s"
| "exact_step permitted verified maintainers registered verified_ack (Exact_Secondary_Failed key) s = fail_secondary key s"
| "exact_step permitted verified maintainers registered verified_ack (Exact_Acknowledge ack) s = acknowledge_secondary verified_ack ack s"

fun run_exact_product where
  "run_exact_product permitted verified maintainers registered verified_ack [] s = s"
| "run_exact_product permitted verified maintainers registered verified_ack (action # rest) s =
    run_exact_product permitted verified maintainers registered verified_ack rest
      (exact_step permitted verified maintainers registered verified_ack action s)"

lemma exact_step_keeps_existing_decision:
  assumes "origin_decisions (settlement_primary s) key = Some recorded"
  shows "origin_decisions (settlement_primary (exact_step permitted verified maintainers registered verified_ack action s)) key = Some recorded"
  using assms by (cases action)
    (auto simp: apply_non_submit_lock_action_def update_settlement_outcomes_def Let_def
      any_origin_entry_keeps_a_committed_decision secondary_steps_preserve_primary split: option.splits if_splits)

theorem every_product_continuation_keeps_the_same_primary_decision:
  "origin_decisions (settlement_primary s) key = Some recorded \<Longrightarrow>
    origin_decisions (settlement_primary (run_exact_product permitted verified maintainers registered verified_ack actions s)) key = Some recorded"
  by (induction actions arbitrary: s) (auto intro: exact_step_keeps_existing_decision)

lemma failed_secondary_step_cannot_change_pending_source_mass:
  "settlement_primary (exact_step permitted verified maintainers registered verified_ack (Exact_Secondary_Failed key) s) =
    settlement_primary s"
  by (simp add: secondary_steps_preserve_primary)

end

end
