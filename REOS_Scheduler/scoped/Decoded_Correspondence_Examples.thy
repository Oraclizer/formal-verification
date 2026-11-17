theory Decoded_Correspondence_Examples
  imports Decoded_Service_Correspondence
begin

lemma checked_queue_indexes_reconstruct_the_full_cut:
  assumes indexed: "indexing_preserves_the_queue_payloads (projected_image d) d"
  shows "a_decoded_cut_represents (decoded_view_for d) d"
proof -
  let ?s = "scheduler_at d"
  have indexed_ordinary: "p \<in> set (ordinary_queue ?s) \<Longrightarrow> admitted_at d (packet_identity p) = Some p" for p
    using indexed by (auto simp: indexing_preserves_the_queue_payloads_def projected_image_def)
  have indexed_regulation: "p \<in> set (regulatory_queue ?s) \<Longrightarrow> admitted_at d (packet_identity p) = Some p" for p
    using indexed by (auto simp: indexing_preserves_the_queue_payloads_def projected_image_def)
  have ordinary: "map ((\<lambda>q. the (admitted_at d q)) \<circ> packet_identity) (ordinary_queue ?s) = ordinary_queue ?s"
    by (rule map_idI) (simp add: indexed_ordinary)
  have regulation: "map ((\<lambda>q. the (admitted_at d q)) \<circ> packet_identity) (regulatory_queue ?s) = regulatory_queue ?s"
    by (rule map_idI) (simp add: indexed_regulation)
  have cut: "decoded_snapshot (decoded_view_for d) = committed_cut d"
    by (intro service_snapshot.equality scheduler_state.equality)
      (simp_all add: decoded_snapshot_def decoded_view_for_def projected_image_def Let_def ordinary regulation)
  from indexed cut show ?thesis
    by (simp add: a_decoded_cut_represents_def dquencer_image_relation_def decoded_view_for_def)
qed

theorem actual_decoded_history_records_a_refusal_followed_by_a_context_commit:
  obtains denied_exchange accepted_exchange denied_event accepted_event where
    "observed_exchanges_are_a_machine_trace rotation_evidence UNIV before_rotation
      [denied_exchange, accepted_exchange] [denied_event, accepted_event] changed_epoch"
    "submitted_operation denied_exchange = Context_Update 5 6 9 8"
    "completed_observation denied_exchange = No_Context_Write"
    "before_exchange denied_exchange = after_exchange denied_exchange"
    "submitted_operation accepted_exchange = Context_Update 5 5 9 8"
    "completed_observation accepted_exchange =
      Verified_Context 5 (image_policy_epoch (decoded_image (after_exchange accepted_exchange))) 5"
    "image_policy_epoch (decoded_image (after_exchange accepted_exchange)) 9 = 8"
    "comparison_token (decoded_image (after_exchange accepted_exchange)) =
      Suc (comparison_token (decoded_image (before_exchange accepted_exchange)))"
proof -
  let ?d = before_rotation
  let ?t = changed_epoch
  let ?E = rotation_evidence
  let ?view = "decoded_view_for ?d"
  let ?new = "decoded_view_for ?t"
  let ?reject = "Applied_Context (Rejected Invalid_Context)"
  let ?advance = "Applied_Context (Internal Context_Advanced)"
  note rejected = rotated_authority_retires_only_the_old_priority_and_serves_the_original_fifo(1)
  note accepted = rotated_authority_retires_only_the_old_priority_and_serves_the_original_fifo(2)
  from accepted obtain r where checked:
    "checked_advance (authority_facts ?E) (rollback_context (scheduler_at ?d)) 5 5 9 8 = (Internal Context_Advanced,r)"
    and written: "?t = write_scheduler ?d ((scheduler_at ?d)\<lparr>rollback_context := r\<rparr>)"
    by (auto split: prod.splits transition_result.splits rollback_internal.splits)
  from checked have updated: "authority_epoch r = 5" "policy_epoch r 9 = 8" "consensus_time r = 5"
    by (auto simp: checked_advance_def split: if_splits)
  have start_queues: "ordinary_queue (scheduler_at ?d) = [ordinary_packet]"
    "regulatory_queue (scheduler_at ?d) = [urgent_packet]"
    by (simp_all add: before_rotation_def Scheduler_Examples.priority_admitted_def
      Scheduler_Examples.ordinary_admitted_def scheduler_reduction packet_example)
  have original_index: "indexing_preserves_the_queue_payloads (projected_image ?d) ?d"
    using start_queues by (simp add: indexing_preserves_the_queue_payloads_def projected_image_def
      before_rotation_def ordinary_packet_def urgent_packet_def)
  have preserved:
    "ordinary_queue (scheduler_at ?t) = ordinary_queue (scheduler_at ?d)"
    "regulatory_queue (scheduler_at ?t) = regulatory_queue (scheduler_at ?d)"
    "admitted_at ?t = admitted_at ?d" by (simp_all add: written write_scheduler_def)
  from original_index have current_index: "indexing_preserves_the_queue_payloads (projected_image ?t) ?t"
    by (simp add: indexing_preserves_the_queue_payloads_def projected_image_def preserved)
  note valid_before = checked_queue_indexes_reconstruct_the_full_cut[OF original_index]
  note valid_after = checked_queue_indexes_reconstruct_the_full_cut[OF current_index]
  let ?policy = "image_policy_epoch (decoded_image ?new)"
  let ?verified = "Verified_Context 5 ?policy 5"
  have reply: "recorded_service_reply (decoded_image ?new) ?advance = ?verified"
    using updated by (simp add: written decoded_view_for_def projected_image_def)
  let ?e1 = "\<lparr>source_state = ?d, step_action = Change_Context 5 6 9 8,
    step_outcome = ?reject, target_state = ?d\<rparr>"
  let ?e2 = "\<lparr>source_state = ?d, step_action = Change_Context 5 5 9 8,
    step_outcome = ?advance, target_state = ?t\<rparr>"
  let ?n1 = "\<lparr>before_exchange = ?view, submitted_operation = Context_Update 5 6 9 8,
    completed_observation = No_Context_Write, after_exchange = ?view\<rparr>"
  let ?n2 = "\<lparr>before_exchange = ?view, submitted_operation = Context_Update 5 5 9 8,
    completed_observation = ?verified, after_exchange = ?new\<rparr>"
  have first: "step_occurs (machine_step ?E) ?e1" and second: "step_occurs (machine_step ?E) ?e2"
    by (simp_all add: step_occurs_def machine_step_def rejected accepted del: run_machine.simps)
  have denied: "observed_exchange_represents ?E ?n1 ?e1"
    by (simp add: observed_exchange_represents_def valid_before first)
  have committed: "observed_exchange_represents ?E ?n2 ?e2"
    by (simp add: observed_exchange_represents_def valid_before valid_after second reply
      del: recorded_service_reply.simps)
  from first second have trace: "finite_trace (machine_step ?E) UNIV ?d [?e1, ?e2] ?t" by simp
  from trace denied committed have observed:
    "observed_exchanges_are_a_machine_trace ?E UNIV ?d [?n1, ?n2] [?e1, ?e2] ?t"
    by (simp add: observed_exchanges_are_a_machine_trace_def)
  show thesis
    by (rule that[OF observed]) (simp_all add: updated written decoded_view_for_def projected_image_def)
qed

end
