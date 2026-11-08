theory Reference_Recovery_Trace_Bounds
  imports Reference_Trace_Read_Execution "OIP_Reference_Profile.Reference_Witness_Selection" "OIP_Product.Promotion_Financial"
begin

fun run_reference_transcript where
  "run_reference_transcript execute [] initial = (initial, [])"
| "run_reference_transcript execute (entry # rest) initial =
     (let (next, reply) = execute entry initial;
          (after, replies) = run_reference_transcript execute rest next
      in (after, reply # replies))"

lemma transcript_has_the_same_final_authority_as_the_reference_word:
  "fst (run_reference_transcript execute word initial) = run_reference_word execute word initial"
proof (induction word arbitrary: initial)
  case Nil
  then show ?case by simp
next
  case (Cons entry rest)
  obtain reached reply where first: "execute entry initial = (reached,reply)" by (cases "execute entry initial")
  obtain final replies where tail: "run_reference_transcript execute rest reached = (final,replies)"
    by (cases "run_reference_transcript execute rest reached")
  have "final = run_reference_word execute rest reached" using Cons.IH[of reached] tail by simp
  then show ?case using first tail by (simp add: Let_def)
qed

context source_attestation
begin

lemma an_exact_durable_call_record_does_not_guarantee_receipt_collection_during_a_crash:
  assumes saved: "outcome_entries state call_id = Some entry"
  shows "outcome_entries (crash_outcome_world state) call_id = Some entry"
    "observe_collection verified actor call_id payload (crash_outcome_world state) \<noteq> Collected outcome"
  using saved by (simp_all add: observe_collection_def crash_outcome_world_def product_crash_def product_apply_public_def
    split: if_splits)

end

definition reopen_with_selected_witness where
  "reopen_with_selected_witness archive_bound archives recovered observed mirrored prepared digest profile attachment disk =
    (case current_through_authority_mirror archive_bound archives recovered observed mirrored prepared of None \<Rightarrow> None
     | Some head \<Rightarrow> if committed_head disk = Some head
       then reopen_from_authenticated_head digest profile attachment disk else None)"

lemma selected_witness_reopens_the_exact_bound_archive_record:
  assumes picked: "current_through_authority_mirror archive_bound archives recovered observed mirrored prepared =
      Some (head_for_record digest stored)"
    and anchor: "committed_head disk = Some (head_for_record digest stored)"
    and archived: "\<And>archive. archive \<in> archives \<Longrightarrow> archive_bound archive observed \<Longrightarrow>
         flushed_records disk (head_for_record digest stored) = Some stored"
    and attached: "attachment_profile attachment = image_profile stored"
  shows "reopen_with_selected_witness archive_bound archives recovered observed mirrored prepared digest
       (image_profile stored) (Some attachment) disk =
     Some (reopen_retained_product (attachment_connection attachment) (image_records stored))"
proof -
  have witness: "witnessed_current archive_bound archives recovered observed = Some (head_for_record digest stored)"
    using picked by (simp add: current_through_authority_mirror_def split: if_splits)
  obtain archive where in_archives: "archive \<in> archives" and exact_archive: "archive_bound archive observed"
    using readback_and_repair_depend_on_the_independently_selected_control(3)[OF witness] by blast
  note exact = independently_anchored_records_construct_a_fresh_endpoint[OF anchor archived[OF in_archives exact_archive] attached]
  show ?thesis using picked anchor exact by (simp add: reopen_with_selected_witness_def)
qed

definition readback_at_one_complete_storage_snapshot ::
  "('hash persisted_commit \<Rightarrow> 'hash) \<Rightarrow> current_attachment \<Rightarrow> 'hash persisted_commit \<Rightarrow> regulated_product_world option" where
  "readback_at_one_complete_storage_snapshot digest attachment stored =
     (let head = head_for_record digest stored;
          cut = \<lparr>witness_version = image_sequence stored, witness_generation = 0, witness_control = head\<rparr>;
          disk = \<lparr>flushed_records = (\<lambda>_. None)(head := Some stored), committed_head = Some head\<rparr>
      in reopen_with_selected_witness (\<lambda>archived selected. archived = stored \<and> witness_control selected = head)
        {stored} cut cut (Some cut) ({} :: ('hash commit_head, 'hash persisted_commit) reference_witness_proposal set)
        digest (image_profile stored) (Some attachment) disk)"

lemma complete_authority_and_witness_rollback_can_make_the_same_recovery_accept_the_old_body:
  assumes old: "attachment_profile attachment = image_profile earlier"
    and current: "image_profile earlier = image_profile latest"
    and changed: "image_records earlier \<noteq> image_records latest"
  shows "map_option capture_retained_product (readback_at_one_complete_storage_snapshot digest attachment earlier) =
         Some (image_records earlier)"
    "map_option capture_retained_product (readback_at_one_complete_storage_snapshot digest attachment latest) =
         Some (image_records latest)"
    "readback_at_one_complete_storage_snapshot digest attachment earlier \<noteq>
      readback_at_one_complete_storage_snapshot digest attachment latest"
proof -
  have old_result: "map_option capture_retained_product (readback_at_one_complete_storage_snapshot digest attachment earlier) =
         Some (image_records earlier)"
    using old by (simp add: readback_at_one_complete_storage_snapshot_def reopen_with_selected_witness_def
      current_through_authority_mirror_def prepared_mirror_agrees_def witnessed_current_def
      reopen_from_authenticated_head_def head_for_record_def Let_def product_round_trip_preserves_the_durable_projection)
  have new_result: "map_option capture_retained_product (readback_at_one_complete_storage_snapshot digest attachment latest) =
         Some (image_records latest)"
    using old current by (simp add: readback_at_one_complete_storage_snapshot_def reopen_with_selected_witness_def
      current_through_authority_mirror_def prepared_mirror_agrees_def witnessed_current_def
      reopen_from_authenticated_head_def head_for_record_def Let_def product_round_trip_preserves_the_durable_projection)
  show "map_option capture_retained_product (readback_at_one_complete_storage_snapshot digest attachment earlier) =
         Some (image_records earlier)" by (rule old_result)
  show "map_option capture_retained_product (readback_at_one_complete_storage_snapshot digest attachment latest) =
         Some (image_records latest)" by (rule new_result)
  show "readback_at_one_complete_storage_snapshot digest attachment earlier \<noteq>
      readback_at_one_complete_storage_snapshot digest attachment latest"
  proof
    assume equal: "readback_at_one_complete_storage_snapshot digest attachment earlier =
       readback_at_one_complete_storage_snapshot digest attachment latest"
    have "image_records earlier = image_records latest" using old_result new_result equal by simp
    with changed show False by simp
  qed
qed

context reference_trace_consumer
begin

theorem the_independently_selected_recovery_keeps_the_full_actual_reference_reply_transcript:
  assumes picked: "current_through_authority_mirror archive_bound archives recovered observed mirrored prepared =
      Some (head_for_record digest stored)"
    and anchor: "committed_head disk = Some (head_for_record digest stored)"
    and archived: "\<And>archive. archive \<in> archives \<Longrightarrow> archive_bound archive observed \<Longrightarrow>
         flushed_records disk (head_for_record digest stored) = Some stored"
    and attached: "attachment_profile attachment = image_profile stored"
    and observed_state: "image_records stored = capture_retained_product uninterrupted"
  obtains restored where "reopen_with_selected_witness archive_bound archives recovered observed mirrored prepared digest
      (image_profile stored) (Some attachment) disk = Some restored"
    "run_reference_transcript execute word \<lparr>reference_product = capture_retained_product restored,reference_inputs = grants\<rparr> =
     run_reference_transcript execute word \<lparr>reference_product = capture_retained_product uninterrupted,reference_inputs = grants\<rparr>"
proof -
  let ?restored = "reopen_retained_product (attachment_connection attachment) (image_records stored)"
  have actual: "reopen_with_selected_witness archive_bound archives recovered observed mirrored prepared digest
       (image_profile stored) (Some attachment) disk = Some ?restored"
    by (rule selected_witness_reopens_the_exact_bound_archive_record[OF picked anchor archived attached])
  show thesis by (rule that[OF actual])
    (simp add: observed_state[symmetric] product_round_trip_preserves_the_durable_projection)
qed

theorem a_reference_trace_conserves_actual_source_mass_and_a_missing_terminal_only_holds_or_queries:
  fixes before prefix initial
  defines "before \<equiv> run_reference_word execute prefix initial"
  assumes start: "reference_service_contract registered (initial_finality_core balances regulatory contexts) initial"
  shows "product_source_mass (core_parent (retained_core (retained_source (reference_product before)))) account = int (balances account)"
    "open_source_binding (identity_source (reopen_retained_product connection (reference_product before))) key = Some binding \<Longrightarrow>
      serve connection (Service_Source_Probe key None) supplied before \<in>
       {(before,Some (Scheduled_Endpoint (Service_Source_Result (Hold_Exact_Source binding)))),
        (before,Some (Scheduled_Endpoint (Service_Source_Result (Query_Exact_Source binding))))}"
proof -
  have contract: "reference_service_contract registered (initial_finality_core balances regulatory contexts) before"
    unfolding before_def by (rule every_reference_prefix_keeps_the_central_authority_contract[OF start])
  note replay = actual_reference_history_consumes_the_public_replay_and_single_origin_settlement(1)[OF contract]
  have mass: "reservation_contract balances (core_parent (retained_core (retained_source (reference_product before))))"
    unfolding replay by (rule finality_supplies_actual_reservation_contract)
  show "product_source_mass (core_parent (retained_core (retained_source (reference_product before)))) account = int (balances account)"
    by (rule a_public_reservation_contract_conserves_the_product_source_pool[OF mass])
  have grants: "reference_grants_fit registered (reference_product before) (reference_inputs before)"
    using contract by (simp add: reference_service_contract_def)
  show "open_source_binding (identity_source (reopen_retained_product connection (reference_product before))) key = Some binding \<Longrightarrow>
      serve connection (Service_Source_Probe key None) supplied before \<in>
       {(before,Some (Scheduled_Endpoint (Service_Source_Result (Hold_Exact_Source binding)))),
        (before,Some (Scheduled_Endpoint (Service_Source_Result (Query_Exact_Source binding))))}"
    using grants by (simp add: actual_execute service_at_reference_snapshot_def select_reference_grants_def schedule_at_retained_state_def
      schedule_service_step_def next_recovery_source_action_def Let_def product_round_trip_preserves_the_durable_projection split: if_splits)
qed

theorem a_successful_read_at_one_reference_prefix_does_not_authorize_a_write_after_a_later_cut:
  fixes before later early_reads later_reads
    execute_prefix extra initial read_connection write_connection
  defines "before \<equiv> run_reference_word execute execute_prefix initial"
    and "later \<equiv> run_reference_word execute extra before"
    and "early_reads \<equiv> regulated_read_world (reopen_retained_product read_connection (reference_product before))"
    and "later_reads \<equiv> regulated_read_world (reopen_retained_product write_connection (reference_product later))"
  assumes returned: "serve read_connection (Service_Read token proof target (Current_Data query expected) cache) supplied before =
    (observed_after,Some (Scheduled_Endpoint (Service_Read_Result (Authorized_Data (Current_Cut_Value observed value)))))"
    and advanced: "observed_product_cut (read_authority early_reads) \<noteq> observed_product_cut (read_authority later_reads)"
  shows "observed = observed_product_cut (read_authority early_reads)"
    "fst (execute_at_checked_cut (reference_permitted_at (reference_inputs later)) verified maintainers registered verified_ack
      entry actor observed call_id payload later_reads) = later_reads"
proof -
  note actual = a_reference_step_uses_the_actual_service_with_the_retained_grants
    [OF returned[unfolded actual_execute reference_service_input.select_convs]]
  have reply: "read_with_revalidated_cache directory read_policy authenticate verify_read token proof target
    (Current_Data query expected) cache (reopen_retained_product read_connection (reference_product before)) =
      Authorized_Data (Current_Cut_Value observed value)"
    using actual by (simp add: schedule_at_retained_state_def schedule_service_step_def Let_def)
  show cut: "observed = observed_product_cut (read_authority early_reads)"
    using a_current_reply_from_the_actual_wire_ready_endpoint_has_its_exact_cut[OF reply] by (simp add: early_reads_def)
  have stale: "observed \<noteq> observed_product_cut (read_authority later_reads)" using advanced cut by simp
  show "fst (execute_at_checked_cut (reference_permitted_at (reference_inputs later)) verified maintainers registered verified_ack
      entry actor observed call_id payload later_reads) = later_reads"
    by (rule stale_cut_cannot_authorize_a_product_effect[OF stale])
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.an_exact_durable_call_record_does_not_guarantee_receipt_collection_during_a_crash
    complete_authority_and_witness_rollback_can_make_the_same_recovery_accept_the_old_body
    reference_trace_consumer.the_independently_selected_recovery_keeps_the_full_actual_reference_reply_transcript
    reference_trace_consumer.a_reference_trace_conserves_actual_source_mass_and_a_missing_terminal_only_holds_or_queries
    reference_trace_consumer.a_successful_read_at_one_reference_prefix_does_not_authorize_a_write_after_a_later_cut})
  then () else error "Unexpected oracle in recovery trace bounds"
\<close>

end
