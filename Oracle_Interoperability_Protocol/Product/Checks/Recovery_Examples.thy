theory Recovery_Examples
  imports "../Recovery_Commit" Identity_Examples
begin

definition recovery_case_profile :: recovery_profile where
  "recovery_case_profile = \<lparr>recovery_deployment = 7, recovery_format = 1, recovery_authority_profile = 99\<rparr>"

definition recovery_case_attachment :: current_attachment where
  "recovery_case_attachment =
    \<lparr>attachment_profile = recovery_case_profile, attachment_connection = Authority_Connected\<rparr>"

definition recovery_case_before where
  "recovery_case_before = record_checked_refusal (7,1) identity_case_payload Authority_Busy handover_case_world"

definition recovery_case_old :: "nat persisted_commit" where
  "recovery_case_old = \<lparr>image_profile = recovery_case_profile, image_sequence = 0, image_parent = None,
    image_records = capture_retained_product handover_case_world\<rparr>"

definition recovery_case_current :: "nat persisted_commit" where
  "recovery_case_current = \<lparr>image_profile = recovery_case_profile, image_sequence = 1, image_parent = Some 0,
    image_records = capture_retained_product recovery_case_before\<rparr>"

definition recovery_case_disk :: "nat recovery_store" where
  "recovery_case_disk =
    \<lparr>flushed_records = (\<lambda>_. None)(head_for_record image_sequence recovery_case_old := Some recovery_case_old),
     committed_head = Some (head_for_record image_sequence recovery_case_old)\<rparr>"

abbreviation recovery_case_flushed where
  "recovery_case_flushed \<equiv> flush_commit_record image_sequence recovery_case_current recovery_case_disk"

abbreviation recovery_case_published where
  "recovery_case_published \<equiv> publish_recovery_head image_sequence
    (Some (head_for_record image_sequence recovery_case_old)) recovery_case_current recovery_case_flushed"

abbreviation recovery_case_reopened where
  "recovery_case_reopened \<equiv> reopen_retained_product Authority_Connected (capture_retained_product recovery_case_before)"

lemma staged_commit_head_still_identifies_the_previous_image:
  "committed_head recovery_case_flushed = Some (head_for_record image_sequence recovery_case_old)"
  by (simp add: recovery_case_disk_def flushed_candidate_is_not_visible_before_the_head_changes)

lemma exact_new_head_reopens_the_records_only_product:
  "reopen_from_authenticated_head image_sequence recovery_case_profile (Some recovery_case_attachment)
     recovery_case_published = Some recovery_case_reopened"
proof -
  have extends: "candidate_extends_head (Some (head_for_record image_sequence recovery_case_old)) recovery_case_current"
    by (simp add: candidate_extends_head_def head_for_record_def recovery_case_old_def recovery_case_current_def)
  have flushed: "flushed_records recovery_case_flushed (head_for_record image_sequence recovery_case_current) =
    Some recovery_case_current"
    by (simp add: flush_commit_record_def Let_def recovery_case_disk_def head_for_record_def
        recovery_case_old_def recovery_case_current_def)
  note pinned = published_head_identifies_the_flushed_record[OF staged_commit_head_still_identifies_the_previous_image extends flushed]
  have profile: "attachment_profile recovery_case_attachment = image_profile recovery_case_current"
    by (simp add: recovery_case_attachment_def recovery_case_current_def)
  show ?thesis using independently_anchored_records_construct_a_fresh_endpoint[OF pinned(1) pinned(2) profile]
    by (simp add: recovery_case_current_def recovery_case_attachment_def)
qed

lemma replaying_old_valid_bytes_cannot_replace_the_latest_image:
  "let head = head_for_record image_sequence recovery_case_current;
       corrupted = recovery_case_published\<lparr>committed_head := Some head,
          flushed_records := (flushed_records recovery_case_published)(head := Some recovery_case_old)\<rparr>
     in reopen_from_authenticated_head image_sequence recovery_case_profile (Some recovery_case_attachment) corrupted = None"
  by (simp add: reopen_from_authenticated_head_def head_for_record_def Let_def
      recovery_case_attachment_def recovery_case_current_def recovery_case_old_def)

lemma recovered_world_keeps_the_actual_pending_reservation:
  "authoritative_reservation_state (identity_source recovery_case_reopened) = authoritative_reservation_state handover_case_source"
proof -
  have actual: "outcome_source (current_product_outcomes handover_case_world) = handover_case_source"
    using identity_case_has_the_actual_source
    by (simp add: identity_source_def observed_product_source_def current_product_outcomes_def
        regulated_read_world_def legal_underlying_outcomes_def)
  have capture_source: "retained_source (capture_retained_product recovery_case_before) =
    capture_retained_source (outcome_source (current_product_outcomes recovery_case_before))"
    by (simp add: capture_retained_product_def current_product_outcomes_def legal_underlying_outcomes_def Let_def)
  have underlying: "outcome_source (current_product_outcomes recovery_case_before) = handover_case_source"
    unfolding recovery_case_before_def checked_refusal_keeps_the_exact_underlying_source by (rule actual)
  have saved: "retained_source (capture_retained_product recovery_case_before) = capture_retained_source handover_case_source"
    unfolding capture_source underlying by (rule refl)
  show ?thesis
    unfolding recovery_projection_supplies_the_exact_source saved
    by (simp add: authoritative_reservation_state_def reopen_retained_source_def capture_retained_source_def Let_def)
qed

lemma retained_request_and_busy_outcome_survive_fresh_reconstruction:
  "outcome_entries (current_product_outcomes recovery_case_reopened) (7,1) =
    Some \<lparr>result_payload = identity_case_payload, result_outcome = Authority_Busy\<rparr>"
proof -
  have unused: "\<not> authority_has_call_id (7,1) handover_case_world"
    by (simp add: authority_has_call_id_def current_product_outcomes_def legal_underlying_outcomes_def
        handover_case_world_def initial_regulated_product_def initial_governed_world_def initial_legal_world_def
        initial_product_reads_def initial_settlement_world_def initial_origin_world_def initial_outcome_world_def unclaimed_regulated_call_def)
  have saved: "outcome_entries (current_product_outcomes recovery_case_before) (7,1) =
    Some \<lparr>result_payload = identity_case_payload, result_outcome = Authority_Busy\<rparr>"
    unfolding recovery_case_before_def by (rule fresh_checked_refusal_records_the_exact_request[OF unused])
  show ?thesis using saved
    by (simp add: current_product_outcomes_def legal_underlying_outcomes_def reopen_retained_product_def
        capture_retained_product_def initial_product_reads_def Let_def)
qed

lemma reopened_source_is_still_the_exact_unresolved_origin:
  "open_source_binding (identity_source recovery_case_reopened) (0,17) = Some (sample_binding 17)"
proof -
  obtain claim where retained: "recoverable_reservation handover_case_source (0,17) = Some claim"
    and binding: "reservation_binding claim = sample_binding 17" "reservation_phase claim = Source_Pending"
    using handover_case_retains_a_live_reservation by blast
  have actual: "reservation_at (authoritative_reservation_state handover_case_source) (0,17) = Some claim"
    using retained by (cases "reservation_at (authoritative_reservation_state handover_case_source) (0,17)")
      (auto simp: recoverable_reservation_def split: if_splits)
  show ?thesis using actual binding
    by (simp add: open_source_binding_def recovered_world_keeps_the_actual_pending_reservation)
qed

context source_attestation
begin

lemma recovery_queries_the_same_origin_and_holds_mismatched_evidence:
  "next_recovery_source_action (0,17) None (identity_source recovery_case_reopened) =
      Query_Exact_Source (sample_binding 17) \<and>
    next_recovery_source_action (0,17) (Some (sample_certificate 22)) (identity_source recovery_case_reopened) =
      Hold_Exact_Source (sample_binding 17)"
proof -
  have connection: "call_connection (product_calls (identity_source recovery_case_reopened)) = Authority_Connected"
    by (simp add: recovery_projection_supplies_the_exact_source reopened_source_has_no_old_process_or_response_cache)
  have missing: "next_recovery_source_action (0,17) None (identity_source recovery_case_reopened) =
      Query_Exact_Source (sample_binding 17)"
    using connection reopened_source_is_still_the_exact_unresolved_origin
    by (simp add: next_recovery_source_action_def)
  have wrong: "statement_binding (certificate_statement (sample_certificate 22)) \<noteq> sample_binding 17"
    by (simp add: sample_certificate_def sample_statement_def sample_binding_def example_binding_def)
  show ?thesis using missing mismatched_source_evidence_only_holds_the_exact_pending_binding
    [OF reopened_source_is_still_the_exact_unresolved_origin wrong] by simp
qed

end

end
