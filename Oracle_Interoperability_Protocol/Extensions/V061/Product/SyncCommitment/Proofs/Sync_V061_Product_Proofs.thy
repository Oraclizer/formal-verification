theory Sync_V061_Product_Proofs
  imports "OIP_Sync_V061_Position_Definitions.Sync_V061_Product" Sync_V061_Attestation
begin

lemma sync_history_is_nonempty [simp]:
  "reference_history_prefixes (sync_reference_history state) \<noteq> []"
  by (simp add: sync_reference_history_def)

lemma sync_mode_initial_requires_absence:
  assumes "sync_mode request = Sync_Initial" "sync_mode_ok policy request a retained"
  shows "retained = None" "sync_predecessor a = None"
  using assms by (cases retained; simp)+

lemma sync_mode_incremental_requires_both_exact_predecessors:
  assumes "sync_mode request = Sync_Incremental" "sync_mode_ok policy request a retained"
  obtains prior where "retained = Some prior"
    "sync_claimed_prior request = Some (sync_commitment prior)"
    "sync_predecessor a = Some (sync_commitment prior)"
  using assms by (cases retained) auto

lemma sync_mode_full_requires_the_exact_current_scope:
  assumes "sync_mode request = Sync_Full" "sync_mode_ok (sync_selected_policy state) request a retained"
  obtains prior where "retained = Some prior" "sync_predecessor a = None"
    "(sync_session request, sync_key request) \<in> sync_full_scope (sync_selected_policy state)"
  using assms by (cases retained) auto

lemma sync_fresh_assess_stale_cut_precedes_the_proof:
  "sync_signed_cut request \<noteq> sync_current_cut state \<Longrightarrow>
    sync_fresh_assess verify state core request = Sync_Reject Sync_Busy"
  by (simp add: sync_fresh_assess_def)

lemma sync_fresh_assess_bad_attestation_precedes_mode:
  assumes "sync_signed_cut request = sync_current_cut state"
  shows "sync_decode_proof (sync_attestation request) = None \<Longrightarrow>
    sync_fresh_assess verify state core request = Sync_Reject Sync_Proof_Rejected"
  and "sync_decode_proof (sync_attestation request) = Some (a,votes) \<Longrightarrow>
    \<not> sync_proof_ok verify (sync_origin_registry (sync_selected_policy state)) core request a votes \<Longrightarrow>
    sync_fresh_assess verify state core request = Sync_Reject Sync_Proof_Rejected"
  using assms by (simp_all add: sync_fresh_assess_def)

lemma sync_fresh_assess_mismatch_precedes_event_or_position:
  assumes "sync_signed_cut request = sync_current_cut state"
    "sync_decode_proof (sync_attestation request) = Some (a,votes)"
    "sync_proof_ok verify (sync_origin_registry (sync_selected_policy state)) core request a votes"
    "\<not> sync_mode_ok (sync_selected_policy state) request a (sync_retained state (sync_key request))"
  shows "sync_fresh_assess verify state core request = Sync_Reject Sync_Mismatch"
  using assms by (simp add: sync_fresh_assess_def)

lemma sync_fresh_assess_event_or_position_failure:
  assumes "sync_signed_cut request = sync_current_cut state"
    "sync_decode_proof (sync_attestation request) = Some (a,votes)"
    "sync_proof_ok verify (sync_origin_registry (sync_selected_policy state)) core request a votes"
    "sync_mode_ok (sync_selected_policy state) request a (sync_retained state (sync_key request))"
    "\<not> sync_position_and_event_fresh state request"
  shows "sync_fresh_assess verify state core request = Sync_Reject Sync_Stale"
  using assms by (simp add: sync_fresh_assess_def)

lemma sync_fresh_assess_binds_the_current_cut_and_source:
  assumes "sync_fresh_assess verify state core request = Sync_Accept a"
  obtains votes where
    "sync_signed_cut request = sync_current_cut state"
    "sync_decode_proof (sync_attestation request) = Some (a,votes)"
    "sync_proof_ok verify (sync_origin_registry (sync_selected_policy state)) core request a votes"
    "sync_mode_ok (sync_selected_policy state) request a (sync_retained state (sync_key request))"
    "sync_position_and_event_fresh state request"
  using assms by (auto simp: sync_fresh_assess_def split: option.splits prod.splits if_splits)

lemma sync_commit_appends_the_exact_read_projection:
  "sync_reference_history (sync_commit_record state core request a) =
    record_reference_advance (sync_receiver_epoch state) 1
      (sync_next_snapshot state request) (sync_reference_history state)"
  by (simp add: sync_reference_history_def sync_commit_record_def sync_write_outcome_def
    record_reference_advance_def)

lemma sync_commit_projects_the_single_stream_and_next_revision:
  fixes state :: "('key, 'product) sync_receiver"
  shows "sync_retained (sync_commit_record state core request a) (sync_key request) = Some (sync_requested request)"
    "stream \<noteq> sync_key request \<Longrightarrow>
      sync_retained (sync_commit_record state core request a) stream = sync_retained state stream"
    "sync_product_value (sync_current_snapshot (sync_commit_record state core request a)) =
      sync_product_value (sync_current_snapshot state)"
    "cut_revision (sync_current_cut (sync_commit_record state core request a)) =
      Suc (cut_revision (sync_current_cut state))"
  unfolding sync_commit_appends_the_exact_read_projection
  by (simp_all add: record_reference_advance_def sync_reference_history_def
    sync_next_snapshot_def reference_observed_cut_def)

lemma sync_commit_records_the_origin_event_and_exact_core:
  "sync_used_events (sync_commit_record state core request a) (sync_event_key request) = Some (sync_call request,a)"
  "sync_outcome_table (sync_commit_record state core request a) (sync_call request) =
    Some (encode_wire_core core,Sync_Committed (cut_revision (sync_current_cut state)))"
  by (simp_all add: sync_commit_record_def sync_write_outcome_def)

theorem sync_verified_fresh_success_is_the_single_attested_commit:
  assumes decoded: "sync_read_operands core = Some request"
    and fresh: "sync_outcome_table state (sync_call request) = None"
    and result: "sync_receive_verified verify core state = (after,Sync_Recorded (Sync_Committed position))"
  obtains a votes where "sync_execute_allowed state core request"
    "sync_signed_cut request = sync_current_cut state"
    "sync_decode_proof (sync_attestation request) = Some (a,votes)"
    "sync_proof_ok verify (sync_origin_registry (sync_selected_policy state)) core request a votes"
    "sync_mode_ok (sync_selected_policy state) request a (sync_retained state (sync_key request))"
    "sync_position_and_event_fresh state request"
    "sync_item a = sync_requested request"
    "after = sync_commit_record state core request a"
    "position = cut_revision (sync_current_cut state)"
proof -
  obtain a where allowed: "sync_execute_allowed state core request"
    and accepted: "sync_fresh_assess verify state core request = Sync_Accept a"
    and written: "after = sync_commit_record state core request a"
    and revision: "position = cut_revision (sync_current_cut state)"
    using decoded fresh result
    by (cases "sync_fresh_assess verify state core request")
      (auto simp: sync_receive_verified_def split: if_splits)
  obtain votes where cut: "sync_signed_cut request = sync_current_cut state"
    and decoded_proof: "sync_decode_proof (sync_attestation request) = Some (a,votes)"
    and trusted: "sync_proof_ok verify (sync_origin_registry (sync_selected_policy state)) core request a votes"
    and mode: "sync_mode_ok (sync_selected_policy state) request a (sync_retained state (sync_key request))"
    and unused: "sync_position_and_event_fresh state request"
    by (rule sync_fresh_assess_binds_the_current_cut_and_source[OF accepted])
  have exact: "sync_item a = sync_requested request"
    by (rule sync_accepted_proof_binds_every_request_field_and_current_roster(5)[OF trusted])
  show thesis by (rule that[OF allowed cut decoded_proof trusted mode unused exact written revision])
qed

lemma sync_fresh_rejection_consumes_only_the_call_outcome:
  fixes verify :: "'key sync_verify" and core :: wire_core and state :: "('key, 'product) sync_receiver"
  assumes "sync_read_operands core = Some request" "sync_execute_allowed state core request"
    "sync_outcome_table state (sync_call request) = None"
    "sync_fresh_assess verify state core request = Sync_Reject reason"
  defines "after \<equiv> fst (sync_receive_verified verify core state)"
  shows "snd (sync_receive_verified verify core state) = Sync_Recorded (Sync_Uncommitted reason)"
    "sync_reference_history after = sync_reference_history state"
    "sync_used_events after = sync_used_events state"
    "sync_selected_policy after = sync_selected_policy state"
    "sync_outcome_table after (sync_call request) = Some (encode_wire_core core,Sync_Uncommitted reason)"
    "other \<noteq> sync_call request \<Longrightarrow> sync_outcome_table after other = sync_outcome_table state other"
  using assms
  by (simp_all add: after_def sync_receive_verified_def sync_write_outcome_def sync_reference_history_def)

lemma sync_malformed_operands_cannot_consume_a_call:
  "sync_read_operands core = None \<Longrightarrow> sync_receive_verified verify core state = (state,Sync_Bad_Operands)"
  by (simp add: sync_receive_verified_def)

lemma sync_old_receiver_epoch_cannot_recover_an_outcome:
  assumes "sync_read_operands core = Some request"
    "wire_authority_epoch core \<noteq> cut_authority_epoch (sync_current_cut state)"
  shows "sync_receive_verified verify core state = (state,Sync_Denied)"
  using assms by (simp add: sync_receive_verified_def sync_execute_allowed_def sync_current_identity_def)

theorem sync_exact_authorized_retry_is_independent_of_fresh_attestation:
  assumes "sync_decode_core raw = Some core" "sync_read_operands core = Some request"
    "sync_execute_allowed state core request" "sync_outcome_table state (sync_call request) = Some (raw,outcome)"
  shows "sync_receive_verified verify core state = (state,Sync_Recorded outcome)"
  using assms sync_decoded_core_has_the_exact_bytes[OF assms(1)]
  by (simp add: sync_receive_verified_def)

lemma sync_distinct_core_cannot_read_or_replace_a_retained_result:
  assumes "sync_read_operands core = Some request" "sync_execute_allowed state core request"
    "sync_outcome_table state (sync_call request) = Some (original,outcome)" "original \<noteq> encode_wire_core core"
  shows "sync_receive_verified verify core state = (state,Sync_Call_Conflict)"
  using assms by (simp add: sync_receive_verified_def)

lemma sync_current_query_returns_exact_scoped_projection:
  assumes "sync_query_verified core state = Some (actual_cut,entry)"
  obtains request where "sync_read_query core = Some request"
    "sync_query_allowed state core request" "actual_cut = sync_query_cut request" "actual_cut = sync_current_cut state"
    "entry = sync_retained state (sync_query_key request)"
proof -
  obtain request where decoded: "sync_read_query core = Some request"
    using assms by (cases "sync_read_query core") (auto simp: sync_query_verified_def)
  have observed: "current_reference_observation (sync_query_allowed state core request)
    (\<lambda>snapshot. sync_entries snapshot (sync_query_key request))
    (sync_query_cut request) (sync_reference_history state) = Some (actual_cut,entry)"
    using assms decoded by (simp add: sync_query_verified_def)
  show thesis using decoded an_authorized_current_reply_consumes_its_exact_ledger_cut[OF observed] that by blast
qed

lemma sync_stale_or_unauthorized_query_hides_value_and_presence:
  assumes "sync_read_query core = Some request"
    "\<not> sync_query_allowed state core request \<or> sync_query_cut request \<noteq> sync_current_cut state"
  shows "sync_query_verified core state = None"
  using assms by (auto simp: sync_query_verified_def current_reference_observation_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_verified_fresh_success_is_the_single_attested_commit
    sync_commit_projects_the_single_stream_and_next_revision sync_commit_records_the_origin_event_and_exact_core
    sync_fresh_rejection_consumes_only_the_call_outcome sync_exact_authorized_retry_is_independent_of_fresh_attestation
    sync_distinct_core_cannot_read_or_replace_a_retained_result sync_current_query_returns_exact_scoped_projection
    sync_stale_or_unauthorized_query_hides_value_and_presence})
  then () else error "Unexpected oracle in SyncCommitment product"
\<close>

end
