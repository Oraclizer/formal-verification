theory Replay_Export_Frames
  imports "OIP_V062_P13_Replay_Finite_Projection.Replay_Finite_Projection"
begin

text \<open>The export equations are finite views of the two checked runs.
The values and markers in these equations come from the actual transition
projections. Input rows select a frame and provide a typed request.\<close>

definition rpe_session_keys :: "product_session_id list" where
  "rpe_session_keys = [1,2,4]"

definition rpe_call_keys :: "client_call_id list" where
  "rpe_call_keys = [(7,1),(7,2)]"

definition rpe_sessions :: "nat \<Rightarrow> (product_session_id \<times> product_session_binding) list" where
  "rpe_sessions epoch =
    [(1,\<lparr>session_principal = 7, session_epoch = epoch\<rparr>),
     (2,\<lparr>session_principal = 7, session_epoch = epoch\<rparr>),
     (4,\<lparr>session_principal = 8, session_epoch = epoch\<rparr>)]"

definition rpe_payload :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> product_call_payload" where
  "rpe_payload signed_epoch signed_revision duration =
    \<lparr>payload_envelope = \<lparr>envelope_message = 1, envelope_origin = (0,17),
      envelope_asset = 17, envelope_caller = 7, envelope_session = 1,
      envelope_cut = \<lparr>cut_authority_epoch = signed_epoch, cut_revision = signed_revision\<rparr>,
      envelope_command = Client_Protocol 0 0 (Reserve_Intent (sample_request 17) [] duration)\<rparr>,
    payload_credential = None, payload_origin_epoch = 9\<rparr>"

definition rpe_dispatch_frame :: rpf_state where
  "rpe_dispatch_frame = rpf_project rpe_session_keys rpe_call_keys prd_completed"

definition rpe_reopened_frame :: rpf_state where
  "rpe_reopened_frame = rpf_project rpe_session_keys rpe_call_keys (prc_outcomes prc_epoch_settlement)"

lemma rpe_initial_cut:
  "current_product_cut hf_initial = \<lparr>cut_authority_epoch = 9, cut_revision = 0\<rparr>"
  using prp_initial_reserved_dispatched_metadata(1) prp_revisions_come_from_actual_submissions(1)
  by (cases "current_product_cut hf_initial") simp

lemma rpe_reserved_cut:
  "current_product_cut hf_reserved = \<lparr>cut_authority_epoch = 9, cut_revision = 1\<rparr>"
  using prp_initial_reserved_dispatched_metadata(2) prp_revisions_come_from_actual_submissions(2)
  by (cases "current_product_cut hf_reserved") simp

lemma rpe_same_cut_payload_is_the_actual_duration_update:
  "rpe_payload 9 0 duration = rpf_payload_for_duration duration"
  unfolding rpe_payload_def rpf_payload_for_duration_def prp_original_payload_def
    hf_envelope_def hf_reserve_def rpe_initial_cut by simp

lemma rpe_original_reply_is_actual_acquisition:
  "pro_original_outcome = Authority_Reply (Protocol_Response Reservation_Acquired)"
  unfolding pro_original_outcome_def hf_reserve_def sample.first_protocol_call_uses_the_current_core
  by (simp add: sample.invoke_protocol_def finality_sample_initial_def initial_finality_core_def
      current_lock_view_def empty_vector_represents_zero_versions lift_protocol_result_def lock_example_public_defs)

lemma rpe_reserve_entry_code [code]:
  "pro_original_entry =
    \<lparr>result_payload = rpe_payload 9 0 10, result_outcome = Authority_Reply (Protocol_Response Reservation_Acquired)\<rparr>"
  unfolding pro_original_entry_def rpe_original_reply_is_actual_acquisition
    rpe_same_cut_payload_is_the_actual_duration_update rpf_duration_controls_change_the_actual_typed_payload(1)
  by (rule refl)

lemma rpe_dispatch_entry_code [code]:
  "prd_entry = \<lparr>result_payload = \<lparr>payload_envelope =
    \<lparr>envelope_message = 2, envelope_origin = (0,17), envelope_asset = 17, envelope_caller = 7,
      envelope_session = 2, envelope_cut = \<lparr>cut_authority_epoch = 9, cut_revision = 1\<rparr>,
      envelope_command = Client_Protocol 0 0 (Dispatch_Intent (sample_request 17) 0 [])\<rparr>,
    payload_credential = Some lock_example_token, payload_origin_epoch = 9\<rparr>,
    result_outcome = Authority_Reply (Protocol_Response Source_Dispatched)\<rparr>"
  unfolding prd_entry_def prd_payload_def hf_envelope_def hf_dispatch_def rpe_reserved_cut
    prd_dispatch_credential_is_the_actual_fence prd_the_actual_second_reply_reports_dispatch
  by simp

lemma rpe_sessions_are_projected_from_the_source:
  assumes sessions: "product_sessions (product_durable (outcome_source outcomes)) = hf_sessions epoch"
  shows "rpf_session_rows rpe_session_keys outcomes = rpe_sessions epoch"
  unfolding rpf_session_rows_def rpe_session_keys_def rpe_sessions_def sessions hf_sessions_def by simp

lemma rpe_dispatch_ready:
  "result_completion_ready prd_entry outcomes"
  unfolding result_completion_ready_def prd_entry_def prd_payload_def hf_envelope_def hf_dispatch_def
    prd_the_actual_second_reply_reports_dispatch by (simp add: Let_def)

lemma rpe_dispatch_frame_code [code]:
  "rpe_dispatch_frame = \<lparr>rpf_epoch = 9, rpf_revision = 2, rpf_live = True,
    rpf_sessions = rpe_sessions 9,
    rpf_entries = [((7,1),(pro_original_entry,True)),((7,2),(prd_entry,True))],
    rpf_completed = rpe_call_keys\<rparr>"
proof -
  have sessions: "rpf_session_rows rpe_session_keys prd_completed = rpe_sessions 9"
    by (rule rpe_sessions_are_projected_from_the_source)
      (unfold prd_completed_dispatch_retains_both_actual_entries(1), rule prp_initial_reserved_dispatched_metadata(6))
  have first_ready: "rpf_ready_entry prd_completed (7,1) = Some (pro_original_entry,True)"
    unfolding rpf_ready_entry_def prd_completed_dispatch_retains_both_actual_entries(2)
    by (simp add: pro_original_reserve_result_needs_no_terminal_publication_to_be_read)
  have second_ready: "rpf_ready_entry prd_completed (7,2) = Some (prd_entry,True)"
    unfolding rpf_ready_entry_def prd_completed_dispatch_retains_both_actual_entries(3)
    by (simp add: rpe_dispatch_ready)
  have entries: "rpf_result_rows rpe_call_keys prd_completed =
    [((7,1),(pro_original_entry,True)),((7,2),(prd_entry,True))]"
    unfolding rpf_result_rows_def rpe_call_keys_def
    by (simp only: List.map_filter_simps first_ready second_ready map_option_case option.case)
  have completed: "filter (\<lambda>key. key \<in> outcome_completed prd_completed) rpe_call_keys = rpe_call_keys"
    unfolding rpe_call_keys_def prd_completed_dispatch_retains_both_actual_entries(4) by simp
  show ?thesis
    unfolding rpe_dispatch_frame_def rpf_project_def Let_def sessions entries completed
      prd_completed_dispatch_retains_both_actual_entries(1)
      prp_initial_reserved_dispatched_metadata(3) prp_revisions_come_from_actual_submissions(3)
      prd_dispatched_endpoint_is_up by simp
qed

lemma rpe_reinstallation_advances_by_its_actual_context_batch:
  "cut_revision (current_product_cut prp_reissued_source) = 3"
proof -
  have counts: "length (call_authority_log
      (sample.finality_calls.run_calls (map Apply_Authority_Input changes) calls)) =
      length (call_authority_log calls) + length changes" for changes calls
    by (induction changes arbitrary: calls)
      (simp_all add: sample.finality_calls.apply_authority_input_def Let_def)
  have before: "length (call_authority_log (product_calls hf_reserved)) = 1"
    using prp_revisions_come_from_actual_submissions(2) by (simp add: current_product_cut_def)
  have batch: "length (transfer_contexts hg_proposal) = 2"
    by (simp add: hg_proposal_def handover_case_proposal_def)
  have calls: "product_calls prp_reissued_source =
      sample.finality_calls.run_calls (map Apply_Authority_Input (transfer_contexts hg_proposal))
        (product_calls hf_reserved)"
    by (simp add: prp_reissued_source_def prp_context_install_has_the_actual_new_epoch sample.product_apply_public_def)
  show ?thesis unfolding current_product_cut_def
    by (simp add: calls counts before batch numeral_2_eq_2 numeral_3_eq_3)
qed

lemma rpe_reopened_frame_code [code]:
  "rpe_reopened_frame = \<lparr>rpf_epoch = 10, rpf_revision = 3, rpf_live = True,
    rpf_sessions = rpe_sessions 10, rpf_entries = [((7,1),(pro_original_entry,True))],
    rpf_completed = [(7,1)]\<rparr>"
proof -
  let ?outcomes = "prc_outcomes prc_epoch_settlement"
  have sessions: "rpf_session_rows rpe_session_keys ?outcomes = rpe_sessions 10"
    by (rule rpe_sessions_are_projected_from_the_source)
      (unfold prc_install_preserves_the_full_outcome_table_and_completed_set(1), rule prp_reused_numeric_session_is_current(2))
  have second: "outcome_entries ?outcomes (7,2) = None"
    unfolding prc_install_preserves_the_full_outcome_table_and_completed_set(2)
      pro_completed_updates_only_the_marker pro_submit_constructs_the_entry_from_the_actual_reserve_reply
      store_product_result_def pro_initial_def initial_outcome_world_def
    by (simp add: numeral_2_eq_2)
  have first_ready: "rpf_ready_entry ?outcomes (7,1) = Some (pro_original_entry,True)"
    unfolding rpf_ready_entry_def prc_install_keeps_the_original_result_at_the_live_new_epoch(2)
    by (simp add: pro_original_reserve_result_needs_no_terminal_publication_to_be_read)
  have second_absent: "rpf_ready_entry ?outcomes (7,2) = None"
    unfolding rpf_ready_entry_def second by simp
  have entries: "rpf_result_rows rpe_call_keys ?outcomes = [((7,1),(pro_original_entry,True))]"
    unfolding rpf_result_rows_def rpe_call_keys_def
    by (simp only: List.map_filter_simps first_ready second_absent map_option_case option.case)
  have completed: "filter (\<lambda>key. key \<in> outcome_completed ?outcomes) rpe_call_keys = [(7,1)]"
    unfolding rpe_call_keys_def prc_install_preserves_the_full_outcome_table_and_completed_set(3)
      pro_completed_retains_the_produced_source_and_entry(3) by (simp add: numeral_2_eq_2)
  show ?thesis
    unfolding rpe_reopened_frame_def rpf_project_def Let_def sessions entries completed
      prc_install_preserves_the_full_outcome_table_and_completed_set(1)
      prp_reused_numeric_session_is_current(1) rpe_reinstallation_advances_by_its_actual_context_batch
      prc_reissued_source_is_live by simp
qed

definition rpe_prefix_units :: "nat list" where
  "rpe_prefix_units = map (\<lambda>snapshot. source_units (snapshot_financial snapshot) (0,17))
    (reference_history_prefixes rpf_live_history_after_dispatch)"

lemma rpe_actual_dispatch_keeps_the_source_units:
  "source_units (authoritative_reservation_state hf_dispatched) (0,17) =
    source_units (authoritative_reservation_state hf_reserved) (0,17)"
proof -
  have actual: "call_authority_state (product_calls hf_dispatched) =
    fst (sample.execute_finality_client hf_dispatch (call_authority_state (product_calls hf_reserved)))"
    unfolding prd_dispatch_reaches_the_actual_authority_step
    by (rule sample.finality_calls.first_dispatch_records_the_actual_execution(1)
        [OF prd_begun_fields(1), unfolded prd_begun_fields(2)])
  show ?thesis
    unfolding authoritative_reservation_state_def actual hf_dispatch_def sample.first_protocol_call_uses_the_current_core
    by (simp add: sample.finality_step_def sample.invoke_protocol_def lift_protocol_result_def dispatch_source_def
        record_observation_def commit_reservation_event_def set_phase_def Let_def split: option.splits if_splits)
qed

lemma rpe_prefix_units_code [code]:
  "rpe_prefix_units = [10,10,10]"
proof -
  have prefixes: "reference_history_prefixes rpf_live_history_after_dispatch =
      [rpf_prefix hf_initial, rpf_prefix hf_reserved, rpf_prefix hf_dispatched]"
    using rpf_read_prefixes_are_the_actual_revision_prefixes unfolding native_read_history_related_def by blast
  have reserved: "source_units (authoritative_reservation_state hf_reserved) (0,17) = 10"
    unfolding prd_reserved_state_comes_from_the_public_hold by (simp add: lock_example_public_defs)
  show ?thesis unfolding rpe_prefix_units_def prefixes
    by (simp add: rpf_prefix_def capture_snapshot_def authoritative_reservation_state_def[symmetric]
        hf_initial_source_amount_is_ten reserved rpe_actual_dispatch_keeps_the_source_units)
qed

definition rpe_handover_epoch :: nat where
  "rpe_handover_epoch = cut_authority_epoch (current_product_cut (hg_product_after True True))"

definition rpe_old_session :: "product_session_binding option" where
  "rpe_old_session = product_sessions (product_durable (hg_product_after True True)) 1"

definition rpe_new_owner :: "product_principal option" where
  "rpe_new_owner = owner_of_product (hg_product_after True True) 17"

lemma rpe_handover_epoch_code [code]: "rpe_handover_epoch = 10"
  using hg_normal_reuses_the_checked_native_product_relation(1)
    hg_normal_native_owner_sessions_epoch_and_immutable_ledger(7)
  by (simp add: rpe_handover_epoch_def rust_handover_matches_def)

lemma rpe_handover_session_code [code]: "rpe_old_session = None"
  using hg_normal_reuses_the_checked_native_product_relation(1)
    hg_normal_native_owner_sessions_epoch_and_immutable_ledger(3)
  by (simp add: rpe_old_session_def rust_handover_matches_def)

lemma rpe_handover_owner_code [code]: "rpe_new_owner = Some 8"
  using hg_normal_reuses_the_checked_native_product_relation(1)
    hg_normal_native_owner_sessions_epoch_and_immutable_ledger(2)
  by (simp add: rpe_new_owner_def rust_handover_matches_def)

thm_oracles rpe_original_reply_is_actual_acquisition rpe_reserve_entry_code rpe_dispatch_entry_code
  rpe_dispatch_frame_code rpe_reopened_frame_code rpe_prefix_units_code
  rpe_handover_epoch_code rpe_handover_session_code rpe_handover_owner_code

ML \<open>
  if null (Thm_Deps.all_oracles @{thms rpe_original_reply_is_actual_acquisition
      rpe_reserve_entry_code rpe_dispatch_entry_code rpe_dispatch_frame_code rpe_reopened_frame_code
      rpe_prefix_units_code rpe_handover_epoch_code rpe_handover_session_code rpe_handover_owner_code})
  then writeln "P13_REPLAY_EXPORT_FRAME_ORACLES_EMPTY"
  else error "Unexpected oracle in replay export frames"
\<close>

end
