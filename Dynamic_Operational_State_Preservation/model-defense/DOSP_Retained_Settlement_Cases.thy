theory DOSP_Retained_Settlement_Cases
  imports DOSP_Admission_Cases
begin

lemma second_native_source_is_already_debited_and_confirmed:
  "retained_credit_admission second_candidate_product quoted_request 0 (sample_request 23)"
proof -
  have debited_source: "current_lock_view second_debited_core 0 = sample_source_context ACTIVE"
    unfolding second_debited_form
    by (simp add: with_finality_core_def with_operational_state_def current_lock_view_def
      finality_sample_current_contexts(1)[unfolded current_lock_view_def])
  have recorded: "second_recorded_core = fst (sample.execute_finality_client
      (Client_Terminal (sample_certificate 23)) second_debited_core)"
    unfolding second_recorded_core_def second_recorded_form second_confirmation_records_the_actual_terminal fst_conv
    by (simp add: with_finality_core_def with_operational_state_def Let_def)
  have recording_keeps_view:
    "current_lock_view (fst (sample.execute_finality_client (Client_Terminal cert) core)) endpoint =
      current_lock_view core endpoint" for cert core endpoint
    by (simp add: sample.execute_finality_client_def sample.finality_step_def
      sample.terminal_recording_preserves_current_view current_view_ignores_internal_epoch_update)
  have source: "current_lock_view second_meter_core 0 = sample_source_context ACTIVE"
    unfolding second_meter_core_def recorded
    by (simp only: non_context_updates_keep_the_lock_view current_view_ignores_internal_epoch_update
      recording_keeps_view debited_source)
  have terminal: "exact_record_reference second_meter_core 0 (request_binding (sample_request 23))
      Confirmed_Decision (request_certificate (sample_request 23))"
    by (simp add: exact_record_reference_def record_reference_def second_meter_core_fields(1) second_request_fields)
  note actual_core = second_meter_operational_fields(1)
  note trace = second_meter_core_fields(4) second_burned_machine_def sample_credited_state advance_reservation_time_def
    sample_confirmed_record_def staged_trace_defs
  have pending: "native_source_pending pre_meter_operational (sample_request 23)"
    by (simp add: native_source_pending_def actual_core trace second_request_fields)
  have debit: "source_was_debited (machine_state (core_parent second_meter_core)) (0,23)"
    by (simp add: trace source_was_debited_def)
  have held: "current_binding_holds_its_native_lock pre_meter_operational (sample_request 23)"
    by (simp add: current_binding_holds_its_native_lock_def actual_core source trace second_request_fields
      sample_source_context_def sample_context_def current_use_allowed_def)
  show ?thesis
    unfolding retained_credit_admission_def
    using pending debit held terminal
    by (simp add: cycle_names_native_binding_def request_flow_def actual_core second_meter_core_fields(2) second_request_fields Let_def)
qed

abbreviation retired_before_settlement where
  "retired_before_settlement \<equiv> second_candidate_product\<lparr>source_recovery :=
    (source_recovery second_candidate_product)\<lparr>active_domains := {2,4}, route_epoch := 2\<rparr>\<rparr>"

abbreviation leave_origin_grant where
  "leave_origin_grant \<equiv> {(Leave_Domain (0::nat) 4,2,86400)}"

theorem retired_origin_can_only_settle_its_already_debited_binding:
  "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
     leave_origin_grant second_candidate_product (Update_Recovery (Activate_Route (Leave_Domain 0 4) 2 86400))
     (Recovery_Outcome (transition_result.Accepted (Left 0 4))) retired_before_settlement"
  "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
     leave_origin_grant retired_before_settlement (Meter_Native quoted_request 0 Bypass_Route (sample_request 23))
     (Binding_Outcome Precommit_Refused) retired_before_settlement"
  "\<exists>q. joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
     leave_origin_grant retired_before_settlement (Settle_Retained_Native quoted_request 0 Bypass_Route (sample_request 23))
       (Binding_Outcome (Cycle_Result (transition_result.Accepted Binding_Committed))) q \<and>
     source_consensus q = actual_authority \<and> primary_sequence (source_recovery q) = 51"
proof -
  let ?old = "source_recovery second_candidate_product"
  let ?retired = "source_recovery retired_before_settlement"
  have leave: "recovery_step leave_origin_grant {} ?old (Activate (Leave_Domain 0 4) 2 86400 86400)
      (transition_result.Accepted (Left 0 4)) ?retired"
  proof -
    have step: "recovery_step leave_origin_grant {} ?old (Activate (Leave_Domain 0 4) 2 86400 86400)
      (transition_result.Accepted (Left 0 4))
      (?old\<lparr>active_domains := active_domains ?old - {0}, route_epoch := 2,
        work_owner := carry_owner 0 4 (work_owner ?old)\<rparr>)"
      by (rule recovery_step.Leave_Route)
         (simp_all add: current_grant_def published_recovery_state_def Let_def)
    have empty: "carry_owner (0::nat) 4 Map.empty = Map.empty"
      by (rule ext) (simp add: carry_owner_def)
    show ?thesis using step by (simp add: published_recovery_state_def empty Let_def)
  qed
  show "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
     leave_origin_grant second_candidate_product (Update_Recovery (Activate_Route (Leave_Domain 0 4) 2 86400))
     (Recovery_Outcome (transition_result.Accepted (Left 0 4))) retired_before_settlement"
    using leave
    by (auto simp: joined_dosp.product_source_step_def joined_dosp.product_recovery_step_def
      joined_dosp.consensus_membership_step_def joined_dosp.activation_uses_the_existing_grant_and_handoff
      earlier_route_update_is_pending_def route_grant_matches_its_epoch_def
      second_meter_operational_fields(6) published_recovery_state_def Let_def)
  have refused: "joined_dosp.joint_credit_step Active_Credit_Route example_versions {} measured_second_input
    retired_before_settlement quoted_request 0 Bypass_Route (sample_request 23) Precommit_Refused retired_before_settlement"
    by (subst joined_dosp.an_exited_origin_cannot_start_a_new_native_credit)
      (simp_all add: second_request_fields)
  show "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
     leave_origin_grant retired_before_settlement (Meter_Native quoted_request 0 Bypass_Route (sample_request 23))
     (Binding_Outcome Precommit_Refused) retired_before_settlement"
    using refused by (simp add: joined_dosp.product_source_step_def outstanding_join_jobs_def Let_def split: if_splits)
  obtain q where existing: "joined_dosp.joint_credit_step Active_Credit_Route example_versions {} measured_second_input
        second_candidate_product quoted_request 0 Bypass_Route (sample_request 23)
        (Cycle_Result (transition_result.Accepted Binding_Committed)) q"
    and source: "source_consensus q = actual_authority"
    using the_actual_eab_credit_and_matching_public_row_commit_together by blast
  have original: "joined_dosp.joint_credit_candidate Active_Credit_Route example_versions {} measured_second_input
        second_candidate_product quoted_request 0 Bypass_Route (sample_request 23) (source_lifecycle q) actual_authority"
    using joined_dosp.a_confirmed_joint_credit_requires_both_linked_effects[OF existing, THEN conjunct1]
    by (simp only: source)
  have same_admission: "retained_credit_admission retired_before_settlement quoted_request 0 (sample_request 23) =
      retained_credit_admission second_candidate_product quoted_request 0 (sample_request 23)"
    by (simp add: retained_credit_admission_def Let_def)
  have held: "retained_credit_admission retired_before_settlement quoted_request 0 (sample_request 23)"
    by (simp only: same_admission second_native_source_is_already_debited_and_confirmed)
  have candidate: "joined_dosp.joint_credit_candidate Retained_Debit_Route example_versions {} measured_second_input
        retired_before_settlement quoted_request 0 Bypass_Route (sample_request 23) (source_lifecycle q) actual_authority"
    by (rule joined_dosp.a_verified_debit_can_settle_after_its_original_route_exits[
      where retired=retired_before_settlement and p=second_candidate_product and versions=example_versions,
      OF original _ _ held])
      (simp_all add: published_recovery_state_def pending_ids_def Let_def)
  let ?work = "Map.empty(8 \<mapsto> (2::nat),9 \<mapsto> 4)"
  let ?after = "publication_recovery_state ?retired actual_authority issued_second_receipt ?work"
  let ?settled = "retired_before_settlement\<lparr>source_lifecycle := source_lifecycle q,
    source_consensus := actual_authority, source_recovery := ?after\<rparr>"
  have work: "fresh_publication_work ?retired ?work"
    by (auto simp: fresh_publication_work_def published_recovery_state_def pending_ids_def inj_on_def Let_def
      split: if_splits intro: exI[of _ 8] exI[of _ 9])
  have prior: "irreversible_facts ?retired \<subseteq> image prod_encode (core_published (credit_core (current_operational actual_authority)))"
    by (simp add: second_meter_operational_fields(1) second_meter_core_fields(2) actual_publication_fields(3))
  have earlier: "next_publication_sequence before_second_meter = 51" by (rule second_meter_operational_fields(7))
  have later: "next_publication_sequence actual_authority = 52"
    by (rule the_same_asset_was_metered_and_published_on_both_sides_of_promotion(5))
  have slot: "issued_receipt actual_authority (next_publication_sequence before_second_meter) = Some issued_second_receipt"
    by (simp only: earlier actual_publication_fields(2))
  have key: "published_key issued_second_receipt = binding_key (request_binding (sample_request 23))"
    by (simp add: issued_second_receipt_def second_request_fields)
  have seq: "published_sequence issued_second_receipt = next_publication_sequence before_second_meter"
    by (simp add: issued_second_receipt_def earlier)
  have next_slot: "Suc (published_sequence issued_second_receipt) = next_publication_sequence actual_authority"
    by (simp add: issued_second_receipt_def later)
  have retained_consensus: "source_consensus retired_before_settlement = before_second_meter"
    by simp
  have retired_slot: "issued_receipt actual_authority (next_publication_sequence (source_consensus retired_before_settlement)) =
    Some issued_second_receipt"
    by (simp only: retained_consensus slot)
  have retired_seq: "published_sequence issued_second_receipt = next_publication_sequence (source_consensus retired_before_settlement)"
    by (simp only: retained_consensus seq)
  have publication: "joined_dosp.joint_publication_transition Retained_Debit_Route example_versions {} measured_second_input
       retired_before_settlement quoted_request 0 Bypass_Route (sample_request 23) ?settled"
    unfolding joined_dosp.joint_publication_transition_def
    using candidate work prior retired_slot key retired_seq next_slot
    by (intro exI[of _ "source_lifecycle q"] exI[of _ actual_authority] exI[of _ issued_second_receipt] exI[of _ ?work])
      blast
  have kept: "joined_dosp.joint_credit_step Retained_Debit_Route example_versions {} measured_second_input
       retired_before_settlement quoted_request 0 Bypass_Route (sample_request 23)
       (Cycle_Result (transition_result.Accepted Binding_Committed)) ?settled"
    using publication by (auto simp: joined_dosp.joint_credit_step_def)
  have product_steps: "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
     leave_origin_grant retired_before_settlement (Settle_Retained_Native quoted_request 0 Bypass_Route (sample_request 23))
       (Binding_Outcome (Cycle_Result (transition_result.Accepted Binding_Committed))) ?settled"
    unfolding joined_dosp.product_source_step_def using kept by (simp add: outstanding_join_jobs_def Let_def)
  show "\<exists>q. joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
     leave_origin_grant retired_before_settlement (Settle_Retained_Native quoted_request 0 Bypass_Route (sample_request 23))
       (Binding_Outcome (Cycle_Result (transition_result.Accepted Binding_Committed))) q \<and>
     source_consensus q = actual_authority \<and> primary_sequence (source_recovery q) = 51"
    using product_steps by (intro exI[of _ ?settled])
      (simp add: publication_recovery_state_def issued_second_receipt_def)
qed

end
