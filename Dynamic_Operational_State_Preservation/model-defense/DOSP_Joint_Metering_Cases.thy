theory DOSP_Joint_Metering_Cases
  imports DOSP_Product_Progress
begin

abbreviation second_candidate_product where
  "second_candidate_product \<equiv> \<lparr>source_lifecycle = stale_local_clock_view, source_consensus = before_second_meter,
    source_recovery = published_recovery_state\<lparr>primary_sequence := 50, active_domains := {0,2,4},
      irreversible_facts := image prod_encode (core_published (credit_core pre_meter_operational))\<rparr>,
    observed_divergence_work = {}\<rparr>"

abbreviation second_publication_work where
  "second_publication_work \<equiv> Map.empty(8 \<mapsto> (2::nat),9 \<mapsto> 4,10 \<mapsto> 0)"

lemma second_native_proposal:
  "joined_dosp.run_registered_meter (cycle_ticket quoted_request) (cycle_session_id quoted_request)
    0 Bypass_Route (sample_request 23) before_second_meter =
      Some (actual_authority, Credit_Result (Some (Credit_Metered second_usage)))"
  using promoted_router_ticket_runs_the_actual_second_meter by simp

lemma a_real_native_success_proposal_does_not_escape_without_measurement:
  "joined_dosp.joint_credit_step Active_Credit_Route example_versions {}
    (measured_second_input\<lparr>verified_measurements := []\<rparr>) second_candidate_product quoted_request 0
    Bypass_Route (sample_request 23) Precommit_Refused second_candidate_product"
  by (subst joined_dosp.a_missing_final_measurement_cannot_publish_either_ledger)
     (simp_all add: checked_final_leaves_def)

theorem the_actual_eab_credit_and_matching_public_row_commit_together:
  "\<exists>q row. joined_dosp.joint_credit_step Active_Credit_Route example_versions {} measured_second_input second_candidate_product
      quoted_request 0 Bypass_Route (sample_request 23) (Cycle_Result (transition_result.Accepted Binding_Committed)) q \<and>
    source_consensus q = actual_authority \<and> row \<in> set (lifecycle_invoice (source_lifecycle q)) \<and>
    public_billing_day (usage_row_for_epoch row) = 1 \<and> public_meter_version (usage_row_for_epoch row) = 4 \<and>
    primary_sequence (source_recovery q) = 51 \<and> source_recovery q \<in> recovery_carrier \<and>
    source_recovery q = published_recovery_state\<lparr>active_domains := {0,2,4}, work_owner := second_publication_work\<rparr>"
proof -
  have names: "cycle_names_native_binding quoted_request (sample_request 23)"
    by (simp add: cycle_names_native_binding_def second_request_fields request_flow_def Let_def)
  obtain row t where steps:
    "lifecycle_step coupling_policy {(12,4)} example_versions {} measured_second_input
      (promotion_locks_clear coupling_policy pre_meter_operational) (stale_local_clock_view\<lparr>lifecycle_clock := 86400\<rparr>)
      (Commit_Cycle True) (Cycle_Result (transition_result.Accepted Binding_Committed)) t"
    "lifecycle_cutover t = degree_state (current_operational actual_authority)"
    "row \<in> set (lifecycle_invoice t)" "public_billing_day (usage_row_for_epoch row) = 1"
    "public_meter_version (usage_row_for_epoch row) = 4"
    using the_actual_second_credit_uses_consensus_day_one_even_if_the_local_clock_lags by blast
  have pair: "joined_dosp.joint_credit_candidate Active_Credit_Route example_versions {} measured_second_input second_candidate_product
     quoted_request 0 Bypass_Route (sample_request 23) t actual_authority"
    unfolding joined_dosp.joint_credit_candidate_def
    using steps(1,2) names second_native_proposal
    by (auto simp: routed_domains_are_active_def recovery_permits_native_credit_def recovery_permits_existing_native_credit_def Let_def
      published_recovery_state_def pending_ids_def coupling_policy_def second_request_fields second_meter_operational_fields(4,6)
      recorded_success_history_def accounted_cutover_entry_def first_accounted_usage_def joined_ticket_def coupling_ticket_def
      billing_record_def fixture_binding tariffs_cover_recorded_usage_def example_versions_def)
  let ?r = "source_recovery second_candidate_product"
  let ?after = "publication_recovery_state ?r actual_authority issued_second_receipt second_publication_work"
  let ?q = "second_candidate_product\<lparr>source_lifecycle := t, source_consensus := actual_authority, source_recovery := ?after\<rparr>"
  have work: "fresh_publication_work ?r second_publication_work"
    by (auto simp: fresh_publication_work_def published_recovery_state_def pending_ids_def inj_on_def Let_def
      split: if_splits intro: exI[of _ 8] exI[of _ 9] exI[of _ 10])
  have prior_facts: "irreversible_facts ?r \<subseteq> image prod_encode (core_published (credit_core (current_operational actual_authority)))"
    by (simp add: second_meter_operational_fields(1) second_meter_core_fields(2) actual_publication_fields(3))
  have issued: "issued_receipt actual_authority (next_publication_sequence before_second_meter) = Some issued_second_receipt"
    by (simp only: second_meter_operational_fields(7) actual_publication_fields(2))
  have key: "published_key issued_second_receipt = binding_key (request_binding (sample_request 23))"
    by (simp add: issued_second_receipt_def second_request_fields)
  have sequence: "published_sequence issued_second_receipt = next_publication_sequence before_second_meter"
    by (simp add: issued_second_receipt_def second_meter_operational_fields(7))
  have latest: "Suc (published_sequence issued_second_receipt) = next_publication_sequence actual_authority"
    by (simp add: issued_second_receipt_def the_same_asset_was_metered_and_published_on_both_sides_of_promotion(5))
  have advance: "joined_dosp.joint_publication_transition Active_Credit_Route example_versions {} measured_second_input second_candidate_product
      quoted_request 0 Bypass_Route (sample_request 23) ?q"
    unfolding joined_dosp.joint_publication_transition_def
    using pair work prior_facts issued key sequence latest
    by (intro exI[of _ t] exI[of _ actual_authority] exI[of _ issued_second_receipt] exI[of _ second_publication_work])
       (simp only: product_source_state.select_convs; blast)
  have accepted: "joined_dosp.joint_credit_step Active_Credit_Route example_versions {} measured_second_input second_candidate_product
     quoted_request 0 Bypass_Route (sample_request 23) (Cycle_Result (transition_result.Accepted Binding_Committed)) ?q"
    using advance by (auto simp: joined_dosp.joint_credit_step_def)
  have carrier: "?after \<in> recovery_carrier"
    using the_publication_carries_exact_fresh_work_for_its_stale_replicas[OF work] by blast
  have same_recovery: "?after = published_recovery_state\<lparr>active_domains := {0,2,4}, work_owner := second_publication_work\<rparr>"
    by (simp add: publication_recovery_state_def published_recovery_state_def actual_publication_fields(2) Let_def)
  have slot: "primary_sequence published_recovery_state = 51"
    by (simp add: published_recovery_state_def actual_publication_fields(2) issued_second_receipt_def Let_def)
  show ?thesis using accepted steps(3-5) carrier same_recovery
    by (intro exI[of _ ?q] exI[of _ row]) (simp add: slot)
qed

end
