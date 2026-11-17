theory DOSP_Integrated_Defense
  imports DOSP_Lifecycle_Defense_Cases DOSP_Repair_Boundaries
begin

lemma promoted_router_ticket_runs_the_actual_second_meter:
  "joined_dosp.run_registered_meter (joined_ticket 0 (promoted_metadata 12 4)) (17,7,3) 0 Bypass_Route
    (sample_request 23) before_second_meter = Some (actual_authority, Credit_Result (Some (Credit_Metered second_usage)))"
proof -
  have guard: "ticket_authorizes (authority_registry before_second_meter) coupling_policy
    (binding_asset (request_binding (sample_request 23))) (joined_ticket 0 (promoted_metadata 12 4))
    (transfer_commit (request_binding (sample_request 23)))"
    by (simp add: ticket_authorizes_def issue_route_ticket_def authority_registry_def joined_ticket_def
      second_meter_operational_fields second_request_fields promoted_metadata_def coupling_policy_def)
  have charge: "snd (joined_dosp.execute_integrated_client second_meter before_second_meter) =
    Credit_Result (Some (Credit_Metered second_usage))"
  proof -
    have native: "sample.meter_source_credit coupling_policy (promoted_metadata 12 4) (core_epoch second_meter_core)
      0 51 Bypass_Route (sample_request 23) pre_meter_operational =
      (second_metered_operational, Credit_Metered second_usage)"
      using second_meter_is_the_actual_native_credit_and_publication
      by (simp only: second_meter_operational_fields(1))
    show ?thesis by (simp add: Let_def sample.meter_consensus_cycle_def unique_consensus_cycle_def
      second_request_fields second_meter_operational_fields issued_second_cycle_def consensus_fixture_def
      successful_cycle_def native)
  qed
  have actual: "joined_dosp.execute_integrated_client second_meter before_second_meter =
    (actual_authority, Credit_Result (Some (Credit_Metered second_usage)))"
    using charge final_authority_runs_the_second_meter by (metis prod.collapse)
  show ?thesis using joined_dosp.authorized_registry_meter_calls_the_native_meter[OF guard,
     where session="(17,7,3)" and index=0 and route=Bypass_Route]
    by (simp only: joined_ticket_def route_ticket.select_convs actual)
qed

theorem the_promoted_router_bill_names_the_publication_used_by_handed_off_recovery:
  "joined_dosp.run_registered_meter (joined_ticket 0 (promoted_metadata 12 4)) (17,7,3) 0 Bypass_Route
    (sample_request 23) before_second_meter = Some (actual_authority, Credit_Result (Some (Credit_Metered second_usage))) \<and>
   (\<exists>cycle. successful_cycle cycle second_usage \<in> set (committed_cycles (metered_ledger actual_authority)) \<and>
      consensus_session cycle = (17,7,3) \<and> consensus_binding cycle = head_key current_repair_head \<and>
      consensus_publication_sequence cycle = head_sequence current_repair_head \<and>
      consensus_commit_second cycle = 86400 \<and> consensus_route_ticket cycle = promoted_metadata 12 4) \<and>
   joined_dosp.select_current_publication two_journals current_repair_head [prior_offer,live_offer]
      (route_epoch handed_off_recovery) = Some (current_publication_authority actual_authority, issued_second_receipt) \<and>
   joined_dosp.offered_recovery_step two_journals current_repair_head [prior_offer,live_offer]
      joined_recovery_grants {} handed_off_recovery (Apply_Repair 8 51)
      (transition_result.Accepted (Installed 8 6 51)) after_job_eight \<and>
   joined_dosp.offered_recovery_step two_journals current_repair_head [live_offer,prior_offer]
      joined_recovery_grants {} after_job_nine (Ordinary_Trade 23) (transition_result.Accepted (Traded 23)) after_job_nine"
proof -
  have bill: "\<exists>cycle. successful_cycle cycle second_usage \<in> set (committed_cycles (metered_ledger actual_authority)) \<and>
      consensus_session cycle = (17,7,3) \<and> consensus_binding cycle = head_key current_repair_head \<and>
      consensus_publication_sequence cycle = head_sequence current_repair_head \<and>
      consensus_commit_second cycle = 86400 \<and> consensus_route_ticket cycle = promoted_metadata 12 4"
    using joined_dosp.registry_routing_and_billing_use_the_same_request[OF promoted_router_ticket_runs_the_actual_second_meter]
    by (auto simp: current_repair_head_def second_meter_operational_fields second_request_fields joined_ticket_def)
  show ?thesis
    using bill promoted_router_ticket_runs_the_actual_second_meter current_source_chosen_from_two_actual_histories(1)
      current_publication_retry_completes_the_carried_job_and_restores_trading(3,6)
      handoff_has_a_real_primary_and_current_epoch(1)
    by force
qed

end
