theory DOSP_Consensus_Billing_Cases
  imports DOSP_Native_Phases DOSP_Product_Recovery
begin

abbreviation quoted_request :: cycle_request where
  "quoted_request \<equiv> \<lparr>cycle_attempt_id = (34,7), cycle_session_id = (17,7,3),
    cycle_binding_id = prod_encode (0,23), cycle_ticket = joined_ticket 0 (promoted_metadata 12 4),
    cycle_source = 0, cycle_target = 2, cycle_value = 5\<rparr>"

definition first_accounted_usage :: accounted_cycle where
  "first_accounted_usage = \<lparr>accounted_attempt = (34,0), accounted_binding = prod_encode (0,17),
    accounted_session = (17,7,3), accounted_ticket = joined_ticket 0 coupling_ticket, accounted_clock = 86399,
    accounted_footprint = {0,2}, accounted_payload = 5, accounted_abort = None, accounted_tariff = 3,
    accounted_schedule = example_price\<rparr>"

abbreviation stale_local_clock_view :: lifecycle_state where
  "stale_local_clock_view \<equiv>
    \<lparr>lifecycle_cutover = degree_state pre_meter_operational, lifecycle_phase = Verified_Cycle quoted_request,
      lifecycle_clock = 86399, lifecycle_session = (17,7,3), lifecycle_tariff = 4,
      lifecycle_registry = authority_registry before_second_meter, cycle_custody = Native_Debit_Pending (0,23),
      lifecycle_diagnostic_authorities = {41}, lifecycle_invoice = [first_accounted_usage]\<rparr>"

abbreviation measured_second_input :: commit_evidence where
  "measured_second_input \<equiv> \<lparr>verified_observations = [],
    verified_measurements = [\<lparr>measuring_authority = 41, measured_request = quoted_request, measured_clock = 86400,
      measured_reply = transition_result.Accepted Binding_Committed,
      measured_write_domains = {0,2}, measured_final_leaves = {1,2,3,4,5}\<rparr>]\<rparr>"

theorem the_actual_second_credit_uses_consensus_day_one_even_if_the_local_clock_lags:
  "\<exists>row t. lifecycle_step coupling_policy grants example_versions {} measured_second_input locks
    (stale_local_clock_view\<lparr>lifecycle_clock := 86400\<rparr>) (Commit_Cycle True)
      (Cycle_Result (transition_result.Accepted Binding_Committed)) t \<and>
    lifecycle_cutover t = degree_state (current_operational actual_authority) \<and>
    row \<in> set (lifecycle_invoice t) \<and>
    public_billing_day (usage_row_for_epoch row) = 1 \<and> public_meter_version (usage_row_for_epoch row) = 4"
proof -
  let ?old = "metered_ledger before_second_meter"
  let ?prior = "set (map billed_consensus (committed_cycles ?old))"
  let ?epoch = "core_epoch (credit_core pre_meter_operational)"
  let ?ingress = "stale_local_clock_view\<lparr>lifecycle_clock := consensus_commit_second issued_second_cycle\<rparr>"
  have credit: "sample.meter_source_credit coupling_policy (consensus_route_ticket issued_second_cycle) ?epoch
    0 (consensus_publication_sequence issued_second_cycle) Bypass_Route (sample_request 23) pre_meter_operational =
    (second_metered_operational, Credit_Metered second_usage)"
    by (simp only: issued_second_cycle_def consensus_cycle.select_convs second_meter_is_the_actual_native_credit_and_publication)
  have admission: "(issued_second_cycle \<notin> insert issued_second_cycle ?prior
      \<or> \<not> unique_consensus_cycle (insert issued_second_cycle ?prior) issued_second_cycle
      \<or> consensus_binding issued_second_cycle \<noteq> binding_key (request_binding (sample_request 23))
      \<or> fst (consensus_session issued_second_cycle) \<noteq> binding_asset (request_binding (sample_request 23))) = False"
    by (simp add: unique_consensus_cycle_def second_meter_operational_fields(8) successful_cycle_def
        second_request_fields issued_second_cycle_def consensus_fixture_def)
  have accepted: "sample.meter_consensus_cycle coupling_policy (insert issued_second_cycle ?prior) issued_second_cycle
      ?epoch 0 Bypass_Route (sample_request 23) ?old = (metered_ledger actual_authority, Some (Credit_Metered second_usage))"
    unfolding joined_authority_normal_form
    by (simp only: sample.meter_consensus_cycle_def admission if_False Let_def credit fst_conv snd_conv
      metered_credit_reply.case; simp)
  have current: "binding_is_current coupling_policy ?ingress quoted_request"
    by (simp add: binding_is_current_def authority_registry_def ticket_authorizes_def issue_route_ticket_def
      joined_ticket_def request_flow_def can_commit_def coupling_policy_def second_meter_operational_fields
      billing_record_def promoted_metadata_def prod_encode_eq first_accounted_usage_def)
  have fields: "ticket_metadata (cycle_ticket quoted_request) = consensus_route_ticket issued_second_cycle"
    "cycle_session_id quoted_request = consensus_session issued_second_cycle"
    "cycle_names_native_binding quoted_request (sample_request 23)"
    "lifecycle_phase ?ingress = Verified_Cycle quoted_request"
    "lifecycle_cutover ?ingress = degree_state (operational_state ?old)"
    "checked_final_leaves measured_second_input ?ingress quoted_request (transition_result.Accepted Binding_Committed) = Some 5"
    "example_versions (lifecycle_tariff ?ingress) = Some example_price"
    by (simp_all add: issued_second_cycle_def joined_ticket_def cycle_names_native_binding_def second_request_fields
      request_flow_def example_versions_def checked_final_leaves_def Let_def)
  note same = sample.the_consensus_commit_drives_the_same_public_billing_day[
    where s=stale_local_clock_view and cycle=issued_second_cycle and versions=example_versions and
      evidence=measured_second_input and grants=grants and confirmed="{}" and locks=locks and precision=100,
    OF accepted fields(1-5) current fields(6-7),
    simplified issued_second_cycle_def consensus_cycle.select_convs]
  show ?thesis using same
    by (auto simp: successful_cycle_def billing_day_def billing_record_def promoted_metadata_def)
qed

end
