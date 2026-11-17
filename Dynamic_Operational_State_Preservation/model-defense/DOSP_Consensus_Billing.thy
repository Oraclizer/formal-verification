theory DOSP_Consensus_Billing
  imports DOSP_Native_Lifecycle
begin

context source_attestation
begin

theorem the_consensus_commit_drives_the_same_public_billing_day:
  fixes s :: lifecycle_state and cycle :: consensus_cycle
  defines "recorded \<equiv> s\<lparr>lifecycle_clock := consensus_commit_second cycle\<rparr>"
  assumes actual: "meter_consensus_cycle policy admitted cycle epoch index route r native =
      (native_after, Some (Credit_Metered native_row))"
    and ticket: "ticket_metadata (cycle_ticket request) = consensus_route_ticket cycle"
    and session: "cycle_session_id request = consensus_session cycle"
    and binding: "cycle_names_native_binding request r"
    and phase: "lifecycle_phase recorded = Verified_Cycle request"
    and projection: "lifecycle_cutover recorded = degree_state (operational_state native)"
    and current: "binding_is_current policy recorded request"
    and footprint: "checked_final_leaves evidence recorded request (transition_result.Accepted Binding_Committed) = Some leaves"
    and tariff: "versions (lifecycle_tariff recorded) = Some schedule"
  shows "\<exists>row t. successful_cycle cycle native_row \<in> set (committed_cycles native_after) \<and>
    lifecycle_step policy grants versions confirmed evidence locks recorded
      (Commit_Cycle True) (Cycle_Result (transition_result.Accepted Binding_Committed)) t \<and>
    lifecycle_cutover t = degree_state (operational_state native_after) \<and>
    row \<in> set (lifecycle_invoice t) \<and> accounted_binding row = binding_id native_row \<and>
    public_session (usage_row_for_epoch row) = consensus_session cycle \<and>
    public_billing_day (usage_row_for_epoch row) = settlement_day (successful_cycle cycle native_row) \<and>
    public_meter_version (usage_row_for_epoch row) = billing_version native_row \<and>
    charge_from_public_row precision versions (usage_row_for_epoch row) = Some (charge_of precision row)"
proof -
  note billed = consensus_cycle_records_the_same_success_on_its_billing_day[OF actual]
  from billed ticket have native_credit:
    "meter_source_credit policy (ticket_metadata (cycle_ticket request)) epoch index (consensus_publication_sequence cycle)
      route r (operational_state native) = (operational_state native_after, Credit_Metered native_row)" by simp
  have published: "successful_cycle cycle native_row \<in> set (committed_cycles native_after)"
    using billed by simp
  note same_row = the_native_credit_consumes_the_same_binding_and_public_meter_row[
    where s=recorded and versions=versions and evidence=evidence and request=request and
      grants=grants and confirmed=confirmed and locks=locks and precision=precision,
    OF native_credit binding phase projection current footprint tariff]
  show ?thesis using published same_row session
    unfolding recorded_def successful_cycle_def billing_day_def by auto
qed

end

end
