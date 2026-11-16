theory EAB_Billing_Cases
  imports EAB_Adapter_Cases DOSP_EAB_Coupling.EAB_Cycle_Accounting
begin

definition consensus_fixture :: "nat \<Rightarrow> consensus_cycle" where
  "consensus_fixture commit_second =
    \<lparr>consensus_session = (17, 7, 3), consensus_binding = (0, 17),
     consensus_publication_sequence = 50, consensus_commit_second = commit_second,
     consensus_route_ticket = coupling_ticket\<rparr>"

definition cycle_fixture :: cycle_ledger_state where
  "cycle_fixture = \<lparr>operational_state = meter_fixture, committed_cycles = []\<rparr>"

abbreviation fixture_billed_usage :: billing_entry where
  "fixture_billed_usage \<equiv> billing_record (prod_encode (0, 17)) coupling_ticket (transfer_commit (sample_binding 17))"

abbreviation run_consensus_fixture :: "nat \<Rightarrow> cycle_ledger_state \<times> metered_credit_reply option" where
  "run_consensus_fixture timestamp \<equiv> sample.meter_consensus_cycle coupling_policy {consensus_fixture timestamp}
    (consensus_fixture timestamp) fixture_epoch 0 Bypass_Route (sample_request 17) cycle_fixture"

lemma consensus_fixture_commits_the_actual_metered_operation:
  "operational_state (fst (run_consensus_fixture stamp)) = fst metered_fixture_result"
  "committed_cycles (fst (run_consensus_fixture stamp)) = [successful_cycle (consensus_fixture stamp) fixture_billed_usage]"
  "snd (run_consensus_fixture stamp) = Some (Credit_Metered fixture_billed_usage)"
  using metered_fixture_has_one_current_charge(2)
  by (simp_all add: sample.meter_consensus_cycle_def cycle_fixture_def consensus_fixture_def fixture_binding
      unique_consensus_cycle_def metered_fixture_result_def[symmetric] Let_def)

lemma same_registry_policy_charges_the_day_of_commit:
  "map settlement_day (committed_cycles (fst (run_consensus_fixture 86399))) = [0]"
  "map settlement_day (committed_cycles (fst (run_consensus_fixture 86400))) = [1]"
  "map billing_epoch (map billed_usage (committed_cycles (fst (run_consensus_fixture 86399)))) = [11]"
  "map billing_epoch (map billed_usage (committed_cycles (fst (run_consensus_fixture 86400)))) = [11]"
  unfolding consensus_fixture_commits_the_actual_metered_operation(2)
  by (simp_all add: successful_cycle_def
      consensus_fixture_def billing_day_def billing_record_def coupling_ticket_def)

lemma two_consensus_owners_cannot_claim_the_same_record:
  fixes alternative :: consensus_cycle
  defines "alternative \<equiv> (consensus_fixture 86400)\<lparr>consensus_session := (17, 29, 4)\<rparr>"
  shows "sample.meter_consensus_cycle coupling_policy {consensus_fixture 86399, alternative}
    (consensus_fixture 86399) fixture_epoch 0 Bypass_Route (sample_request 17) cycle_fixture = (cycle_fixture, None)"
  and "sample.meter_consensus_cycle coupling_policy {consensus_fixture 86399, alternative}
    alternative fixture_epoch 0 Bypass_Route (sample_request 17) cycle_fixture = (cycle_fixture, None)"
proof -
  let ?admitted = "{consensus_fixture 86399, alternative}"
  have different: "alternative \<noteq> consensus_fixture 86399"
    and same_key: "consensus_binding alternative = consensus_binding (consensus_fixture 86399)"
    by (simp_all add: alternative_def consensus_fixture_def)
  show "sample.meter_consensus_cycle coupling_policy ?admitted
    (consensus_fixture 86399) fixture_epoch 0 Bypass_Route (sample_request 17) cycle_fixture = (cycle_fixture, None)"
    by (rule sample.ambiguous_consensus_record_is_rejected_before_operational_metering[where other = alternative])
      (simp_all add: different same_key)
  show "sample.meter_consensus_cycle coupling_policy ?admitted
    alternative fixture_epoch 0 Bypass_Route (sample_request 17) cycle_fixture = (cycle_fixture, None)"
    by (rule sample.ambiguous_consensus_record_is_rejected_before_operational_metering[where other = "consensus_fixture 86399"])
      (use different same_key in auto)
qed

end
