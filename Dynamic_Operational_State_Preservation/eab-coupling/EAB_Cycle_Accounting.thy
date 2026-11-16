theory EAB_Cycle_Accounting
  imports EAB_Binding_Cutover
begin

type_synonym oracle_session_identity = "nat \<times> nat \<times> nat"

record consensus_cycle =
  consensus_session :: oracle_session_identity
  consensus_binding :: source_key
  consensus_publication_sequence :: nat
  consensus_commit_second :: nat
  consensus_route_ticket :: cutover_metadata

record billed_cycle =
  billed_consensus :: consensus_cycle
  billed_usage :: billing_entry
  settlement_day :: nat

record cycle_ledger_state =
  operational_state :: metered_source_state
  committed_cycles :: "billed_cycle list"

text \<open>The timestamp counts consensus seconds since the Epoch Manager's
  epoch origin. The Registry policy cutover and the accounting clock have
  independent sources. The admitted consensus record binds that clock to the
  same session, source key, and public sequence as the charged operation.\<close>

definition billing_day :: "nat \<Rightarrow> nat" where
  "billing_day elapsed = elapsed div 86400"

definition successful_cycle :: "consensus_cycle \<Rightarrow> billing_entry \<Rightarrow> billed_cycle" where
  "successful_cycle cycle entry = \<lparr>billed_consensus = cycle, billed_usage = entry,
    settlement_day = billing_day (consensus_commit_second cycle)\<rparr>"

definition unique_consensus_cycle :: "consensus_cycle set \<Rightarrow> consensus_cycle \<Rightarrow> bool" where
  "unique_consensus_cycle admitted cycle \<longleftrightarrow>
    (\<forall>other\<in>admitted. consensus_binding other = consensus_binding cycle \<or>
      consensus_publication_sequence other = consensus_publication_sequence cycle \<longrightarrow> other = cycle)"

context source_attestation
begin

definition meter_consensus_cycle ::
  "nat flow_policy \<Rightarrow> consensus_cycle set \<Rightarrow> consensus_cycle \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    message_route \<Rightarrow> execution_request \<Rightarrow> cycle_ledger_state \<Rightarrow>
    cycle_ledger_state \<times> metered_credit_reply option"
where
  "meter_consensus_cycle p admitted cycle epoch index route r s =
    (if cycle \<notin> admitted \<or> \<not> unique_consensus_cycle admitted cycle \<or>
        consensus_binding cycle \<noteq> binding_key (request_binding r) \<or>
        fst (consensus_session cycle) \<noteq> binding_asset (request_binding r)
     then (s, None)
     else let raw = meter_source_credit p (consensus_route_ticket cycle) epoch index
                      (consensus_publication_sequence cycle) route r (operational_state s);
              next = s\<lparr>operational_state := fst raw\<rparr>
          in case snd raw of
            Credit_Metered entry \<Rightarrow>
              (next\<lparr>committed_cycles := committed_cycles s @ [successful_cycle cycle entry]\<rparr>,
               Some (Credit_Metered entry))
          | outcome \<Rightarrow> (next, Some outcome))"

theorem consensus_cycle_records_the_same_success_on_its_billing_day:
  assumes "meter_consensus_cycle p admitted cycle epoch index route r s = (t, Some (Credit_Metered entry))"
  shows "cycle \<in> admitted \<and> unique_consensus_cycle admitted cycle \<and>
    consensus_binding cycle = binding_key (request_binding r) \<and>
    fst (consensus_session cycle) = binding_asset (request_binding r) \<and>
    meter_source_credit p (consensus_route_ticket cycle) epoch index
      (consensus_publication_sequence cycle) route r (operational_state s) = (operational_state t, Credit_Metered entry) \<and>
    committed_cycles t = committed_cycles s @ [successful_cycle cycle entry] \<and>
    settlement_day (successful_cycle cycle entry) = consensus_commit_second cycle div 86400"
  using assms
  by (auto simp: meter_consensus_cycle_def successful_cycle_def billing_day_def Let_def
      split: if_splits metered_credit_reply.splits intro: prod_eqI)

lemma another_binding_cannot_take_the_consensus_cycle:
  assumes "consensus_binding cycle \<noteq> binding_key (request_binding r)"
  shows "meter_consensus_cycle p admitted cycle epoch index route r s = (s, None)"
  using assms by (simp add: meter_consensus_cycle_def)

lemma ambiguous_consensus_record_is_rejected_before_operational_metering:
  assumes "other \<in> admitted" "other \<noteq> cycle"
    "consensus_binding other = consensus_binding cycle \<or>
      consensus_publication_sequence other = consensus_publication_sequence cycle"
  shows "meter_consensus_cycle p admitted cycle epoch index route r s = (s, None)"
  using assms by (auto simp: meter_consensus_cycle_def unique_consensus_cycle_def)

end

end
