theory Recovered_Source_Obligations
  imports Recovered_Observations
begin

datatype restart_source_action =
    No_Source_Obligation
  | Query_Exact_Source transfer_binding
  | Hold_Exact_Source transfer_binding
  | Consider_Confirmed_Source transfer_binding
  | Consider_Reversed_Source transfer_binding

definition open_source_binding where
  "open_source_binding source key =
    (case reservation_at (authoritative_reservation_state source) key of None \<Rightarrow> None
     | Some claim \<Rightarrow> if reservation_phase claim \<in> {Source_Submitted, Source_Pending}
       then Some (reservation_binding claim) else None)"

context source_attestation
begin

definition next_recovery_source_action where
  "next_recovery_source_action key evidence source =
    (case open_source_binding source key of None \<Rightarrow> No_Source_Obligation
     | Some binding \<Rightarrow> if call_connection (product_calls source) \<noteq> Authority_Connected
       then Hold_Exact_Source binding
       else (case evidence of None \<Rightarrow> Query_Exact_Source binding
        | Some cert \<Rightarrow> let statement = certificate_statement cert in
            if \<not> certificate_ok cert \<or> statement_binding statement \<noteq> binding then Hold_Exact_Source binding
            else case statement_status statement of
               Finalized \<Rightarrow> Consider_Confirmed_Source binding
             | Reversed \<Rightarrow> Consider_Reversed_Source binding
             | Observed \<Rightarrow> Hold_Exact_Source binding))"

lemma missing_evidence_requests_exact_source_or_holds:
  assumes "open_source_binding source key = Some binding"
  shows "next_recovery_source_action key None source \<in> {Query_Exact_Source binding, Hold_Exact_Source binding}"
  using assms by (simp add: next_recovery_source_action_def)

lemma mismatched_source_evidence_only_holds_the_exact_pending_binding:
  assumes "open_source_binding source key = Some binding"
    "statement_binding (certificate_statement cert) \<noteq> binding"
  shows "next_recovery_source_action key (Some cert) source = Hold_Exact_Source binding"
  using assms by (simp add: next_recovery_source_action_def Let_def)

lemma considered_reversal_has_exact_verified_source_evidence:
  assumes "next_recovery_source_action key evidence source = Consider_Reversed_Source binding"
  shows "open_source_binding source key = Some binding \<and>
     (\<exists>cert. evidence = Some cert \<and> certificate_ok cert \<and>
       certificate_statement cert = \<lparr>statement_binding = binding, statement_status = Reversed\<rparr>)"
  using assms by (auto simp: next_recovery_source_action_def Let_def split: option.splits if_splits source_status.splits)

lemma missing_or_wrong_reversal_cannot_move_the_source_balance:
  assumes "\<not> exact_record_reference s index (request_binding request) Reversed_Decision (request_certificate request)"
  shows "let result = execute_finality_client (Client_Protocol endpoint index (Return_Intent request generation versions)) s
     in machine_state (core_parent (fst result)) = machine_state (core_parent s)"
  using assms by (simp add: execute_finality_client_def finality_step_def invoke_protocol_def reject_protocol_intent_def
      record_observation_def Let_def)

end

end
