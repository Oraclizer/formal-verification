theory Legal_Product
  imports Legal_Admission
begin

datatype legal_execution_reply = Legal_Blocked legal_refusal | Legal_Checked checked_execution_reply

fun regulatory_lock_entry where
  "regulatory_lock_entry Regulatory_Normal = Normal_Lock_Entry"
| "regulatory_lock_entry Regulatory_Administrative = Administrative_Lock_Entry"
| "regulatory_lock_entry Regulatory_Adapter = Adapter_Lock_Entry"
| "regulatory_lock_entry Regulatory_Force_Inclusion = Adapter_Lock_Entry"

definition binding_fulfils_legal_order where
  "binding_fulfils_legal_order order binding \<longleftrightarrow>
    binding = legal_binding order \<and> binding_key binding = legal_origin order \<and>
    binding_asset binding = legal_asset order \<and> binding_operation binding = Regulatory_State_Effect (legal_action order) \<and>
    (\<forall>destination. legal_destination order = Some destination \<longrightarrow> binding_recipient binding = destination)"

definition legal_payload_is_exact where
  "legal_payload_is_exact stage order payload \<longleftrightarrow>
    (let envelope = payload_envelope payload in
      envelope_origin envelope = legal_origin order \<and> envelope_asset envelope = legal_asset order \<and>
      payload_origin_epoch payload = legal_issuance_epoch order \<and>
      (case (stage, envelope_command envelope) of
         (Legal_Source_Emission, Client_Terminal cert) \<Rightarrow>
           statement_status (certificate_statement cert) = Finalized \<and>
           binding_fulfils_legal_order order (statement_binding (certificate_statement cert))
       | (Legal_Receiving_Commit, Client_Regulatory endpoint index request) \<Rightarrow>
           binding_fulfils_legal_order order (request_binding request)
       | _ \<Rightarrow> False))"

definition retain_issued_legal_order where
  "retain_issued_legal_order order s =
    (if issued_legal_orders s (legal_origin order) = None then
       s\<lparr>issued_legal_orders := (issued_legal_orders s)(legal_origin order := Some order)\<rparr> else s)"

definition retain_committed_legal_event where
  "retain_committed_legal_event order commit_cut s =
    (let key = legal_origin order; asset = legal_asset order;
         entry = \<lparr>applied_order = order, applied_legal_cut = commit_cut\<rparr>;
         retained = s\<lparr>committed_legal_events := (committed_legal_events s)(key := Some entry)\<rparr>
     in if committed_legal_events s key \<noteq> None then s
        else case legal_action order of
          FREEZE \<Rightarrow> retained\<lparr>active_freeze_event := (active_freeze_event s)(asset := Some key)\<rparr>
        | SEIZE \<Rightarrow> retained\<lparr>active_seizure_event := (active_seizure_event s)(asset := Some key)\<rparr>
        | UNFREEZE \<Rightarrow> retained\<lparr>active_freeze_event := (active_freeze_event s)(asset := None)\<rparr>
        | RELEASE \<Rightarrow> retained\<lparr>active_freeze_event := (active_freeze_event s)(asset := None),
              active_seizure_event := (active_seizure_event s)(asset := None)\<rparr>
        | _ \<Rightarrow> retained)"

definition legal_underlying_outcomes where
  "legal_underlying_outcomes s = origin_outcomes (settlement_primary (read_authority (legal_reads s)))"

definition retain_actual_legal_result where
  "retain_actual_legal_result stage order call_id payload commit_cut previous next =
    (if outcome_entries (legal_underlying_outcomes previous) call_id \<noteq> None then next
     else case outcome_entries (legal_underlying_outcomes next) call_id of None \<Rightarrow> next
     | Some recorded \<Rightarrow> if result_payload recorded \<noteq> payload then next
       else case (stage, result_outcome recorded) of
         (Legal_Source_Emission, Authority_Reply Terminal_Recorded) \<Rightarrow> retain_issued_legal_order order next
       | (Legal_Source_Emission, Authority_Reply Evidence_Refreshed) \<Rightarrow> retain_issued_legal_order order next
       | (Legal_Receiving_Commit, Authority_Reply Regulatory_Applied) \<Rightarrow> retain_committed_legal_event order commit_cut next
       | _ \<Rightarrow> next)"

context source_attestation
begin

definition run_legal_effect where
  "run_legal_effect legal_grant order_verified permitted verified maintainers registered verified_ack
      stage entry who expected call_id order payload s =
    (case legal_admission_at_cut legal_grant order_verified stage entry who order s of
       Legal_Refuse reason \<Rightarrow> (s, Legal_Blocked reason)
     | Legal_Admit \<Rightarrow> if \<not> legal_payload_is_exact stage order payload then (s, Legal_Blocked Invalid_Legal_Binding)
       else let result = execute_at_checked_cut permitted verified maintainers registered verified_ack
             (regulatory_lock_entry entry) who expected call_id payload (legal_reads s);
           next = s\<lparr>legal_reads := fst result\<rparr>
         in (retain_actual_legal_result stage order call_id payload (legal_current_cut s) s next, Legal_Checked (snd result)))"

lemma any_rejected_legal_entry_preserves_all_authority_state:
  assumes "snd (run_legal_effect legal_grant order_verified permitted verified maintainers registered verified_ack
      stage entry who expected call_id order payload s) = Legal_Blocked reason"
  shows "fst (run_legal_effect legal_grant order_verified permitted verified maintainers registered verified_ack
      stage entry who expected call_id order payload s) = s"
  using assms by (auto simp: run_legal_effect_def Let_def split: legal_admission.splits if_splits)

lemma missing_prior_seizure_rejects_before_source_or_receiver_changes:
  assumes "legal_admission_at_cut legal_grant order_verified stage entry who order s = Legal_Refuse Missing_Prior_Seizure"
  shows "run_legal_effect legal_grant order_verified permitted verified maintainers registered verified_ack
      stage entry who expected call_id order payload s = (s, Legal_Blocked Missing_Prior_Seizure)"
  using assms by (simp add: run_legal_effect_def)

lemma confiscation_forwarding_consumes_the_current_seizure_and_deadline:
  assumes "legal_action order = CONFISCATE"
    "snd (run_legal_effect legal_grant order_verified permitted verified maintainers registered verified_ack
      stage entry who expected call_id order payload s) = Legal_Checked Forwarded_At_Checked_Cut"
  shows "legal_current_state s (fst (legal_origin order)) (legal_asset order) = Some SEIZED \<and>
    exact_legal_predecessor s order (active_seizure_event s (legal_asset order)) SEIZE \<and>
    appeal_has_elapsed s order \<and> legal_destination order \<noteq> None"
proof -
  have admit: "legal_admission_at_cut legal_grant order_verified stage entry who order s = Legal_Admit"
    using assms(2) by (cases "legal_admission_at_cut legal_grant order_verified stage entry who order s")
      (simp_all add: run_legal_effect_def)
  have state_admit: "legal_state_gate s order = Legal_Admit"
    using admit by (simp add: legal_admission_at_cut_def split: if_splits)
  show ?thesis by (rule confiscation_requires_current_seizure_and_elapsed_appeal[OF assms(1) state_admit])
qed

end

end
