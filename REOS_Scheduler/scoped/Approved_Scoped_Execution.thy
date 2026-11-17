theory Approved_Scoped_Execution
  imports Mixed_Service_Example Verified_Rollback_Authority
begin

fun policy_allows :: "verified_inputs \<Rightarrow> rollback_state \<Rightarrow> packet_body \<Rightarrow> bool" where
  "policy_allows inputs s (Execute_Governed_Rollback r a rp) =
    (\<exists>q t. checked_rollback inputs s r a rp = (Accepted q, t))"
| "policy_allows _ _ (Ordinary_Work _) = True"
| "policy_allows _ _ (Raise_Level _ _) = True"
| "policy_allows _ _ (Lower_Level _ _) = True"

definition scoped_submit ::
  "verified_inputs \<Rightarrow> scheduler_state \<Rightarrow> packet \<Rightarrow> scheduler_result \<times> scheduler_state"
where
  "scoped_submit inputs s p =
    (case admit s p of (Accepted q, t) \<Rightarrow>
        if policy_allows inputs (rollback_context s) (packet_contents p)
        then (Accepted q, t) else (Rejected Regulation_Ineligible, s)
      | result \<Rightarrow> result)"

definition authorized_view :: "verified_inputs \<Rightarrow> scheduler_state \<Rightarrow> scheduler_state" where
  "authorized_view inputs s = s\<lparr>regulatory_queue :=
    filter (\<lambda>p. policy_allows inputs (rollback_context s) (packet_contents p)) (regulatory_queue s)\<rparr>"

definition planned :: "scheduler_state \<Rightarrow> packet option" where
  "planned s = (case next_regulation s of Some p \<Rightarrow> Some p
    | None \<Rightarrow> (case ordinary_queue s of [] \<Rightarrow> None | p # _ \<Rightarrow> Some p))"

definition scoped_service ::
  "verified_inputs \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> (service_turn \<times> packet) set \<Rightarrow> scheduler_state \<Rightarrow>
    service_turn \<Rightarrow> packet \<Rightarrow> scheduler_result \<times> scheduler_state"
where
  "scoped_service inputs signer verified s turn p =
    (let view = authorized_view inputs s in
      if (turn, p) \<in> verified \<and> qualified_turn signer {turn} s turn \<and> planned view = Some p
      then (case schedule view of (r, t) \<Rightarrow>
        (r, t\<lparr>regulatory_queue := (case r of Internal (Served_Regulation _ _) \<Rightarrow>
                remove1 p (regulatory_queue s) | _ \<Rightarrow> regulatory_queue s)\<rparr>))
      else (Operational_Failure No_Effective_Opportunity, s))"

lemma a_previously_signed_order_cannot_execute_another_request:
  assumes "planned (authorized_view inputs s) \<noteq> Some p"
  shows "scoped_service inputs signer verified s turn p = (Operational_Failure No_Effective_Opportunity, s)"
  using assms by (simp add: scoped_service_def Let_def)

definition proposed_governance :: packet where
  "proposed_governance = urgent_packet\<lparr>packet_identity := 11,
    packet_contents := Execute_Governed_Rollback governed_intent None None\<rparr>"

definition rollback_intake :: scheduler_state where
  "rollback_intake = scheduler_example\<lparr>signed_packets := insert proposed_governance (signed_packets scheduler_example)\<rparr>"

definition pending_governance :: scheduler_state where
  "pending_governance = snd (admit rollback_intake proposed_governance)"

definition local_governance_turn :: service_turn where
  "local_governance_turn = \<lparr>turn_actor = 2, turn_authority = 4, turn_id = 11\<rparr>"

lemmas governance_execution = proposed_governance_def rollback_intake_def pending_governance_def
  local_governance_turn_def governed_intent_def unapproved_def scoped_submit_def scoped_service_def
  authorized_view_def planned_def qualified_turn_def checked_rollback_def scheduler_reduction
  scheduler_example_def regulatory_effect_def packet_example fixture_setup decision_rules
  ready_regulation_def packet_fresh_def Let_def

lemma unchecked_rollback_acceptance_cannot_bypass_the_collective_decision:
  "fst (admit rollback_intake proposed_governance) = Accepted 11"
  "scoped_submit unapproved rollback_intake proposed_governance = (Rejected Regulation_Ineligible, rollback_intake)"
  "scoped_service unapproved (\<lambda>_. Some 2) {(local_governance_turn, proposed_governance)} pending_governance
      local_governance_turn proposed_governance = (Operational_Failure No_Effective_Opportunity, pending_governance)"
  "\<exists>t. scoped_service (unapproved\<lparr>collective_decisions := {governed_intent}\<rparr>)
      (\<lambda>_. Some 2) {(local_governance_turn, proposed_governance)} pending_governance local_governance_turn proposed_governance
      = (Internal (Served_Regulation 11 9), t) \<and> cell_value (rollback_context t) chosen = 2
      \<and> regulation_receipts t 11 = Some proposed_governance"
  by (simp_all add: governance_execution)

definition approved_governance :: verified_inputs where
  "approved_governance = unapproved\<lparr>collective_decisions := {governed_intent}\<rparr>"

definition governed_with_fifo :: scheduler_state where
  "governed_with_fifo = snd (scoped_submit approved_governance pending_governance ordinary_packet)"

definition governed_effect :: scheduler_state where
  "governed_effect = snd (scoped_service approved_governance (\<lambda>_. Some 2)
     {(local_governance_turn, proposed_governance)} governed_with_fifo local_governance_turn proposed_governance)"

definition ordinary_turn :: service_turn where
  "ordinary_turn = local_governance_turn\<lparr>turn_id := 12\<rparr>"

lemma checked_rollback_and_ordinary_service_share_the_same_model_run:
  "scoped_submit approved_governance rollback_intake proposed_governance = (Accepted 11, pending_governance)"
  "scoped_submit approved_governance pending_governance ordinary_packet = (Accepted 101, governed_with_fifo)"
  "scoped_service approved_governance (\<lambda>_. Some 2) {(local_governance_turn, proposed_governance)}
      governed_with_fifo local_governance_turn proposed_governance
    = (Internal (Served_Regulation 11 9), governed_effect)"
  "cell_value (rollback_context governed_effect) chosen = 2"
  "ordinary_queue governed_effect = [ordinary_packet]"
  "\<exists>t. scoped_service approved_governance (\<lambda>_. Some 2) {(ordinary_turn, ordinary_packet)}
     governed_effect ordinary_turn ordinary_packet = (Internal (Served_Ordinary 101), t)
     \<and> ordinary_receipts t 101 = Some ordinary_packet
     \<and> cell_value (rollback_context t) chosen = 2"
  by (simp_all add: approved_governance_def governed_with_fifo_def governed_effect_def ordinary_turn_def governance_execution)

lemma accepted_mixed_effect_does_not_authorize_the_next_ordinary_order:
  "scoped_service unapproved (\<lambda>_. Some 2) {(current_turn, regulation_b)} second_update current_turn regulation_b
     = (Internal (Served_Regulation fixture_actor_b fixture_case_b), b_served)"
  "scoped_service unapproved (\<lambda>_. Some 2) {(current_turn, regulation_b)} b_served current_turn regulation_b
     = (Operational_Failure No_Effective_Opportunity, b_served)"
  "scoped_service unapproved (\<lambda>_. Some 2) {(current_turn, regulation_b)} b_served current_turn ordinary_input
     = (Operational_Failure No_Effective_Opportunity, b_served)"
  by (simp_all add: scoped_service_def qualified_turn_def authorized_view_def planned_def
      current_turn_def mixed_steps)

datatype stored_observation =
    Returned_Ordinary packet
  | Returned_Regulation packet
  | Superseded_Request packet
  | Contended_Attempt

definition retire_stale :: "scheduler_state \<Rightarrow> scheduler_state" where
  "retire_stale s = s\<lparr>regulatory_queue :=
    filter (\<lambda>p. \<not> permanently_stale s p) (regulatory_queue s)\<rparr>"

lemma retirement_preserves_priority_and_the_replay_set:
  "priority_slots (retire_stale s) = priority_slots s"
  "dedup_ids (retire_stale s) = dedup_ids s"
  "ordinary_queue (retire_stale s) = ordinary_queue s"
  by (simp_all add: retire_stale_def retaining_identity_while_retiring_stale_entries_preserves_priority_slots)

fun sees_without_commit ::
  "scheduler_state \<Rightarrow> stored_observation \<Rightarrow> scheduler_state \<Rightarrow> bool"
where
  "sees_without_commit s (Returned_Ordinary p) t = read_ordinary_receipt s p t"
| "sees_without_commit s (Returned_Regulation p) t = (t = s \<and> regulation_receipts s (packet_identity p) = Some p)"
| "sees_without_commit s (Superseded_Request p) t =
    (t = s \<and> \<not> ordinary_body (packet_contents p) \<and> permanently_stale s p \<and> packet_identity p \<in> dedup_ids s
      \<and> p \<notin> set (regulatory_queue s) \<and> regulation_receipts s (packet_identity p) = None)"
| "sees_without_commit s Contended_Attempt t = (t = s)"

lemma a_retry_read_or_cas_refusal_never_claims_an_extra_effect:
  "sees_without_commit s observed t \<Longrightarrow> t = s"
  by (cases observed) (simp_all add: read_ordinary_receipt_def)

lemma mixed_trace_classifies_control_conflict_supersession_and_retained_receipts:
  "sees_without_commit second_update Contended_Attempt second_update"
  "sees_without_commit (retire_stale second_update) (Superseded_Request regulation_a) (retire_stale second_update)"
  "sees_without_commit b_served (Returned_Regulation regulation_b) b_served"
  "sees_without_commit ordinary_served (Returned_Ordinary ordinary_input) ordinary_served"
  by (simp_all add: mixed_steps permanently_stale_def read_ordinary_receipt_def retire_stale_def)

lemma recovered_and_replayed_regulation_is_one_saved_result:
  "fixture_exact_regulation_receipt = fixture_recovery_receipt \<and>
   fixture_exact_regulation_receipt = fixture_replay_receipt \<and>
   fixture_exact_regulation_receipt = fixture_reopened_regulation_receipt \<and>
   sees_without_commit b_served (Returned_Regulation regulation_b) b_served"
  using mixed_trace_classifies_control_conflict_supersession_and_retained_receipts(3)
  by (simp add: fixture_exact_regulation_receipt_def fixture_recovery_receipt_def
    fixture_replay_receipt_def fixture_reopened_regulation_receipt_def)

end
