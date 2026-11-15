theory Rollback_Examples
  imports REOS_Rollback.Rollback_Contracts
begin

abbreviation chosen :: ledger_cell where "chosen \<equiv> Cell 1 2 3 Balance"
abbreviation sibling :: ledger_cell where "sibling \<equiv> Cell 1 7 3 Balance"
abbreviation billing :: ledger_cell where "billing \<equiv> Cell 1 2 3 Billing"
abbreviation terminal :: ledger_cell where "terminal \<equiv> Cell 1 2 4 Ownership"
abbreviation session_cell :: ledger_cell where "session_cell \<equiv> Cell 1 2 5 Session"

definition intent :: rollback_intent where
  "intent = \<lparr>request_id = 11, requester = 2, requested_role = Regulator, request_case = 9,
      request_authority_epoch = 4, request_policy_epoch = 8, request_window = (3,7),
      request_scope = Targeted 1 2 3, request_cells = [chosen], undo_entry = 10\<rparr>"

definition wide_intent :: rollback_intent where
  "wide_intent = intent\<lparr>request_scope := Wide, request_cells := [chosen, sibling]\<rparr>"

definition validator_intent :: rollback_intent where
  "validator_intent = intent\<lparr>requester := 3, requested_role := Validator\<rparr>"

definition emergency_intent :: rollback_intent where
  "emergency_intent = intent\<lparr>requester := 4, requested_role := Emergency\<rparr>"

definition terminal_intent :: rollback_intent where
  "terminal_intent = intent\<lparr>request_scope := Targeted 1 2 4, request_cells := [terminal], undo_entry := 77\<rparr>"

definition older_terminal_intent :: rollback_intent where
  "older_terminal_intent = terminal_intent\<lparr>undo_entry := 10\<rparr>"

definition reverse_intent :: rollback_intent where
  "reverse_intent = intent\<lparr>request_id := 12, undo_entry := 11\<rparr>"

definition ordinary_entry :: history_entry where
  "ordinary_entry = \<lparr>entry_case = 9, entry_cells = {chosen, sibling, billing, session_cell, terminal},
      previous_value = (\<lambda>_. 2), applied_value = (\<lambda>_. 9),
      entry_stage = Ordinary_Reversible\<rparr>"

definition in_flight_entry :: history_entry where
  "in_flight_entry = ordinary_entry\<lparr>entry_cells := {terminal}, entry_stage := External_Pending\<rparr>"

definition receipt :: terminal_record where
  "receipt = \<lparr>terminal_cells = {terminal}, terminal_value = (\<lambda>_. 13)\<rparr>"

definition grant :: "nat \<Rightarrow> nat \<Rightarrow> registered_grant option" where
  "grant epoch actor =
    (if epoch \<noteq> 4 \<or> actor \<notin> {1,2,3,4} then None else
      Some \<lparr>grant_role = (if actor = 1 then Governance else if actor = 2 then Regulator
                           else if actor = 3 then Validator else Emergency),
        grant_cases = {9}, grant_cells = (if actor \<in> {3,4} then {chosen} else UNIV)\<rparr>)"

definition fixture :: rollback_state where
  "fixture = \<lparr>consensus_time = 4, authority_epoch = 4, policy_epoch = (\<lambda>_. 8),
    authenticated_intents =
      {intent, wide_intent, validator_intent, emergency_intent, terminal_intent, older_terminal_intent, reverse_intent,
        wide_intent\<lparr>request_id := 12\<rparr>, intent\<lparr>requester := 1, requested_role := Governance\<rparr>,
        intent\<lparr>requested_role := Governance\<rparr>, intent\<lparr>request_case := 8\<rparr>,
        intent\<lparr>request_window := (3,8)\<rparr>, intent\<lparr>request_cells := [chosen,sibling]\<rparr>,
        intent\<lparr>request_scope := Targeted 1 2 5, request_cells := [session_cell],
          requester := 3, requested_role := Validator\<rparr>,
        intent\<lparr>request_id := 13, undo_entry := 12\<rparr>},
    grant_at = grant,
    rules_at = (\<lambda>k e. if k = 9 \<and> e = 8
      then Some \<lparr>case_window = (3,7), policy_cells = (\<lambda>_. UNIV), wide_roles = {Governance,Regulator}\<rparr> else None),
    verified_certificates = (\<lambda>i.
      if i = 20 then Some \<lparr>certificate_kind = Governance_Ratification, certificate_holder = 1,
        certified_intent = wide_intent\<rparr>
      else if i = 30 then Some \<lparr>certificate_kind = Validation_Failure, certificate_holder = 3,
        certified_intent = validator_intent\<rparr>
      else if i = 40 then Some \<lparr>certificate_kind = Emergency_Activation, certificate_holder = 4,
        certified_intent = emergency_intent\<rparr> else None),
    case_remaining = (\<lambda>k. if k = 9 then 2 else 4), cell_value = (\<lambda>_. 9),
    replica_value = (\<lambda>_ _. 8),
    journal = (\<lambda>i. if i = 10 then Some ordinary_entry else if i = 77 then Some in_flight_entry else None),
    abort_receipts = {},
    finality_receipts = (\<lambda>i. if i = 77 then Some receipt else None), terminal_records = (\<lambda>_. None)\<rparr>"

lemmas fixture_setup = fixture_def grant_def intent_def wide_intent_def validator_intent_def
  emergency_intent_def terminal_intent_def older_terminal_intent_def reverse_intent_def
  ordinary_entry_def in_flight_entry_def receipt_def

lemmas decision_rules = rollback_step_def execute_rollback_def authorization_failure_def
  restoration_failure_def footprint_def matches_certificate_def protected_def
  restore_def finality_applicable_def preserve_protected_def other_unsettled_cells_def update_cells_def

definition single_restore :: rollback_state where
  "single_restore = snd (execute fixture (Execute_Rollback intent None None))"

lemma selected_value_changes_and_peers_survive:
  "rollback_step fixture (Execute_Rollback intent None None) (Accepted 11) single_restore"
  "cell_value fixture chosen = 9"
  "cell_value single_restore chosen = 2"
  "cell_value single_restore sibling = 9"
  "cell_value single_restore billing = 9"
  "cell_value single_restore session_cell = 9"
  by (simp_all add: fixture_setup decision_rules single_restore_def)

lemma wide_with_and_without_ratification:
  "rollback_step fixture (Execute_Rollback wide_intent None None) (Rejected Approval_Required) fixture"
  "\<exists>t. rollback_step fixture (Execute_Rollback wide_intent (Some 20) None) (Accepted 11) t"
  "rollback_step fixture (Execute_Rollback (wide_intent\<lparr>request_id := 12\<rparr>) (Some 20) None)
    (Rejected Approval_Required) fixture"
  by (simp_all add: fixture_setup decision_rules)

lemma head_role_controls:
  "\<exists>t. rollback_step fixture
    (Execute_Rollback (intent\<lparr>requester := 1, requested_role := Governance\<rparr>) None None) (Accepted 11) t"
  "rollback_step fixture (Execute_Rollback (intent\<lparr>requested_role := Governance\<rparr>) None None)
    (Rejected Unknown_Authority) fixture"
  "\<exists>t. rollback_step fixture (Execute_Rollback validator_intent None (Some 30)) (Accepted 11) t"
  "rollback_step fixture (Execute_Rollback validator_intent None None) (Rejected Role_Proof_Required) fixture"
  "\<exists>t. rollback_step fixture (Execute_Rollback emergency_intent None (Some 40)) (Accepted 11) t"
  "rollback_step fixture (Execute_Rollback emergency_intent None (Some 30)) (Rejected Role_Proof_Required) fixture"
  by (simp_all add: fixture_setup decision_rules)

lemma scope_and_context_denials:
  "rollback_step fixture (Execute_Rollback (intent\<lparr>request_id := 99\<rparr>) None None)
     (Rejected Unauthenticated_Intent) fixture"
  "rollback_step fixture (Execute_Rollback (intent\<lparr>request_authority_epoch := 3\<rparr>) None None)
     (Rejected Stale_Authority) fixture"
  "rollback_step fixture (Execute_Rollback (intent\<lparr>request_policy_epoch := 7\<rparr>) None None)
     (Rejected Stale_Policy) fixture"
  "rollback_step fixture (Execute_Rollback (intent\<lparr>request_case := 8\<rparr>) None None)
     (Rejected Wrong_Case) fixture"
  "rollback_step fixture (Execute_Rollback (intent\<lparr>request_window := (3,8)\<rparr>) None None)
     (Rejected Invalid_Window) fixture"
  "rollback_step (fixture\<lparr>consensus_time := 7\<rparr>) (Execute_Rollback intent None None)
     (Rejected Invalid_Window) (fixture\<lparr>consensus_time := 7\<rparr>)"
  "rollback_step fixture (Execute_Rollback (intent\<lparr>request_cells := [chosen,sibling]\<rparr>) None None)
     (Rejected Invalid_Scope) fixture"
  "rollback_step fixture (Execute_Rollback (intent\<lparr>request_scope := Targeted 1 2 5, request_cells := [session_cell],
       requester := 3, requested_role := Validator\<rparr>) None (Some 30))
     (Rejected Invalid_Scope) fixture"
  by (simp_all add: fixture_setup decision_rules)

definition abort_origin :: rollback_state where
  "abort_origin = fixture\<lparr>abort_receipts := {77}, finality_receipts := (\<lambda>_. None)\<rparr>"

definition can_compensate :: rollback_state where
  "can_compensate = snd (execute abort_origin (Record_Abort 77))"

definition offered_late_receipt :: rollback_state where
  "offered_late_receipt = can_compensate\<lparr>finality_receipts := (finality_receipts can_compensate)(77 \<mapsto> receipt)\<rparr>"

definition with_finality :: rollback_state where
  "with_finality = snd (execute fixture (Record_Finality 77))"

definition replica_repaired :: rollback_state where
  "replica_repaired = snd (execute with_finality (Repair_From_Record 77 1))"

lemma primary_finality_and_rollback_controls:
  "rollback_step fixture (Execute_Rollback terminal_intent None None) (Rejected Pending_Effect) fixture"
  "rollback_step fixture (Execute_Rollback older_terminal_intent None None) (Rejected Pending_Effect) fixture"
  "\<exists>t. rollback_step can_compensate (Execute_Rollback terminal_intent None None) (Accepted 11) t
    \<and> cell_value t terminal = 2"
  "rollback_step fixture (Record_Abort 77) (Rejected No_Abort_Evidence) fixture"
  "rollback_step offered_late_receipt (Record_Finality 77) (Rejected Invalid_Context) offered_late_receipt"
  "rollback_step fixture (Record_Finality 77) (Internal (Recorded_Finality 77)) with_finality"
  "rollback_step with_finality (Execute_Rollback terminal_intent None None)
    (Rejected Terminal_Effect) with_finality"
  "rollback_step with_finality (Repair_From_Record 77 1) (Internal (Repaired_From_Record 77 1)) replica_repaired"
  "replica_value with_finality 1 terminal = 8"
  "replica_value replica_repaired 1 terminal = 13"
  "replica_value replica_repaired 2 terminal = 8"
  "cell_value replica_repaired terminal = 13"
  "\<exists>t. rollback_step with_finality (Execute_Rollback intent None None) (Accepted 11) t
    \<and> cell_value t chosen = 2 \<and> cell_value t terminal = 13"
  by (simp_all add: fixture_setup decision_rules abort_origin_def can_compensate_def
      offered_late_receipt_def with_finality_def replica_repaired_def)

definition effect_compensated :: rollback_state where
  "effect_compensated = snd (execute can_compensate (Execute_Rollback terminal_intent None None))"

lemma pending_receipt_then_real_compensation:
  "finite_trace rollback_step UNIV abort_origin
    [\<lparr>source_state = abort_origin, step_action = Record_Abort 77,
      step_outcome = Internal (Recorded_Abort 77), target_state = can_compensate\<rparr>,
     \<lparr>source_state = can_compensate, step_action = Execute_Rollback terminal_intent None None,
      step_outcome = Accepted 11, target_state = effect_compensated\<rparr>]
    effect_compensated"
  "cell_value abort_origin terminal = 9"
  "cell_value effect_compensated terminal = 2"
  by (simp_all add: fixture_setup decision_rules abort_origin_def can_compensate_def
      effect_compensated_def step_occurs_def)

definition inconsistent_prior_record :: rollback_state where
  "inconsistent_prior_record = with_finality\<lparr>cell_value := (\<lambda>_. 9),
     journal := (journal with_finality)(78 \<mapsto> in_flight_entry),
     finality_receipts := (finality_receipts with_finality)(78 \<mapsto> receipt\<lparr>terminal_value := (\<lambda>_. 9)\<rparr>)\<rparr>"

lemma incoming_receipt_matching_live_value_still_needs_old_receipt_agreement:
  "terminal_value receipt terminal = 13"
  "cell_value inconsistent_prior_record terminal = 9"
  "rollback_step inconsistent_prior_record (Record_Finality 78) (Rejected Terminal_Effect) inconsistent_prior_record"
  by (simp_all add: fixture_setup decision_rules inconsistent_prior_record_def with_finality_def)

definition after_reverse :: rollback_state where
  "after_reverse = snd (execute single_restore (Execute_Rollback reverse_intent None None))"

lemma rollback_of_rollback_really_fires_then_exhausts:
  "rollback_step single_restore (Execute_Rollback reverse_intent None None) (Accepted 12) after_reverse"
  "cell_value after_reverse chosen = 9"
  "case_remaining after_reverse 9 = 0"
  "case_remaining after_reverse 8 = 4"
  "rollback_step after_reverse (Execute_Rollback (intent\<lparr>request_id := 13, undo_entry := 12\<rparr>) None None)
    (Rejected Budget_Exhausted) after_reverse"
  by (simp_all add: fixture_setup decision_rules single_restore_def after_reverse_def reverse_intent_def)

end
