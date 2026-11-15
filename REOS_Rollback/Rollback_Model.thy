theory Rollback_Model
  imports Operational_Trace_Contracts.Operational_Trace_Contracts
begin

section \<open>Rollback requests and authenticated facts\<close>

datatype resource = Balance | Ownership | Lock | Session | Billing | Transition_Record
datatype ledger_cell = Cell nat nat nat resource

datatype rollback_role = Governance | Regulator | Validator | Emergency
datatype rollback_scope = Targeted nat nat nat | Wide
datatype certificate_kind = Governance_Ratification | Validation_Failure | Emergency_Activation
datatype effect_stage = Ordinary_Reversible | Aborted_Compensable | External_Pending | Irreversible

record rollback_intent =
  request_id :: nat
  requester :: nat
  requested_role :: rollback_role
  request_case :: nat
  request_authority_epoch :: nat
  request_policy_epoch :: nat
  request_window :: "nat \<times> nat"
  request_scope :: rollback_scope
  request_cells :: "ledger_cell list"
  undo_entry :: nat

record registered_grant =
  grant_role :: rollback_role
  grant_cases :: "nat set"
  grant_cells :: "ledger_cell set"

record case_rules =
  case_window :: "nat \<times> nat"
  policy_cells :: "rollback_role \<Rightarrow> ledger_cell set"
  wide_roles :: "rollback_role set"

record rollback_certificate =
  certificate_kind :: certificate_kind
  certificate_holder :: nat
  certified_intent :: rollback_intent

record history_entry =
  entry_case :: nat
  entry_cells :: "ledger_cell set"
  previous_value :: "ledger_cell \<Rightarrow> nat"
  applied_value :: "ledger_cell \<Rightarrow> nat"
  entry_stage :: effect_stage

record terminal_record =
  terminal_cells :: "ledger_cell set"
  terminal_value :: "ledger_cell \<Rightarrow> nat"

text \<open>The input tables model already authenticated snapshots, intents and receipts.
  The wire protocol must justify their provenance and the authoritative
  abort/finality fence. A missing local finality record is not an abort receipt.\<close>

record rollback_state =
  consensus_time :: nat
  authority_epoch :: nat
  policy_epoch :: "nat \<Rightarrow> nat"
  authenticated_intents :: "rollback_intent set"
  grant_at :: "nat \<Rightarrow> nat \<Rightarrow> registered_grant option"
  rules_at :: "nat \<Rightarrow> nat \<Rightarrow> case_rules option"
  verified_certificates :: "nat \<Rightarrow> rollback_certificate option"
  case_remaining :: "nat \<Rightarrow> nat"
  cell_value :: "ledger_cell \<Rightarrow> nat"
  replica_value :: "nat \<Rightarrow> ledger_cell \<Rightarrow> nat"
  journal :: "nat \<Rightarrow> history_entry option"
  abort_receipts :: "nat set"
  finality_receipts :: "nat \<Rightarrow> terminal_record option"
  terminal_records :: "nat \<Rightarrow> terminal_record option"

datatype rollback_action =
    Execute_Rollback rollback_intent "nat option" "nat option"
  | Record_Abort nat
  | Record_Finality nat
  | Repair_From_Record nat nat
  | Advance_Context nat nat nat nat

datatype rollback_denial =
    Unauthenticated_Intent | Unknown_Authority | Stale_Authority | Stale_Policy | Wrong_Case
  | Invalid_Window | Invalid_Scope | Approval_Required | Role_Proof_Required
  | Unknown_Entry | Invalid_Preimage | Terminal_Effect | Pending_Effect
  | Budget_Exhausted | Repeated_Request | Invalid_Context | No_Abort_Evidence | No_Primary_Record

datatype rollback_internal =
    Recorded_Abort nat | Recorded_Finality nat | Repaired_From_Record nat nat | Context_Advanced

type_synonym rollback_result =
  "(nat, rollback_denial, unit, rollback_internal) transition_result"

fun inside_scope :: "rollback_scope \<Rightarrow> ledger_cell \<Rightarrow> bool" where
  "inside_scope (Targeted asset address tx) (Cell a d t res) =
    (asset = a \<and> address = d \<and> tx = t)"
| "inside_scope Wide c = True"

definition footprint :: "rollback_intent \<Rightarrow> ledger_cell set" where
  "footprint r = set (request_cells r)"

definition matches_certificate ::
  "rollback_state \<Rightarrow> rollback_intent \<Rightarrow> certificate_kind \<Rightarrow> rollback_role
    \<Rightarrow> nat option \<Rightarrow> bool"
where
  "matches_certificate s r kind role ref =
    (\<exists>i c g. ref = Some i \<and> verified_certificates s i = Some c
      \<and> certificate_kind c = kind \<and> certified_intent c = r
      \<and> grant_at s (authority_epoch s) (certificate_holder c) = Some g
      \<and> grant_role g = role \<and> request_case r \<in> grant_cases g
      \<and> footprint r \<subseteq> grant_cells g)"

fun role_proof_ok :: "rollback_state \<Rightarrow> rollback_intent \<Rightarrow> rollback_role \<Rightarrow> nat option \<Rightarrow> bool"
where
  "role_proof_ok s r Validator ref = matches_certificate s r Validation_Failure Validator ref"
| "role_proof_ok s r Emergency ref = matches_certificate s r Emergency_Activation Emergency ref"
| "role_proof_ok s r Governance ref = True"
| "role_proof_ok s r Regulator ref = True"

definition protected :: "rollback_state \<Rightarrow> ledger_cell set" where
  "protected s = {c. \<exists>i p. terminal_records s i = Some p \<and> c \<in> terminal_cells p}"

definition other_unsettled_cells :: "rollback_state \<Rightarrow> nat \<Rightarrow> ledger_cell set"
where
  "other_unsettled_cells s selected =
    {c. \<exists>i h. i \<noteq> selected \<and> journal s i = Some h \<and>
      (entry_stage h = External_Pending \<or> entry_stage h = Irreversible) \<and> c \<in> entry_cells h}"

definition preserve_protected ::
  "rollback_state \<Rightarrow> ledger_cell set \<Rightarrow> (ledger_cell \<Rightarrow> nat) \<Rightarrow> bool"
where
  "preserve_protected s cells contents =
    ((\<forall>c \<in> cells \<inter> protected s. contents c = cell_value s c)
     \<and> (\<forall>i p. terminal_records s i = Some p \<longrightarrow>
          (\<forall>c \<in> cells \<inter> terminal_cells p. contents c = terminal_value p c)))"

definition authorization_failure ::
  "rollback_state \<Rightarrow> rollback_intent \<Rightarrow> nat option \<Rightarrow> nat option \<Rightarrow> rollback_denial option"
where
  "authorization_failure s r approval role_proof =
    (if request_authority_epoch r \<noteq> authority_epoch s then Some Stale_Authority
     else if request_policy_epoch r \<noteq> policy_epoch s (request_case r) then Some Stale_Policy
     else if r \<notin> authenticated_intents s then Some Unauthenticated_Intent
     else case (grant_at s (authority_epoch s) (requester r),
                rules_at s (request_case r) (request_policy_epoch r)) of
         (None, _) \<Rightarrow> Some Unknown_Authority
       | (_, None) \<Rightarrow> Some Wrong_Case
       | (Some g, Some p) \<Rightarrow>
          if grant_role g \<noteq> requested_role r then Some Unknown_Authority
          else if request_case r \<notin> grant_cases g then Some Wrong_Case
          else if request_window r \<noteq> case_window p
               \<or> consensus_time s < fst (case_window p)
               \<or> snd (case_window p) \<le> consensus_time s then Some Invalid_Window
          else if footprint r = {}
               \<or> \<not> (\<forall>c\<in>footprint r. inside_scope (request_scope r) c)
               \<or> \<not> footprint r \<subseteq> grant_cells g \<inter> policy_cells p (requested_role r)
               \<or> (request_scope r = Wide \<and> requested_role r \<notin> wide_roles p)
               then Some Invalid_Scope
          else if request_scope r = Wide
               \<and> \<not> matches_certificate s r Governance_Ratification Governance approval
               then Some Approval_Required
          else if \<not> role_proof_ok s r (requested_role r) role_proof then Some Role_Proof_Required
          else None)"

definition restoration_failure ::
  "rollback_state \<Rightarrow> rollback_intent \<Rightarrow> history_entry \<Rightarrow> rollback_denial option"
where
  "restoration_failure s r h =
    (if request_case r \<noteq> entry_case h then Some Wrong_Case
     else if \<not> footprint r \<subseteq> entry_cells h then Some Invalid_Scope
     else if entry_stage h = Irreversible \<or> footprint r \<inter> protected s \<noteq> {} then Some Terminal_Effect
     else if entry_stage h = External_Pending
         \<or> footprint r \<inter> other_unsettled_cells s (undo_entry r) \<noteq> {} then Some Pending_Effect
     else if \<not> (\<forall>c \<in> footprint r. cell_value s c = applied_value h c) then Some Invalid_Preimage
     else if case_remaining s (request_case r) = 0 then Some Budget_Exhausted
     else if journal s (request_id r) \<noteq> None then Some Repeated_Request
     else None)"

definition restore :: "rollback_state \<Rightarrow> rollback_intent \<Rightarrow> history_entry \<Rightarrow> rollback_state"
where
  "restore s r h = s\<lparr>
      cell_value := update_cells (footprint r) (previous_value h) (cell_value s),
      case_remaining := (case_remaining s)(request_case r := case_remaining s (request_case r) - 1),
      journal := (journal s)(request_id r \<mapsto>
        \<lparr>entry_case = request_case r, entry_cells = footprint r,
          previous_value = cell_value s, applied_value = previous_value h,
          entry_stage = Ordinary_Reversible\<rparr>)
    \<rparr>"

definition execute_rollback ::
  "rollback_state \<Rightarrow> rollback_intent \<Rightarrow> nat option \<Rightarrow> nat option
    \<Rightarrow> rollback_result \<times> rollback_state"
where
  "execute_rollback s r approval role_proof =
    (case authorization_failure s r approval role_proof of
         Some why \<Rightarrow> (Rejected why, s)
       | None \<Rightarrow> (case journal s (undo_entry r) of
           None \<Rightarrow> (Rejected Unknown_Entry, s)
         | Some h \<Rightarrow> (case restoration_failure s r h of
               Some why \<Rightarrow> (Rejected why, s)
             | None \<Rightarrow> (Accepted (request_id r), restore s r h))))"

definition finality_applicable ::
  "rollback_state \<Rightarrow> nat \<Rightarrow> terminal_record \<Rightarrow> bool"
where
  "finality_applicable s i p =
    (\<exists>h. journal s i = Some h \<and>
      (entry_stage h = External_Pending \<or> entry_stage h = Irreversible) \<and>
      terminal_cells p \<noteq> {} \<and> terminal_cells p \<subseteq> entry_cells h)"

fun execute :: "rollback_state \<Rightarrow> rollback_action \<Rightarrow> rollback_result \<times> rollback_state"
where
  "execute s (Execute_Rollback r approval role_proof) = execute_rollback s r approval role_proof"
| "execute s (Record_Abort i) =
    (if i \<notin> abort_receipts s then (Rejected No_Abort_Evidence, s)
     else case journal s i of None \<Rightarrow> (Rejected Unknown_Entry, s)
     | Some h \<Rightarrow>
       if entry_stage h \<noteq> External_Pending \<or> terminal_records s i \<noteq> None
         \<or> finality_receipts s i \<noteq> None
       then (Rejected Invalid_Context, s)
       else (Internal (Recorded_Abort i), s\<lparr>
         journal := (journal s)(i \<mapsto> h\<lparr>entry_stage := Aborted_Compensable\<rparr>)\<rparr>))"
| "execute s (Record_Finality i) =
    (case finality_receipts s i of None \<Rightarrow> (Rejected No_Primary_Record, s)
     | Some p \<Rightarrow>
       if \<not> finality_applicable s i p then (Rejected Invalid_Context, s)
       else if terminal_records s i \<noteq> None
           \<or> \<not> preserve_protected s (terminal_cells p) (terminal_value p)
       then (Rejected Terminal_Effect, s)
       else (Internal (Recorded_Finality i), s\<lparr>
         terminal_records := (terminal_records s)(i \<mapsto> p),
         cell_value := update_cells (terminal_cells p) (terminal_value p) (cell_value s)\<rparr>))"
| "execute s (Repair_From_Record i replica) =
    (case terminal_records s i of None \<Rightarrow> (Rejected No_Primary_Record, s)
     | Some p \<Rightarrow>
       (Internal (Repaired_From_Record i replica), s\<lparr>
         replica_value := (replica_value s)(replica :=
           update_cells (terminal_cells p) (terminal_value p) (replica_value s replica))\<rparr>))"
| "execute s (Advance_Context time authority case_id policy) =
    (if time < consensus_time s \<or> authority < authority_epoch s
        \<or> policy < policy_epoch s case_id
     then (Rejected Invalid_Context, s)
     else (Internal Context_Advanced, s\<lparr>
         consensus_time := time, authority_epoch := authority,
         policy_epoch := (policy_epoch s)(case_id := policy)\<rparr>))"

definition rollback_step :: "(rollback_state, rollback_action, rollback_result) step_rel"
where
  "rollback_step s action outcome t \<longleftrightarrow> execute s action = (outcome, t)"

end
