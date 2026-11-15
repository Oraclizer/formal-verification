theory Deployment_Recovery
  imports REOS_Rollback.Rollback_Contracts
begin

text \<open>A deployment consumer resolves an artifact only when the environment
  alias agrees with the installed manifest. A retired environment never
  resolves its artifact. The observer combines two cells and a retirement fact.\<close>

datatype resolution = Runnable nat | Inconsistent | Retired

abbreviation alias_cell :: "nat \<Rightarrow> ledger_cell" where "alias_cell environment \<equiv> Cell 71 environment 5 Ownership"
abbreviation manifest_cell :: "nat \<Rightarrow> ledger_cell" where "manifest_cell environment \<equiv> Cell 71 environment 5 Transition_Record"

definition resolve :: "rollback_state \<Rightarrow> nat \<Rightarrow> resolution"
where
  "resolve s environment =
    (if terminal_records s environment \<noteq> None then Retired
     else if cell_value s (alias_cell environment) = cell_value s (manifest_cell environment)
          then Runnable (cell_value s (alias_cell environment)) else Inconsistent)"

definition deployment_switch :: rollback_intent where
  "deployment_switch = \<lparr>request_id = 12, requester = 1, requested_role = Governance,
    request_case = 1, request_authority_epoch = 2, request_policy_epoch = 3, request_window = (0,8),
    request_scope = Targeted 71 1 5, request_cells = [alias_cell 1, manifest_cell 1], undo_entry = 4\<rparr>"

definition deployment_origin :: rollback_state where
  "deployment_origin = \<lparr>consensus_time = 4, authority_epoch = 2, policy_epoch = (\<lambda>_. 3),
    authenticated_intents = {deployment_switch, deployment_switch\<lparr>request_cells := [alias_cell 1]\<rparr>},
    grant_at = (\<lambda>ep a. if ep = 2 \<and> a = 1 then Some \<lparr>grant_role = Governance, grant_cases = {1},
      grant_cells = {alias_cell 1, manifest_cell 1}\<rparr> else None),
    rules_at = (\<lambda>k ep. if k = 1 \<and> ep = 3 then Some \<lparr>case_window = (0,8),
      policy_cells = (\<lambda>_. {alias_cell 1, manifest_cell 1}), wide_roles = {}\<rparr> else None),
    verified_certificates = (\<lambda>_. None), case_remaining = (\<lambda>_. 1),
    cell_value = (\<lambda>_. 24), replica_value = (\<lambda>_ _. 24),
    journal = (\<lambda>i. if i = 4 then Some \<lparr>entry_case = 1, entry_cells = {alias_cell 1, manifest_cell 1},
      previous_value = (\<lambda>_. 11), applied_value = (\<lambda>_. 24),
      entry_stage = Ordinary_Reversible\<rparr>
      else if i = 9 then Some \<lparr>entry_case = 1, entry_cells = {alias_cell 9, manifest_cell 9},
        previous_value = (\<lambda>_. 24), applied_value = (\<lambda>_. 0),
        entry_stage = External_Pending\<rparr> else None),
    abort_receipts = {},
    finality_receipts = (\<lambda>i. if i = 9 then Some \<lparr>terminal_cells = {alias_cell 9, manifest_cell 9},
      terminal_value = (\<lambda>_. 0)\<rparr> else None),
    terminal_records = (\<lambda>_. None)\<rparr>"

definition before_deployment_rollback :: rollback_state
where "before_deployment_rollback = snd (execute deployment_origin (Record_Finality 9))"

definition after_deployment_rollback :: rollback_state
where "after_deployment_rollback =
  snd (execute before_deployment_rollback (Execute_Rollback deployment_switch None None))"

lemma artifact_resolution_after_targeted_restore:
  "rollback_step deployment_origin (Record_Finality 9)
    (Internal (Recorded_Finality 9)) before_deployment_rollback"
  "rollback_step before_deployment_rollback (Execute_Rollback deployment_switch None None)
    (Accepted 12) after_deployment_rollback"
  "resolve before_deployment_rollback 1 = Runnable 24"
  "resolve after_deployment_rollback 1 = Runnable 11"
  "resolve after_deployment_rollback 2 = resolve before_deployment_rollback 2"
  "resolve after_deployment_rollback 9 = Retired"
  by (simp_all add: before_deployment_rollback_def after_deployment_rollback_def deployment_origin_def
      deployment_switch_def rollback_step_def finality_applicable_def preserve_protected_def protected_def
      execute_rollback_def authorization_failure_def restoration_failure_def footprint_def restore_def
      update_cells_def other_unsettled_cells_def resolve_def)

lemma consumers_need_the_manifest_agreement:
  "\<exists>t. rollback_step before_deployment_rollback
    (Execute_Rollback (deployment_switch\<lparr>request_cells := [alias_cell 1]\<rparr>) None None)
    (Accepted 12) t \<and> resolve t 1 = Inconsistent"
  by (simp add: before_deployment_rollback_def deployment_origin_def deployment_switch_def
      rollback_step_def finality_applicable_def preserve_protected_def protected_def
      execute_rollback_def authorization_failure_def restoration_failure_def footprint_def restore_def
      update_cells_def other_unsettled_cells_def resolve_def)

end
