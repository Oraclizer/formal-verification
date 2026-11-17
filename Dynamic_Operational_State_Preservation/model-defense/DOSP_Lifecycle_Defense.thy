theory DOSP_Lifecycle_Defense
  imports DOSP_Commit_Defense
begin

record cycle_request =
  cycle_attempt_id :: client_call_id
  cycle_session_id :: oracle_session_identity
  cycle_binding_id :: nat
  cycle_ticket :: route_ticket
  cycle_source :: nat
  cycle_target :: nat
  cycle_value :: nat

datatype lifecycle_phase =
    Idle_Cycle | Bound_Cycle cycle_request | Verified_Cycle cycle_request
  | Partial_Cycle cycle_request "nat flow_state"

datatype lifecycle_custody = Local_Cells_Only | Native_Debit_Pending source_key

record lifecycle_state =
  lifecycle_cutover :: "nat cutover_state"
  lifecycle_phase :: lifecycle_phase
  lifecycle_clock :: nat
  lifecycle_session :: oracle_session_identity
  lifecycle_tariff :: nat
  lifecycle_registry :: registry_snapshot
  cycle_custody :: lifecycle_custody
  lifecycle_diagnostic_authorities :: "nat set"
  lifecycle_invoice :: "accounted_cycle list"

record restoration_evidence =
  restoration_attempt :: client_call_id
  restoration_ticket :: route_ticket
  restoration_values :: "nat flow_state"

record commit_observation =
  observing_authority :: nat
  observed_request :: cycle_request
  observed_clock :: nat
  observed_failure :: flow_failure
  observed_cause :: observed_fault

record commit_measurement =
  measuring_authority :: nat
  measured_request :: cycle_request
  measured_clock :: nat
  measured_reply :: cutover_result
  measured_write_domains :: "nat set"
  measured_final_leaves :: "nat set"

record commit_evidence =
  verified_observations :: "commit_observation list"
  verified_measurements :: "commit_measurement list"

text \<open>The verified evidence comes from the execution authorities. Client
  commands carry neither diagnostic records nor measurements. The following
  checks bind each admitted record to the state's authorized suppliers and to
  the exact attempt. Authentic storage and evidence verification supply the
  streams consumed by this model.\<close>

datatype lifecycle_command =
    Bind_Cycle cycle_request | Verify_Cycle "observed_fault list"
  | Commit_Cycle bool | Retry_Cycle client_call_id
  | Restore_Cycle restoration_evidence | Promote_Cycle nat nat

datatype lifecycle_reply =
    Cycle_Bound | Cycle_Verified | Precommit_Refused | Cycle_Result cutover_result
  | Measurement_Unavailable | Cycle_Restored | Restoration_Refused | Lifecycle_Promoted | Lifecycle_Promotion_Refused

definition request_flow :: "cycle_request \<Rightarrow> nat flow_action" where
  "request_flow request = Commit_From (cycle_source request) (cycle_target request) (cycle_value request)"

definition binding_is_current :: "nat flow_policy \<Rightarrow> lifecycle_state \<Rightarrow> cycle_request \<Rightarrow> bool" where
  "binding_is_current policy s request \<longleftrightarrow>
    cycle_session_id request = lifecycle_session s \<and>
    cycle_attempt_id request \<notin> image accounted_attempt (set (lifecycle_invoice s)) \<and>
    \<not> (\<exists>row \<in> set (lifecycle_invoice s). accounted_abort row = None \<and>
      accounted_session row = cycle_session_id request \<and> accounted_binding row = cycle_binding_id request) \<and>
    ticket_metadata (cycle_ticket request) = route_metadata (lifecycle_cutover s) \<and>
    lifecycle_tariff s = meter_version (ticket_metadata (cycle_ticket request)) \<and>
    can_commit policy (lifecycle_cutover s) (cycle_binding_id request)
      (ticket_metadata (cycle_ticket request)) (request_flow request) \<and>
    ticket_authorizes (lifecycle_registry s) policy (fst (cycle_session_id request)) (cycle_ticket request) (request_flow request)"

definition request_commit :: "cycle_request \<Rightarrow> bool \<Rightarrow> nat cutover_action" where
  "request_commit request healthy =
    Commit_Binding (cycle_binding_id request) (ticket_metadata (cycle_ticket request))
      (cycle_source request) (cycle_target request) (cycle_value request) healthy"

definition reports_for_commit ::
  "commit_observation list \<Rightarrow> lifecycle_state \<Rightarrow> cycle_request \<Rightarrow> cutover_result \<Rightarrow> observed_fault list"
where
  "reports_for_commit verified s request reply =
    (case reply of transition_result.Operational_Failure failure \<Rightarrow>
      map observed_cause (filter (\<lambda>observation.
        observing_authority observation \<in> lifecycle_diagnostic_authorities s \<and> observed_request observation = request \<and>
        observed_clock observation = lifecycle_clock s \<and> observed_failure observation = failure) verified)
    | _ \<Rightarrow> [])"

lemma client_report_is_authenticated_for_this_commit:
  assumes "resolved_responsibility (reports_for_commit verified s request reply) = Client_Abort"
  shows "\<exists>failure observation. reply = transition_result.Operational_Failure failure \<and>
    observation \<in> set verified \<and> observing_authority observation \<in> lifecycle_diagnostic_authorities s \<and>
    observed_request observation = request \<and>
    observed_clock observation = lifecycle_clock s \<and> observed_failure observation = failure \<and>
    blame_of (observed_cause observation) = Client_Abort"
proof (cases reply)
  case (Operational_Failure failure)
  let ?eligible = "filter (\<lambda>observation.
        observing_authority observation \<in> lifecycle_diagnostic_authorities s \<and> observed_request observation = request \<and>
        observed_clock observation = lifecycle_clock s \<and> observed_failure observation = failure) verified"
  have eligible: "map observed_cause ?eligible \<noteq> []" "\<forall>cause \<in> set (map observed_cause ?eligible). blame_of cause = Client_Abort"
    using assms[unfolded liability_requires_attributable_client_evidence] Operational_Failure
    by (simp_all add: reports_for_commit_def)
  then obtain observation where "observation \<in> set ?eligible" by (cases ?eligible) auto
  with eligible Operational_Failure show ?thesis by auto
qed (use assms in \<open>simp_all add: reports_for_commit_def\<close>)

definition checked_final_leaves where
  "checked_final_leaves evidence s request reply =
    (case remdups (filter (\<lambda>measurement.
          measuring_authority measurement \<in> lifecycle_diagnostic_authorities s \<and> measured_request measurement = request \<and>
          measured_clock measurement = lifecycle_clock s \<and> measured_reply measurement = reply \<and>
          measured_write_domains measurement = participants (request_flow request) \<and>
          finite (measured_final_leaves measurement)) (verified_measurements evidence)) of
       [measurement] \<Rightarrow> Some (card (measured_final_leaves measurement))
     | _ \<Rightarrow> None)"

lemma metered_leaf_count_has_a_verified_final_write_set:
  assumes "checked_final_leaves evidence s request reply = Some leaves"
  shows "\<exists>row \<in> set (verified_measurements evidence).
       measuring_authority row \<in> lifecycle_diagnostic_authorities s \<and>
       measured_request row = request \<and> measured_clock row = lifecycle_clock s \<and> measured_reply row = reply \<and>
       measured_write_domains row = participants (request_flow request) \<and>
       finite (measured_final_leaves row) \<and> leaves = card (measured_final_leaves row)"
proof -
  let ?matches = "remdups (filter (\<lambda>measurement.
          measuring_authority measurement \<in> lifecycle_diagnostic_authorities s \<and> measured_request measurement = request \<and>
          measured_clock measurement = lifecycle_clock s \<and> measured_reply measurement = reply \<and>
          measured_write_domains measurement = participants (request_flow request) \<and>
          finite (measured_final_leaves measurement)) (verified_measurements evidence))"
  obtain row where matches: "?matches = [row]" and count: "leaves = card (measured_final_leaves row)"
    using assms unfolding checked_final_leaves_def by (cases ?matches) (auto split: list.splits)
  have "row \<in> set ?matches" using matches by simp
  then show ?thesis using count by auto
qed

definition metered_attempt ::
  "nat flow_policy \<Rightarrow> promotion_grants \<Rightarrow> (nat \<Rightarrow> meter_schedule option)
    \<Rightarrow> commit_evidence \<Rightarrow> lifecycle_state \<Rightarrow> cycle_request \<Rightarrow> bool \<Rightarrow> cutover_result \<Rightarrow>
    nat cutover_state \<Rightarrow> accounted_cycle option" where
  "metered_attempt policy grants versions verified s request healthy reply updated =
    (case checked_final_leaves verified s request reply of None \<Rightarrow> None | Some leaves \<Rightarrow>
     observed_commit_charge policy grants (lifecycle_registry s) Committing (cycle_attempt_id request)
      (cycle_session_id request) (lifecycle_tariff s) (lifecycle_clock s) (cycle_ticket request) (cycle_binding_id request)
      (cycle_source request) (cycle_target request) (cycle_value request) healthy
      (lifecycle_cutover s) reply updated (reports_for_commit (verified_observations verified) s request reply) leaves versions)"

definition restoration_matches :: "restoration_evidence set \<Rightarrow> lifecycle_state \<Rightarrow> restoration_evidence \<Rightarrow> bool" where
  "restoration_matches confirmed s evidence \<longleftrightarrow>
    cycle_custody s = Local_Cells_Only \<and> evidence \<in> confirmed \<and>
    (\<exists>request previous. lifecycle_phase s = Partial_Cycle request previous \<and>
      restoration_attempt evidence = cycle_attempt_id request \<and>
      restoration_ticket evidence = cycle_ticket request \<and>
      restoration_values evidence = previous)"

definition lifecycle_promotable :: "bool \<Rightarrow> lifecycle_state \<Rightarrow> bool" where
  "lifecycle_promotable locks_clear s \<longleftrightarrow> locks_clear \<and> cycle_custody s = Local_Cells_Only \<and> lifecycle_phase s = Idle_Cycle \<and>
    lifecycle_registry s (fst (lifecycle_session s)) = Some (route_metadata (lifecycle_cutover s))"

definition finish_promotion where
  "finish_promotion s updated version =
    s\<lparr>lifecycle_cutover := updated, lifecycle_tariff := version,
      lifecycle_registry := (lifecycle_registry s)(fst (lifecycle_session s) \<mapsto> route_metadata updated)\<rparr>"

inductive lifecycle_step ::
  "nat flow_policy \<Rightarrow> promotion_grants \<Rightarrow> (nat \<Rightarrow> meter_schedule option)
    \<Rightarrow> restoration_evidence set \<Rightarrow> commit_evidence \<Rightarrow> bool \<Rightarrow>
    (lifecycle_state, lifecycle_command, lifecycle_reply) step_rel"
  for policy grants versions restoration_confirmed verified locks_clear
where
  Bind:
    "\<lbrakk>lifecycle_phase s = Idle_Cycle; \<not> unreconciled_soft_write (lifecycle_cutover s);
       binding_is_current policy s request\<rbrakk>
     \<Longrightarrow> lifecycle_step policy grants versions restoration_confirmed verified locks_clear s (Bind_Cycle request) Cycle_Bound
       (s\<lparr>lifecycle_phase := Bound_Cycle request\<rparr>)"
| Bind_Refused:
    "\<not> (lifecycle_phase s = Idle_Cycle \<and> \<not> unreconciled_soft_write (lifecycle_cutover s) \<and>
       binding_is_current policy s request)
     \<Longrightarrow> lifecycle_step policy grants versions restoration_confirmed verified locks_clear s
       (Bind_Cycle request) Precommit_Refused s"
| Verify:
    "lifecycle_phase s = Bound_Cycle request
     \<Longrightarrow> lifecycle_step policy grants versions restoration_confirmed verified locks_clear s (Verify_Cycle []) Cycle_Verified
       (s\<lparr>lifecycle_phase := Verified_Cycle request\<rparr>)"
| Verify_Failed:
    "\<lbrakk>lifecycle_phase s = Bound_Cycle request; reports \<noteq> []\<rbrakk>
     \<Longrightarrow> lifecycle_step policy grants versions restoration_confirmed verified locks_clear s (Verify_Cycle reports)
       Precommit_Refused (s\<lparr>lifecycle_phase := Idle_Cycle\<rparr>)"
| Commit:
    "\<lbrakk>lifecycle_phase s = Verified_Cycle request;
       binding_is_current policy s request;
       metered_attempt policy grants versions verified s request healthy reply updated = Some row\<rbrakk>
     \<Longrightarrow> lifecycle_step policy grants versions restoration_confirmed verified locks_clear s
       (Commit_Cycle healthy) (Cycle_Result reply)
       (s\<lparr>lifecycle_cutover := updated, lifecycle_invoice := append_accounted_cycle (lifecycle_invoice s) row,
          lifecycle_phase := (if (case reply of transition_result.Operational_Failure fault \<Rightarrow>
                fault = Partial_Write \<or> cycle_custody s \<noteq> Local_Cells_Only | _ \<Rightarrow> False)
            then Partial_Cycle request (binding_state (lifecycle_cutover s)) else Idle_Cycle)\<rparr>)"
| Commit_Refused:
    "\<lbrakk>lifecycle_phase s = Verified_Cycle request;
       \<not> binding_is_current policy s request \<or>
       versions (lifecycle_tariff s) = None\<rbrakk>
     \<Longrightarrow> lifecycle_step policy grants versions restoration_confirmed verified locks_clear s
       (Commit_Cycle healthy) Precommit_Refused (s\<lparr>lifecycle_phase := Idle_Cycle\<rparr>)"
| Commit_Without_Verification:
    "(\<And>request. lifecycle_phase s \<noteq> Verified_Cycle request)
     \<Longrightarrow> lifecycle_step policy grants versions restoration_confirmed verified locks_clear s
       (Commit_Cycle healthy) Precommit_Refused s"
| Commit_Awaiting_Measurement:
    "\<lbrakk>lifecycle_phase s = Verified_Cycle request; binding_is_current policy s request;
       versions (lifecycle_tariff s) \<noteq> None;
       \<And>reply updated row. metered_attempt policy grants versions verified s request healthy reply updated \<noteq> Some row\<rbrakk>
     \<Longrightarrow> lifecycle_step policy grants versions restoration_confirmed verified locks_clear s
       (Commit_Cycle healthy) Measurement_Unavailable s"
| Retry:
    "\<lbrakk>lifecycle_phase s = Partial_Cycle prior previous;
       request = prior\<lparr>cycle_attempt_id := attempt\<rparr>; binding_is_current policy s request;
       metered_attempt policy grants versions verified s request True
          (transition_result.Accepted Binding_Committed) updated = Some row; cycle_custody s = Local_Cells_Only\<rbrakk>
     \<Longrightarrow> lifecycle_step policy grants versions restoration_confirmed verified locks_clear s
       (Retry_Cycle attempt) (Cycle_Result (transition_result.Accepted Binding_Committed))
       (s\<lparr>lifecycle_cutover := updated\<lparr>unreconciled_soft_write := False\<rparr>,
          lifecycle_invoice := append_accounted_cycle (lifecycle_invoice s) row, lifecycle_phase := Idle_Cycle\<rparr>)"
| Restore:
    "restoration_matches restoration_confirmed s evidence
     \<Longrightarrow> lifecycle_step policy grants versions restoration_confirmed verified locks_clear s
       (Restore_Cycle evidence) Cycle_Restored
       (s\<lparr>lifecycle_phase := Idle_Cycle,
          lifecycle_cutover := (lifecycle_cutover s)\<lparr>binding_state := restoration_values evidence,
             unreconciled_soft_write := False\<rparr>\<rparr>)"
| Restore_Refused:
    "\<not> restoration_matches restoration_confirmed s evidence
     \<Longrightarrow> lifecycle_step policy grants versions restoration_confirmed verified locks_clear s
       (Restore_Cycle evidence) Restoration_Refused s"
| Promote:
    "\<lbrakk>lifecycle_promotable locks_clear s; versions version \<noteq> None; cutover_step policy grants (lifecycle_cutover s)
       (Confirm_Promotion epoch version) (transition_result.Accepted Promotion_Finalized) updated\<rbrakk>
     \<Longrightarrow> lifecycle_step policy grants versions restoration_confirmed verified locks_clear s
       (Promote_Cycle epoch version) Lifecycle_Promoted (finish_promotion s updated version)"
| Promote_Refused:
    "\<not> (lifecycle_promotable locks_clear s \<and> versions version \<noteq> None \<and>
       promotion_allowed grants (lifecycle_cutover s) epoch version)
     \<Longrightarrow> lifecycle_step policy grants versions restoration_confirmed verified locks_clear s
       (Promote_Cycle epoch version) Lifecycle_Promotion_Refused s"

lemma lifecycle_preparation_does_not_expose_changes_or_invoice:
  assumes "lifecycle_step policy grants versions confirmed verified locks s command reply t"
    "(\<exists>request. command = Bind_Cycle request) \<or> (\<exists>reports. command = Verify_Cycle reports)"
  shows "lifecycle_cutover t = lifecycle_cutover s \<and> lifecycle_invoice t = lifecycle_invoice s"
  using assms by (cases rule: lifecycle_step.cases) auto

theorem lifecycle_promotion_has_the_exact_safe_boundary:
  "(\<exists>updated. lifecycle_step policy grants versions confirmed verified locks s
      (Promote_Cycle epoch version) Lifecycle_Promoted updated) \<longleftrightarrow>
    lifecycle_promotable locks s \<and> versions version \<noteq> None \<and> promotion_allowed grants (lifecycle_cutover s) epoch version"
proof
  assume "\<exists>updated. lifecycle_step policy grants versions confirmed verified locks s
      (Promote_Cycle epoch version) Lifecycle_Promoted updated"
  then obtain updated where step: "lifecycle_step policy grants versions confirmed verified locks s
      (Promote_Cycle epoch version) Lifecycle_Promoted updated" by blast
  show "lifecycle_promotable locks s \<and> versions version \<noteq> None \<and> promotion_allowed grants (lifecycle_cutover s) epoch version"
    using step by (cases rule: lifecycle_step.cases) (auto elim: cutover_step.cases)
next
  assume ready: "lifecycle_promotable locks s \<and> versions version \<noteq> None \<and>
    promotion_allowed grants (lifecycle_cutover s) epoch version"
  then have real: "cutover_step policy grants (lifecycle_cutover s) (Confirm_Promotion epoch version)
    (transition_result.Accepted Promotion_Finalized)
    ((lifecycle_cutover s)\<lparr>route_metadata := promoted_metadata epoch version\<rparr>)"
    by (auto intro: cutover_step.Promote)
  show "\<exists>updated. lifecycle_step policy grants versions confirmed verified locks s
      (Promote_Cycle epoch version) Lifecycle_Promoted updated"
    using ready real by (blast intro: lifecycle_step.Promote)
qed

lemma native_promotion_still_requires_idle_model_phase:
  assumes idle: "lifecycle_phase s = Idle_Cycle"
    and custody: "cycle_custody s = Local_Cells_Only"
    and match: "degree_state native = lifecycle_cutover s"
    and registry_match: "lifecycle_registry s (fst (lifecycle_session s)) = Some (route_metadata (degree_state native))"
    and tariff: "versions version \<noteq> None"
    and actual: "promote_settled_asset policy grants epoch version native =
      (settled, transition_result.Accepted Promotion_Finalized)"
  shows "lifecycle_step policy grants versions confirmed verified (promotion_locks_clear policy native) s
    (Promote_Cycle epoch version) Lifecycle_Promoted (finish_promotion s (degree_state settled) version)"
  using settled_asset_promotion_projects_to_cutover[OF actual] idle custody match tariff registry_match
  by (auto simp: lifecycle_promotable_def intro: lifecycle_step.Promote)

theorem actual_atomic_failure_preserves_the_committed_cells:
  assumes run: "lifecycle_step policy grants versions confirmed verified locks s (Commit_Cycle healthy)
       (Cycle_Result (transition_result.Operational_Failure failure)) t"
    and atomic: "required_level (route_metadata (lifecycle_cutover s)) = Atomic"
  shows "failure = Rolled_Back \<and> binding_state (lifecycle_cutover t) = binding_state (lifecycle_cutover s)"
proof -
  from run obtain request row updated where metered:
    "metered_attempt policy grants versions verified s request healthy (transition_result.Operational_Failure failure)
      updated = Some row" and core: "lifecycle_cutover t = updated"
    by (cases rule: lifecycle_step.cases) auto
  from metered have step:
    "cutover_step policy grants (lifecycle_cutover s) (request_commit request healthy)
      (transition_result.Operational_Failure failure) updated"
    by (auto simp: metered_attempt_def request_commit_def observed_commit_charge_def Let_def
        split: if_splits option.splits)
  from step have rank:
    "level_rank (required_level (route_metadata (lifecycle_cutover s))) \<le>
      level_rank (chosen_path (route_metadata (lifecycle_cutover s)))"
    unfolding request_commit_def by (cases rule: cutover_step.cases) (auto simp: can_commit_def)
  have path: "chosen_path (route_metadata (lifecycle_cutover s)) = Atomic"
    using rank atomic by (cases "chosen_path (route_metadata (lifecycle_cutover s))") auto
  show ?thesis using step path unfolding request_commit_def core
    by (cases rule: cutover_step.cases) (auto simp: can_commit_def flow_step_def split: if_splits)
qed

lemma any_precommit_refusal_preserves_all_cells_and_the_invoice:
  assumes "lifecycle_step policy grants versions confirmed verified locks s command Precommit_Refused t"
  shows "lifecycle_cutover t = lifecycle_cutover s \<and> lifecycle_invoice t = lifecycle_invoice s"
  using assms by (cases rule: lifecycle_step.cases) auto

lemma missing_measurement_cannot_publish_a_commit_or_clear_the_phase:
  assumes step: "lifecycle_step policy grants versions confirmed verified locks s
    (Commit_Cycle healthy) reply t"
    and no_measurement: "\<And>request reply. checked_final_leaves verified s request reply = None"
  shows "lifecycle_cutover t = lifecycle_cutover s \<and> lifecycle_invoice t = lifecycle_invoice s \<and>
    (reply = Measurement_Unavailable \<longrightarrow> t = s)"
  using step no_measurement by (cases rule: lifecycle_step.cases) (auto simp: metered_attempt_def)

lemma bare_retry_and_restore_cannot_clear_a_pending_native_debit:
  assumes pending: "cycle_custody s = Native_Debit_Pending key"
  shows "lifecycle_step policy grants versions confirmed verified locks s (Restore_Cycle evidence) Restoration_Refused s"
        "\<not> lifecycle_step policy grants versions confirmed verified locks s (Restore_Cycle evidence) Cycle_Restored t"
        "\<not> lifecycle_step policy grants versions confirmed verified locks s (Retry_Cycle attempt)
                  (Cycle_Result (transition_result.Accepted Binding_Committed)) t"
  using pending by (auto simp: restoration_matches_def intro: lifecycle_step.Restore_Refused elim: lifecycle_step.cases)

lemma failed_commit_keeps_the_exact_binding_while_the_native_debit_is_pending:
  assumes "lifecycle_step policy grants versions confirmed verified locks s (Commit_Cycle healthy)
    (Cycle_Result (transition_result.Operational_Failure failure)) t"
    "lifecycle_phase s = Verified_Cycle request" "cycle_custody s = Native_Debit_Pending key"
  shows "lifecycle_phase t = Partial_Cycle request (binding_state (lifecycle_cutover s)) \<and>
    cycle_custody t = Native_Debit_Pending key"
  using assms by (cases rule: lifecycle_step.cases) auto

end
