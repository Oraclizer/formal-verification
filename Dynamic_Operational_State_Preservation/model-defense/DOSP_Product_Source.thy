theory DOSP_Product_Source
  imports DOSP_Native_Admission
begin

datatype product_source_command =
    Prepare_Native client_command
  | Observe_Route route_ticket nat nat
  | Bind_Native cycle_request execution_request
  | Verify_Native cycle_request nat execution_request
  | Meter_Native cycle_request nat message_route execution_request
  | Settle_Retained_Native cycle_request nat message_route execution_request
  | Record_Native_Commit_Failure cycle_request execution_request
  | Retry_Local client_call_id
  | Retry_Protected cycle_request nat message_route execution_request
  | Reconcile_Native reconciliation_lease nat execution_request
  | Abort_Unexecuted_Native reconciliation_lease nat execution_request
  | Release_Live_Native_Reversal nat execution_request nat version_vector
  | Renew_Pending_Native nat execution_request nat
  | Restore_Native restoration_evidence nat nat execution_request nat
  | Promote_Native nat nat
  | Advance_Native_Clock nat
  | Report_Replica_Receipt nat nat eab_primary_receipt
  | Update_Recovery product_recovery_command

datatype product_source_reply =
    Binding_Outcome lifecycle_reply | Released_Outcome bool | Promotion_Outcome cutover_result
  | Native_Settlement_Pending source_key
  | Preparation_Outcome finality_reply
  | Observation_Outcome flow_result
  | Recovery_Outcome "nat repair_result"
  | Clock_Outcome bool

definition protected_retry_is_current where
  "protected_retry_is_current p request index r \<longleftrightarrow>
    (let s = source_lifecycle p; native = current_operational (source_consensus p); b = request_binding r in
      (\<exists>prior previous. lifecycle_phase s = Partial_Cycle prior previous \<and>
        request = prior\<lparr>cycle_attempt_id := cycle_attempt_id request\<rparr>) \<and>
      cycle_custody s = Native_Debit_Pending (binding_key b) \<and> native_source_pending native r \<and>
      cycle_names_native_binding request r \<and> current_binding_holds_its_native_lock native r \<and>
      exact_record_reference (credit_core native) index b Confirmed_Decision (request_certificate r))"

definition clear_reconciled_soft_write where
  "clear_reconciled_soft_write p =
    (let s = source_lifecycle p; a = source_consensus p; native = current_operational a;
          restored = (lifecycle_cutover s)\<lparr>unreconciled_soft_write := False\<rparr>
     in p\<lparr>source_lifecycle := s\<lparr>lifecycle_cutover := restored\<rparr>,
          source_consensus := with_operational_state (native\<lparr>degree_state := restored\<rparr>) a\<rparr>)"

fun update_divergence_work :: "nat repair_result \<Rightarrow> nat set \<Rightarrow> nat set" where
  "update_divergence_work (transition_result.Accepted (Opened job)) jobs = insert job jobs"
| "update_divergence_work (transition_result.Accepted (Installed job domain sequence)) jobs = jobs - {job}"
| "update_divergence_work _ jobs = jobs"

fun failed_credit_observation :: "lifecycle_custody \<Rightarrow> lifecycle_reply \<Rightarrow> product_source_reply" where
  "failed_credit_observation (Native_Debit_Pending key) (Cycle_Result (transition_result.Operational_Failure fault)) =
    Native_Settlement_Pending key"
| "failed_credit_observation _ reply = Binding_Outcome reply"

definition route_activation_is_due where
  "route_activation_is_due a repair grants \<longleftrightarrow>
    (\<exists>change epoch boundary. route_change_is_applicable repair change \<and>
      current_grant grants repair change epoch boundary (consensus_now a))"

context integrated_dosp_authority
begin

definition a_replica_shows_a_different_issued_receipt ::
  "integrated_authority \<Rightarrow> available_journals \<Rightarrow> nat recovery_state \<Rightarrow> eab_primary_receipt \<Rightarrow> bool" where
  "a_replica_shows_a_different_issued_receipt a sources repair receipt \<longleftrightarrow>
    current_primary_is_recorded a repair \<and>
    binding_asset (published_binding receipt) = registered_asset (current_operational a) \<and>
    (\<exists>current. issued_receipt a (primary_sequence repair) = Some current \<and> receipt \<noteq> current) \<and>
    (issued_receipt a (published_sequence receipt) = Some receipt \<or>
      (\<exists>issuer original. sources issuer = Some original \<and>
        journal.checked_current_replay original (current_source_candidate original) = Some (call_authority_state original) \<and>
        issued_receipt (call_authority_state original) (published_sequence receipt) = Some receipt))"

definition product_source_step where
  "product_source_step versions confirmed evidence administrators approvals sources head offers grants p command reply q \<longleftrightarrow>
    (let s = source_lifecycle p; a = source_consensus p; native = current_operational a; repair = source_recovery p;
         routes_current = (\<not> route_activation_is_due a repair grants);
         reserved_jobs = outstanding_join_jobs repair grants in
      case command of
        Prepare_Native command \<Rightarrow>
          (if (needs_active_native_route command \<longrightarrow> routes_current) \<and>
              (\<exists>response updated. prepare_product_credit p command response updated)
           then (\<exists>response. prepare_product_credit p command response q \<and> reply = Preparation_Outcome response)
           else reply = Binding_Outcome Precommit_Refused \<and> q = p)
      | Observe_Route ticket origin receiver \<Rightarrow>
          (if routes_current \<and> lifecycle_phase s = Idle_Cycle \<and> cycle_custody s = Local_Cells_Only \<and>
              \<not> unreconciled_soft_write (lifecycle_cutover s) \<and>
              origin \<in> active_domains repair \<and> receiver \<in> active_domains repair \<and>
              lifecycle_cutover s = degree_state native
           then let observed = route_and_execute (authority_registry a) flow_policy (registered_asset native) ticket True
                      (binding_state (degree_state native)) (Read_From origin receiver);
                    view = (degree_state native)\<lparr>binding_state := fst observed\<rparr>
                in reply = Observation_Outcome (snd observed) \<and>
                   q = p\<lparr>source_lifecycle := s\<lparr>lifecycle_cutover := view\<rparr>,
                        source_consensus := with_operational_state (native\<lparr>degree_state := view\<rparr>) a\<rparr>
           else reply = Observation_Outcome (transition_result.Rejected ()) \<and> q = p)
      | Bind_Native request r \<Rightarrow>
          (if routes_current \<and> cycle_session_id request = active_session \<and> recovery_permits_native_credit p \<and>
              routed_domains_are_active repair r
           then (\<exists>response t. native_bind_step flow_policy promotion_authorizations versions confirmed evidence s native request r response t \<and>
             reply = Binding_Outcome response \<and> q = p\<lparr>source_lifecycle := t\<rparr>)
           else reply = Binding_Outcome Precommit_Refused \<and> q = p)
      | Verify_Native request index r \<Rightarrow>
          (\<exists>response t. native_verify_step flow_policy promotion_authorizations versions confirmed evidence s native request index r response t \<and>
             reply = Binding_Outcome response \<and> q = p\<lparr>source_lifecycle := t\<rparr>)
      | Meter_Native request index route r \<Rightarrow>
          (if routes_current
           then (\<exists>response. reply = Binding_Outcome response \<and>
             joint_credit_excluding_jobs reserved_jobs Active_Credit_Route versions confirmed evidence p request index route r response q)
           else reply = Binding_Outcome Precommit_Refused \<and> q = p)
      | Settle_Retained_Native request index route r \<Rightarrow>
          (\<exists>response. reply = Binding_Outcome response \<and>
            joint_credit_excluding_jobs reserved_jobs Retained_Debit_Route versions confirmed evidence p request index route r response q)
      | Record_Native_Commit_Failure request r \<Rightarrow>
          (\<exists>response. reply = failed_credit_observation (cycle_custody (source_lifecycle q)) response \<and>
            joint_failed_credit_step (flow_policy,promotion_authorizations,active_session) (versions,confirmed,evidence) (p,request,r,response,q))
      | Retry_Local attempt \<Rightarrow>
          (if (\<exists>t. routes_current \<and> recovery_permits_native_credit p \<and> lifecycle_cutover s = degree_state native \<and> lifecycle_registry s = authority_registry a \<and>
                 lifecycle_step flow_policy promotion_authorizations versions confirmed evidence (promotion_locks_clear flow_policy native)
                   (s\<lparr>lifecycle_clock := consensus_now a\<rparr>) (Retry_Cycle attempt)
                   (Cycle_Result (transition_result.Accepted Binding_Committed)) t)
           then (\<exists>t. lifecycle_step flow_policy promotion_authorizations versions confirmed evidence (promotion_locks_clear flow_policy native)
                   (s\<lparr>lifecycle_clock := consensus_now a\<rparr>) (Retry_Cycle attempt)
                   (Cycle_Result (transition_result.Accepted Binding_Committed)) t \<and>
                 reply = Binding_Outcome (Cycle_Result (transition_result.Accepted Binding_Committed)) \<and>
                 q = p\<lparr>source_lifecycle := t, source_consensus := with_operational_state (native\<lparr>degree_state := lifecycle_cutover t\<rparr>) a\<rparr>)
           else reply = Binding_Outcome Precommit_Refused \<and> q = p)
      | Retry_Protected request index route r \<Rightarrow>
          (let prepared = p\<lparr>source_lifecycle := s\<lparr>lifecycle_phase := Verified_Cycle request\<rparr>\<rparr>;
                retry = joint_credit_excluding_jobs reserved_jobs Retained_Debit_Route versions confirmed evidence prepared request index route r
                  (Cycle_Result (transition_result.Accepted Binding_Committed)) in
           if protected_retry_is_current p request index r \<and> (\<exists>updated. retry updated)
           then reply = Binding_Outcome (Cycle_Result (transition_result.Accepted Binding_Committed)) \<and>
                (\<exists>updated. retry updated \<and> q = clear_reconciled_soft_write updated)
           else reply = Binding_Outcome Precommit_Refused \<and> q = p)
      | Reconcile_Native lease index r \<Rightarrow>
          (\<exists>released t b. clear_confirmed_custody s a lease index r released t b \<and>
             reply = Released_Outcome released \<and> q = p\<lparr>source_lifecycle := t, source_consensus := b\<rparr>)
      | Abort_Unexecuted_Native lease index r \<Rightarrow>
          (\<exists>released. abort_unexecuted_credit p lease index r released q \<and> reply = Released_Outcome released)
      | Release_Live_Native_Reversal index r generation versions \<Rightarrow>
          (\<exists>released. release_live_reversed_debit p index r generation versions released q \<and> reply = Released_Outcome released)
      | Renew_Pending_Native index r duration \<Rightarrow>
          (\<exists>renewed. reassign_pending_product_debit p index r duration renewed q \<and> reply = Released_Outcome renewed)
      | Restore_Native restoration epoch index r duration \<Rightarrow>
          (if (\<exists>t updated. restore_with_native_terminal flow_policy promotion_authorizations versions confirmed evidence
                 s native restoration epoch index r duration t updated)
           then reply = Binding_Outcome Cycle_Restored \<and>
             (\<exists>t updated. restore_with_native_terminal flow_policy promotion_authorizations versions confirmed evidence
               s native restoration epoch index r duration t updated \<and>
               q = p\<lparr>source_lifecycle := t, source_consensus := with_operational_state updated a\<rparr>)
           else reply = Binding_Outcome Restoration_Refused \<and> q = p)
      | Promote_Native epoch version \<Rightarrow>
          (\<exists>response t updated. guarded_native_promotion flow_policy promotion_authorizations versions s native
             epoch version response t updated \<and>
             reply = Promotion_Outcome response \<and>
             q = p\<lparr>source_lifecycle := t, source_consensus := with_operational_state updated a\<rparr>)
      | Advance_Native_Clock seconds \<Rightarrow>
          (\<exists>b applied. execute_integrated_consensus (Advance_Consensus_Time seconds) a = (b, Clock_Result applied) \<and>
             reply = Clock_Outcome applied \<and>
             q = p\<lparr>source_lifecycle := s\<lparr>lifecycle_clock := consensus_now b\<rparr>, source_consensus := b\<rparr>)
      | Report_Replica_Receipt job domain receipt \<Rightarrow>
          (if domain \<in> active_domains repair \<and> a_replica_shows_a_different_issued_receipt a sources repair receipt
           then (case recovery_job_for_observation repair grants job of
               None \<Rightarrow> reply = Recovery_Outcome (transition_result.Operational_Failure Evidence_Unavailable) \<and> q = p
             | Some assigned \<Rightarrow> if fresh_work repair assigned
               then reply = Recovery_Outcome (transition_result.Accepted (Opened assigned)) \<and>
                 q = p\<lparr>source_recovery := repair\<lparr>work_owner := (work_owner repair)(assigned \<mapsto> domain)\<rparr>,
                   observed_divergence_work := insert assigned (observed_divergence_work p)\<rparr>
               else reply = Recovery_Outcome (transition_result.Operational_Failure Evidence_Unavailable) \<and> q = p)
           else reply = Recovery_Outcome (transition_result.Internal ()) \<and> q = p)
      | Update_Recovery request \<Rightarrow>
          (if (\<exists>tx. request = Trade_After_Recovery tx) \<and>
                (\<not> routes_current \<or> lifecycle_phase s \<noteq> Idle_Cycle \<or> cycle_custody s \<noteq> Local_Cells_Only \<or>
                 unreconciled_soft_write (lifecycle_cutover s) \<or> observed_divergence_work p \<noteq> {} \<or>
                 \<not> current_primary_is_recorded a repair \<or>
                 asset_owner (machine_state (core_parent (credit_core native))) (registered_asset native) \<noteq> None)
           then reply = Recovery_Outcome (transition_result.Rejected Recovery_Blocks_Trade) \<and> q = p
           else (\<exists>response t. product_recovery_step a administrators approvals sources head offers grants repair request response t \<and>
              reply = Recovery_Outcome response \<and> q = p\<lparr>source_recovery := t,
                observed_divergence_work := update_divergence_work response (observed_divergence_work p)\<rparr>)))"

lemma recorded_divergence_blocks_new_native_credit_even_before_first_publication:
  assumes "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Update_Recovery (Register_Divergence requested domain observed))
    (Recovery_Outcome (transition_result.Accepted (Opened job))) q"
  shows "job \<in> observed_divergence_work q \<and> \<not> recovery_permits_native_credit q"
  using assms by (auto simp: product_source_step_def recovery_permits_native_credit_def Let_def)

lemma a_required_pending_debit_is_reported_as_awaiting_settlement:
  assumes step: "joint_failed_credit_step (flow_policy,promotion_authorizations,active_session) (versions,confirmed,evidence)
    (p,request,r,Cycle_Result (transition_result.Operational_Failure fault),q)"
    and custody: "cycle_custody (source_lifecycle q) = Native_Debit_Pending key"
  shows "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Record_Native_Commit_Failure request r) (Native_Settlement_Pending key) q"
  using assms by (auto simp: product_source_step_def Let_def intro: exI[of _ "Cycle_Result (transition_result.Operational_Failure fault)"])

lemma observations_after_departure_use_the_current_membership:
  assumes "origin \<notin> active_domains (source_recovery p)"
  shows "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Observe_Route ticket origin receiver) reply q \<longleftrightarrow>
      reply = Observation_Outcome (transition_result.Rejected ()) \<and> q = p"
  using assms by (simp add: product_source_step_def Let_def)

lemma fresh_native_preparation_waits_for_due_route_activation:
  assumes "route_activation_is_due (source_consensus p) (source_recovery p) grants"
    "needs_active_native_route command"
  shows "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Prepare_Native command) reply q \<longleftrightarrow> reply = Binding_Outcome Precommit_Refused \<and> q = p"
  using assms by (simp add: product_source_step_def Let_def)

lemma a_receipt_regression_opens_work_even_when_its_replica_value_matches:
  assumes "domain \<in> active_domains (source_recovery p)" "fresh_work (source_recovery p) job"
    "a_replica_shows_a_different_issued_receipt (source_consensus p) sources (source_recovery p) receipt"
    "recovery_job_for_observation (source_recovery p) grants requested = Some job"
  shows "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Report_Replica_Receipt requested domain receipt) (Recovery_Outcome (transition_result.Accepted (Opened job)))
    (p\<lparr>source_recovery := (source_recovery p)\<lparr>work_owner := (work_owner (source_recovery p))(job \<mapsto> domain)\<rparr>,
      observed_divergence_work := insert job (observed_divergence_work p)\<rparr>)"
  using assms by (simp add: product_source_step_def Let_def)

lemma observing_a_receipt_cannot_consume_an_outstanding_join_job:
  assumes "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Report_Replica_Receipt requested domain receipt) (Recovery_Outcome (transition_result.Accepted (Opened job))) q"
  shows "job \<notin> outstanding_join_jobs (source_recovery p) grants"
proof -
  have selected: "recovery_job_for_observation (source_recovery p) grants requested = Some job"
    using assms by (auto simp: product_source_step_def Let_def split: if_splits option.splits)
  show ?thesis by (rule a_selected_observation_job_is_never_reserved[OF selected])
qed

lemma observing_the_current_receipt_cannot_create_divergent_work:
  assumes "issued_receipt (source_consensus p) (primary_sequence (source_recovery p)) = Some receipt"
  shows "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Report_Replica_Receipt job domain receipt) reply q \<longleftrightarrow>
    reply = Recovery_Outcome (transition_result.Internal ()) \<and> q = p"
  using assms by (simp add: product_source_step_def a_replica_shows_a_different_issued_receipt_def Let_def)

lemma a_receipt_for_another_asset_cannot_open_a_replica_job:
  assumes "binding_asset (published_binding receipt) \<noteq> registered_asset (current_operational (source_consensus p))"
  shows "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Report_Replica_Receipt job domain receipt) reply q \<longleftrightarrow>
    reply = Recovery_Outcome (transition_result.Internal ()) \<and> q = p"
  using assms by (simp add: product_source_step_def a_replica_shows_a_different_issued_receipt_def Let_def)

lemma recorded_replica_divergence_blocks_ordinary_trade:
  assumes "observed_divergence_work p \<noteq> {}"
  shows "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Update_Recovery (Trade_After_Recovery tx)) reply q \<longleftrightarrow>
    reply = Recovery_Outcome (transition_result.Rejected Recovery_Blocks_Trade) \<and> q = p"
  using assms by (simp add: product_source_step_def Let_def)

lemma an_inflight_binding_blocks_the_products_ordinary_trade:
  assumes "\<not> (lifecycle_phase (source_lifecycle p) = Idle_Cycle \<and> cycle_custody (source_lifecycle p) = Local_Cells_Only \<and>
    \<not> unreconciled_soft_write (lifecycle_cutover (source_lifecycle p)))"
  shows "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Update_Recovery (Trade_After_Recovery tx)) reply q \<longleftrightarrow>
    reply = Recovery_Outcome (transition_result.Rejected Recovery_Blocks_Trade) \<and> q = p"
  using assms by (auto simp: product_source_step_def Let_def)

lemma native_reservation_blocks_trade_even_if_the_local_phase_is_idle:
  assumes "asset_owner (machine_state (core_parent (credit_core (current_operational (source_consensus p)))))
        (registered_asset (current_operational (source_consensus p))) \<noteq> None"
  shows "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Update_Recovery (Trade_After_Recovery tx)) reply q \<longleftrightarrow>
    reply = Recovery_Outcome (transition_result.Rejected Recovery_Blocks_Trade) \<and> q = p"
  using assms by (simp add: product_source_step_def Let_def)

lemma a_read_only_registered_degree_refuses_the_native_reservation:
  assumes "required_level (route_metadata (degree_state (current_operational (source_consensus p))))
    \<in> {Static, Observation}"
  shows "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Prepare_Native (Client_Protocol endpoint index (Reserve_Intent r expected duration))) reply q \<longleftrightarrow>
    reply = Binding_Outcome Precommit_Refused \<and> q = p"
proof -
  have cannot_reserve: "\<not> prepare_product_credit p
      (Client_Protocol endpoint index (Reserve_Intent r expected duration)) result updated" for result updated
  proof
    assume reserve: "prepare_product_credit p
      (Client_Protocol endpoint index (Reserve_Intent r expected duration)) result updated"
    from assms native_reservation_requires_a_degree_that_permits_commit[OF reserve] show False by auto
  qed
  have absent: "\<not> (\<exists>response updated. prepare_product_credit p
      (Client_Protocol endpoint index (Reserve_Intent r expected duration)) response updated)"
    using cannot_reserve by blast
  show ?thesis by (simp add: product_source_step_def Let_def absent)
qed

lemma registry_observation_does_not_publish_a_charge_or_primary_record:
  assumes "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Observe_Route ticket origin receiver) reply q"
  shows "lifecycle_invoice (source_lifecycle q) = lifecycle_invoice (source_lifecycle p) \<and>
    source_authority (current_operational (source_consensus q)) = source_authority (current_operational (source_consensus p)) \<and>
    billing_history (lifecycle_cutover (source_lifecycle q)) = billing_history (lifecycle_cutover (source_lifecycle p))"
  using assms by (auto simp: product_source_step_def with_operational_state_def Let_def split: if_splits)

lemma an_accepted_clock_input_updates_the_same_product_state:
  assumes "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Advance_Native_Clock seconds) (Clock_Outcome True) q"
  shows "seconds \<ge> consensus_now (source_consensus p) \<and> consensus_now (source_consensus q) = seconds \<and>
    lifecycle_clock (source_lifecycle q) = seconds \<and> source_recovery q = source_recovery p"
  using assms by (auto simp: product_source_step_def Let_def split: if_splits)

lemma ordinary_trade_reopens_when_native_custody_and_repair_work_are_settled:
  assumes local: "lifecycle_phase (source_lifecycle p) = Idle_Cycle"
    "cycle_custody (source_lifecycle p) = Local_Cells_Only"
    "\<not> unreconciled_soft_write (lifecycle_cutover (source_lifecycle p))"
    and unlocked: "asset_owner (machine_state (core_parent (credit_core (current_operational (source_consensus p)))))
        (registered_asset (current_operational (source_consensus p))) = None"
    and consistent: "current_primary_is_recorded (source_consensus p) (source_recovery p)" "pending_ids (source_recovery p) = {}"
      "rollback_incomplete (source_recovery p) \<Longrightarrow> pending_ids (source_recovery p) \<noteq> {}"
      "observed_divergence_work p = {}"
      "\<not> route_activation_is_due (source_consensus p) (source_recovery p) grants"
  shows "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Update_Recovery (Trade_After_Recovery tx)) (Recovery_Outcome (transition_result.Accepted (Traded tx))) p"
proof -
  have "\<not> rollback_incomplete (source_recovery p)" using consistent by blast
  then have trade: "recovery_step grants {} (source_recovery p) (Ordinary_Trade tx)
    (transition_result.Accepted (Traded tx)) (source_recovery p)"
    by (rule recovery_step.Admit_Trade[OF consistent(2)])
  show ?thesis using local unlocked consistent(1,4,5) trade
    by (auto simp: product_source_step_def product_recovery_step_def offered_recovery_step_def Let_def
      intro: exI[of _ "source_recovery p"])
qed

lemma a_protected_retry_without_current_confirmation_keeps_both_states:
  assumes "\<not> exact_record_reference (credit_core (current_operational (source_consensus p))) index
    (request_binding r) Confirmed_Decision (request_certificate r)"
  shows "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
    (Retry_Protected request index route r) reply q \<longleftrightarrow> reply = Binding_Outcome Precommit_Refused \<and> q = p"
  using assms by (simp add: product_source_step_def protected_retry_is_current_def Let_def)

lemma product_metering_uses_the_updated_membership_in_the_same_state:
  assumes leave: "product_source_step versions confirmed evidence administrators approvals sources head offers grants p
      (Update_Recovery (Activate_Route (Leave_Domain old successor) epoch boundary))
      (Recovery_Outcome (transition_result.Accepted (Left old successor))) q"
    and destination: "binding_destination (request_binding r) = old"
  shows "product_source_step versions confirmed evidence administrators approvals sources head offers grants q
      (Meter_Native request index route r) reply t \<longleftrightarrow>
    reply = Binding_Outcome Precommit_Refused \<and> t = q"
proof -
  obtain updated where changes:
    "recovery_step grants {} (source_recovery p)
        (Activate (Leave_Domain old successor) epoch boundary (consensus_now (source_consensus p)))
        (transition_result.Accepted (Left old successor)) updated"
    and state: "source_recovery q = updated"
    using leave by (auto simp: product_source_step_def product_recovery_step_def consensus_membership_step_def
      activation_uses_the_existing_grant_and_handoff Let_def split: if_splits)
  have left: "old \<notin> active_domains updated"
    using changes by (cases rule: recovery_step.cases) auto
  then show ?thesis using destination
    by (simp add: product_source_step_def joint_credit_excluding_jobs_def joint_publication_transition_def
      joint_credit_candidate_def routed_domains_are_active_def state Let_def)
qed

end

end
