theory DOSP_Joint_Failure
  imports DOSP_Joint_Metering
begin

definition product_public_usage where
  "product_public_usage p = map usage_row_for_epoch (lifecycle_invoice (source_lifecycle p))"

definition expired_native_binding :: "metered_source_state \<Rightarrow> execution_request \<Rightarrow> bool" where
  "expired_native_binding native r \<longleftrightarrow>
    (let core = credit_core native; b = request_binding r; key = binding_key b; state = machine_state (core_parent core)
     in current_use_allowed (lock_authority (current_lock_view core (fst key))) r \<and>
      (\<exists>reservation. reservation_at state key = Some reservation \<and> reservation_binding reservation = b \<and>
        reservation_deadline reservation \<le> reservation_clock state))"

lemma a_verified_timeout_is_network_liability:
  assumes "Lock_Timeout \<in> set reports"
  shows "resolved_responsibility reports = Network_Abort"
  using assms by (cases reports) (auto simp: list_all_iff split: if_splits)

type_synonym failure_policy = "nat flow_policy \<times> promotion_grants \<times> oracle_session_identity"
type_synonym failure_evidence = "(nat \<Rightarrow> meter_schedule option) \<times> restoration_evidence set \<times> commit_evidence"
type_synonym failed_credit_event = "product_source_state \<times> cycle_request \<times> execution_request \<times> lifecycle_reply \<times> product_source_state"

definition joint_failed_credit_step :: "failure_policy \<Rightarrow> failure_evidence \<Rightarrow> failed_credit_event \<Rightarrow> bool"
where
  "joint_failed_credit_step policy evidence_in event \<longleftrightarrow>
    (case policy of (flow_policy,promotion_authorizations,active_session) \<Rightarrow>
      case evidence_in of (versions,confirmed,evidence) \<Rightarrow>
      case event of (p,request,r,reply,q) \<Rightarrow>
    (let a = source_consensus p;
         native = current_operational a;
         stamped = (source_lifecycle p)\<lparr>lifecycle_clock := consensus_now a\<rparr>;
         b = request_binding r;
         eligible = (\<lambda>fault t. (routed_domains_are_active (source_recovery p) r \<or>
           (\<exists>index. retained_credit_admission p request index r)) \<and>
           recovery_permits_existing_native_credit p \<and>
           binding_key b \<notin> core_published (credit_core native) \<and>
           (current_binding_holds_its_native_lock native r \<or> (expired_native_binding native r \<and>
             Lock_Timeout \<in> set (reports_for_commit (verified_observations evidence) stamped request
               (transition_result.Operational_Failure fault)))) \<and>
           lifecycle_phase stamped = Verified_Cycle request \<and> cycle_session_id request = active_session \<and>
           lifecycle_cutover stamped = degree_state native \<and> lifecycle_registry stamped = authority_registry a \<and>
           recorded_success_history stamped = billing_history (degree_state native) \<and>
           tariffs_cover_recorded_usage versions stamped \<and>
           cycle_names_native_binding request r \<and>
           lifecycle_step flow_policy promotion_authorizations versions confirmed evidence (promotion_locks_clear flow_policy native)
             stamped (Commit_Cycle False) (Cycle_Result (transition_result.Operational_Failure fault)) t)
     in if (\<exists>fault t. eligible fault t)
        then (\<exists>fault t. eligible fault t \<and> reply = Cycle_Result (transition_result.Operational_Failure fault) \<and>
          q = p\<lparr>source_lifecycle := t, source_consensus :=
            with_operational_state (native\<lparr>degree_state := lifecycle_cutover t\<rparr>) a\<rparr>)
        else reply = Precommit_Refused \<and> q = p))"

lemma failed_product_commit_preserves_native_publication_and_lock_history:
  assumes "joint_failed_credit_step (flow_policy,promotion_authorizations,active_session) (versions,confirmed,evidence) (p,request,r,reply,q)"
  shows "source_authority (current_operational (source_consensus q)) =
      source_authority (current_operational (source_consensus p)) \<and>
    committed_cycles (metered_ledger (source_consensus q)) = committed_cycles (metered_ledger (source_consensus p)) \<and>
    source_recovery q = source_recovery p \<and>
    (reply = Precommit_Refused \<longrightarrow> q = p)"
  using assms by (auto simp: joint_failed_credit_step_def with_operational_state_def Let_def split: if_splits)

lemma a_published_binding_cannot_be_metered_as_an_abort:
  assumes "binding_key (request_binding r) \<in> core_published (credit_core (current_operational (source_consensus p)))"
  shows "joint_failed_credit_step (flow_policy,promotion_authorizations,active_session) (versions,confirmed,evidence) (p,request,r,reply,q)
    \<longleftrightarrow> reply = Precommit_Refused \<and> q = p"
  using assms by (simp add: joint_failed_credit_step_def Let_def)

lemma an_accepted_failed_commit_publishes_its_charge_cause_on_the_consensus_day:
  assumes step: "joint_failed_credit_step (flow_policy,promotion_authorizations,active_session) (versions,confirmed,evidence)
    (p,request,r,Cycle_Result (transition_result.Operational_Failure fault),q)"
  shows "\<exists>row. product_public_usage q = product_public_usage p @ [row] \<and>
    public_abort_cause row \<noteq> None \<and>
    public_billing_day row = billing_day (consensus_now (source_consensus p))"
proof -
  let ?a = "source_consensus p"
  let ?stamped = "(source_lifecycle p)\<lparr>lifecycle_clock := consensus_now ?a\<rparr>"
  obtain t where effect: "source_lifecycle q = t"
    and actual: "lifecycle_step flow_policy promotion_authorizations versions confirmed evidence
      (promotion_locks_clear flow_policy (current_operational ?a)) ?stamped
      (Commit_Cycle False) (Cycle_Result (transition_result.Operational_Failure fault)) t"
    using step by (auto simp: joint_failed_credit_step_def Let_def split: if_splits)
  obtain cycle updated row where booked: "lifecycle_invoice t = append_accounted_cycle (lifecycle_invoice ?stamped) row"
    and current: "binding_is_current flow_policy ?stamped cycle"
    and metered: "metered_attempt flow_policy promotion_authorizations versions evidence ?stamped cycle False
      (transition_result.Operational_Failure fault) updated = Some row"
    using actual by (cases rule: lifecycle_step.cases) auto
  have fields: "accounted_attempt row = cycle_attempt_id cycle \<and>
    accounted_abort row \<noteq> None \<and> accounted_clock row = consensus_now ?a"
    using metered by (auto simp: metered_attempt_def observed_commit_charge_def Let_def split: option.splits if_splits)
  have fresh: "cycle_attempt_id cycle \<notin> image accounted_attempt (set (lifecycle_invoice ?stamped))"
    using current unfolding binding_is_current_def by blast
  have appended: "lifecycle_invoice t = lifecycle_invoice (source_lifecycle p) @ [row]"
    using booked fields fresh by (simp add: append_accounted_cycle_def)
  show ?thesis using appended fields effect
    by (intro exI[of _ "usage_row_for_epoch row"]) (simp add: product_public_usage_def usage_row_for_epoch_def settlement_epoch_def Let_def)
qed

end
