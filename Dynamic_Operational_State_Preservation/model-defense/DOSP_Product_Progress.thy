theory DOSP_Product_Progress
  imports DOSP_Classified_Entry
begin

type_synonym product_repair_event = "(nat recovery_state, product_recovery_command, nat repair_result) transition"

lemma native_recovery_permissions_mono:
  assumes permission: "governance \<subseteq> enlarged"
    and known: "recovery_step grants governance s action reply t"
  shows "recovery_step grants enlarged s action reply t"
  using known permission by (cases rule: recovery_step.cases) (auto intro: recovery_step.intros)

context integrated_dosp_authority
begin

lemma an_accepted_product_recovery_consumes_the_same_available_authority:
  assumes "product_step_with_supply input p (Update_Recovery action) (Recovery_Outcome (transition_result.Accepted outcome)) q"
  shows "product_recovery_step (source_consensus p) (supplied_administrators input) (supplied_approvals input)
    (supplied_journals input) (supplied_head input) (supplied_offers input) (supplied_routing_grants input)
    (source_recovery p) action (transition_result.Accepted outcome) (source_recovery q)"
  using assms by (auto simp: product_step_with_supply_def product_source_step_def Let_def split: if_splits)

lemma offered_recovery_permissions_mono:
  assumes "allowed \<subseteq> all_ids"
    "offered_recovery_step sources head offers grants allowed s action reply t"
  shows "offered_recovery_step sources head offers grants all_ids s action reply t"
  using assms by (auto simp: offered_recovery_step_def receipt_repair_step_def
    split: if_splits option.splits prod.splits intro: native_recovery_permissions_mono)

lemma product_recovery_projects_to_the_same_step_or_a_refusal:
  assumes step: "product_recovery_step a authorities confirmed sources head offers grants s command reply t"
  shows "offered_recovery_step sources head offers grants (image approval_id confirmed)
    s (product_native_repair a grants s command) reply t \<or>
    ((\<nexists>ok. reply = transition_result.Accepted ok) \<and> t = s)"
proof (cases command)
  case (Resolve_Rollback approval job seq)
  show ?thesis
  proof (cases "resync_permitted authorities confirmed (registered_asset (current_operational a)) s approval job seq")
    case True
    have key: "{approval_id approval} \<subseteq> image approval_id confirmed"
      using True by (auto simp: resync_permitted_def)
    have real: "offered_recovery_step sources head offers grants {approval_id approval}
       s (Governance_Resync (approval_id approval) job seq) reply t \<or>
       (reply = transition_result.Operational_Failure Evidence_Unavailable \<and> t = s)"
      using step Resolve_Rollback True by (auto simp: product_recovery_step_def scoped_resync_def Let_def split: if_splits)
    then show ?thesis unfolding Resolve_Rollback product_native_repair.simps
      using offered_recovery_permissions_mono[OF key] by auto
  next
    case False
    with step show ?thesis
      by (simp add: Resolve_Rollback product_recovery_step_def scoped_resync_def)
  qed
qed (use step in \<open>auto simp: product_recovery_step_def consensus_membership_step_def
  split: if_splits option.splits intro: offered_recovery_permissions_mono[OF empty_subsetI]\<close>)

definition product_accounting_event ::
  "integrated_authority \<Rightarrow> nat routing_grants \<Rightarrow> product_repair_event \<Rightarrow> nat repair_event" where
  "product_accounting_event a grants e =
    (if (\<exists>ok. step_outcome e = transition_result.Accepted ok)
     then mk_event (source_state e) (product_native_repair a grants (source_state e) (step_action e)) (step_outcome e) (target_state e)
     else mk_event (source_state e) Wait_For_Source (transition_result.Internal ()) (target_state e))"

lemma product_accounting_keeps_both_states [simp]:
  "source_state (product_accounting_event a grants e) = source_state e"
  "target_state (product_accounting_event a grants e) = target_state e"
  by (simp_all add: product_accounting_event_def mk_event_def)

lemma product_accounting_is_valid_at_the_actual_scope:
  assumes occurrence: "step_occurs (product_recovery_step a authorities confirmed sources head offers grants) e"
  shows "step_occurs (offered_recovery_step sources head offers grants (image approval_id confirmed))
    (product_accounting_event a grants e)"
proof (cases "\<exists>ok. step_outcome e = transition_result.Accepted ok")
  case True
  from product_recovery_projects_to_the_same_step_or_a_refusal[OF occurrence[unfolded step_occurs_def]] True
  show ?thesis by (simp add: product_accounting_event_def mk_event_def step_occurs_def)
next
  case False
  have "target_state e = source_state e"
  proof -
    from product_recovery_projects_to_the_same_step_or_a_refusal[OF occurrence[unfolded step_occurs_def]]
    consider (native) "offered_recovery_step sources head offers grants (image approval_id confirmed)
        (source_state e) (product_native_repair a grants (source_state e) (step_action e)) (step_outcome e) (target_state e)" | (still) "target_state e = source_state e"
      by auto
    then show ?thesis
    proof cases
      case native
      from offered_recovery_uses_a_native_step_or_refuses_without_effect[OF native] False
      show ?thesis by (auto elim: recovery_step.cases)
    next
      case still then show ?thesis .
    qed
  qed
  with False show ?thesis by (simp add: product_accounting_event_def mk_event_def step_occurs_def
    offered_recovery_step_def recovery_step.Idle)
qed

theorem verified_product_repairs_finish_after_finite_interference:
  fixes events :: "nat \<Rightarrow> product_repair_event"
    and authorities_at :: "nat \<Rightarrow> integrated_authority"
    and grants :: "nat routing_grants"
  defines "accounting \<equiv> \<lambda>i. product_accounting_event (authorities_at i) grants (events i)"
  assumes start: "source_state (events 0) \<in> initial"
    and run: "\<And>i. source_state (events i) \<in> recovery_carrier \<and>
      step_occurs (product_recovery_step (authorities_at i) administrators approvals (sources i) (heads i) (offers i) grants) (events i) \<and>
      target_state (events i) = source_state (events (Suc i))"
    and finite: "finite {i. recovery_interference heads accounting i}"
    and scheduled:
      "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> affects_recovery (accounting j)) \<Longrightarrow>
        pending_ids (source_state (events i)) \<noteq> {} \<Longrightarrow>
        \<exists>j\<ge>i. product_repair_command_enabled
          (publication_matches_current_state (authorities_at j) (sources j) (heads j) (offers j) (source_state (events j)))
          (selected_asset (sources j) (heads j) (offers j) (source_state (events j)) =
             Some (registered_asset (current_operational (authorities_at j))))
          (\<exists>authority receipt. select_current_publication (sources j) (heads j) (offers j) (route_epoch (source_state (events j))) =
            Some (authority,receipt) \<and> primary_receipt_matches authority receipt (source_state (events j)))
          (source_state (events j))
          (\<lambda>approval job seq. resync_permitted administrators approvals (registered_asset (current_operational (authorities_at j)))
             (source_state (events j)) approval job seq)
          (step_action (events j))"
  shows "\<exists>n. \<forall>i\<ge>n.
    pending_ids (source_state (events i)) = {} \<and>
    (\<forall>d\<in>active_domains (source_state (events i)).
      replica (source_state (events i)) d = primary_record (source_state (events i))) \<and>
    (\<forall>j\<le>i. pending_ids (source_state (events j)) \<union> completion_log (source_state (events j))
      \<subseteq> completion_log (source_state (events i)))"
proof -
  have native_step: "step_occurs (recovery_step grants (image approval_id approvals)) (accounting i)" for i
  proof -
    have step: "step_occurs (product_recovery_step (authorities_at i) administrators approvals
       (sources i) (heads i) (offers i) grants) (events i)" using run[of i] by blast
    note projection = product_accounting_is_valid_at_the_actual_scope[OF step]
    have preserved: "accounting_event (accounting i) = accounting i"
      by (simp add: accounting_def accounting_event_def product_accounting_event_def mk_event_def split: if_splits)
    from offered_events_project_to_native_work_accounting[OF projection] preserved show ?thesis
      by (simp only: accounting_def)
  qed
  have native_run: "infinite_run (recovery_step grants (image approval_id approvals)) initial recovery_carrier accounting"
    using start run native_step by (auto simp: infinite_run_def accounting_def)
  have sub: "{i. affects_recovery (accounting i)} \<subseteq> {i. recovery_interference heads accounting i}"
    by (auto simp: recovery_interference_def)
  have finite_work: "finite {i. affects_recovery (accounting i)}" by (rule finite_subset[OF sub finite])
  have makes_progress:
      "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> affects_recovery (accounting j)) \<Longrightarrow>
       pending_ids (source_state (accounting i)) \<noteq> {} \<Longrightarrow>
       \<exists>j\<ge>i. \<exists>job d seq. step_outcome (accounting j) = transition_result.Accepted (Installed job d seq)"
  proof -
    fix i assume quiet: "\<And>j. i \<le> j \<Longrightarrow> \<not> affects_recovery (accounting j)"
      and pending: "pending_ids (source_state (accounting i)) \<noteq> {}"
    have outstanding: "pending_ids (source_state (events i)) \<noteq> {}" using pending by (simp add: accounting_def)
    obtain j where later: "i \<le> j" and ready:
      "product_repair_command_enabled
          (publication_matches_current_state (authorities_at j) (sources j) (heads j) (offers j) (source_state (events j)))
          (selected_asset (sources j) (heads j) (offers j) (source_state (events j)) =
             Some (registered_asset (current_operational (authorities_at j))))
          (\<exists>authority receipt. select_current_publication (sources j) (heads j) (offers j) (route_epoch (source_state (events j))) =
            Some (authority,receipt) \<and> primary_receipt_matches authority receipt (source_state (events j)))
          (source_state (events j))
          (\<lambda>approval job seq. resync_permitted administrators approvals (registered_asset (current_operational (authorities_at j)))
             (source_state (events j)) approval job seq)
          (step_action (events j))"
      using scheduled[OF quiet outstanding] by blast
    have executed: "step_occurs (product_recovery_step (authorities_at j) administrators approvals
      (sources j) (heads j) (offers j) grants) (events j)"
      using run[of j] by blast
    have occurs: "product_recovery_step (authorities_at j) administrators approvals (sources j) (heads j) (offers j) grants
      (source_state (events j)) (step_action (events j)) (step_outcome (events j)) (target_state (events j))"
      using executed by (simp only: step_occurs_def)
    obtain job d seq where installed: "step_outcome (events j) = transition_result.Accepted (Installed job d seq)"
      using a_ready_product_repair_uses_actual_permission_and_finishes[OF ready occurs] by blast
    have fired: "step_outcome (accounting j) = transition_result.Accepted (Installed job d seq)"
      using installed by (simp add: accounting_def product_accounting_event_def mk_event_def)
    show "\<exists>j\<ge>i. \<exists>job d seq. step_outcome (accounting j) = transition_result.Accepted (Installed job d seq)"
      using later fired by blast
  qed
  show ?thesis using recovery_finishes_under_finite_interference[OF native_run finite_work makes_progress]
    by (simp add: accounting_def)
qed

end

end
