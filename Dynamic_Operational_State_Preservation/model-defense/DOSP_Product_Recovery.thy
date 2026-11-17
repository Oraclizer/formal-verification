theory DOSP_Product_Recovery
  imports DOSP_Scoped_Recovery
begin

datatype product_recovery_command =
    Activate_Route "nat route_change" nat nat
  | Register_Divergence nat nat nat
  | Repair_Replica nat nat
  | Resolve_Rollback resync_approval nat nat
  | Trade_After_Recovery nat
  | Await_Recovery_Evidence

fun route_change_is_applicable where
  "route_change_is_applicable s (Join_Domain domain job) = (domain \<notin> active_domains s \<and> fresh_work s job)"
| "route_change_is_applicable s (Leave_Domain old successor) =
    (old \<in> active_domains s \<and> successor \<in> active_domains s \<and> old \<noteq> successor)"

definition earlier_route_update_is_pending where
  "earlier_route_update_is_pending s grants epoch \<longleftrightarrow>
    (\<exists>change prior boundary. (change,prior,boundary) \<in> grants \<and>
      route_epoch s < prior \<and> prior < epoch)"

definition route_grant_matches_its_epoch where
  "route_grant_matches_its_epoch grants change epoch boundary \<longleftrightarrow>
    (\<forall>other second. (other,epoch,second) \<in> grants \<longrightarrow> other = change \<and> second = boundary)"

definition outstanding_join_jobs :: "nat recovery_state \<Rightarrow> nat routing_grants \<Rightarrow> nat set" where
  "outstanding_join_jobs s grants =
    {job. \<exists>domain epoch boundary. (Join_Domain domain job,epoch,boundary) \<in> grants \<and> route_epoch s < epoch}"

lemma outstanding_join_jobs_empty [simp]:
  "outstanding_join_jobs s {} = {}"
  by (simp add: outstanding_join_jobs_def)

lemma a_pending_join_reserves_its_recovery_job:
  assumes "(Join_Domain domain job,epoch,boundary) \<in> grants" "route_epoch s < epoch"
  shows "job \<in> outstanding_join_jobs s grants"
  using assms unfolding outstanding_join_jobs_def by blast

definition recovery_job_for_observation where
  "recovery_job_for_observation s grants requested =
    (let reserved = outstanding_join_jobs s grants; usable = (\<lambda>job. fresh_work s job \<and> job \<notin> reserved)
     in if requested \<in> reserved then (if (\<exists>job. usable job) then Some (LEAST job. usable job) else None)
        else Some requested)"

lemma an_unreserved_observation_keeps_its_job_id [simp]:
  "requested \<notin> outstanding_join_jobs s grants \<Longrightarrow>
    recovery_job_for_observation s grants requested = Some requested"
  by (simp add: recovery_job_for_observation_def Let_def)

lemma a_selected_observation_job_is_never_reserved:
  assumes chosen: "recovery_job_for_observation s grants requested = Some job"
  shows "job \<notin> outstanding_join_jobs s grants"
proof (cases "requested \<in> outstanding_join_jobs s grants")
  case True
  let ?usable = "\<lambda>job. fresh_work s job \<and> job \<notin> outstanding_join_jobs s grants"
  have exists: "\<exists>job. ?usable job"
    using True chosen by (auto simp: recovery_job_for_observation_def Let_def split: if_splits)
  have selected: "job = (LEAST job. ?usable job)"
    using True chosen exists by (simp add: recovery_job_for_observation_def Let_def)
  have unreserved: "(LEAST job. ?usable job) \<notin> outstanding_join_jobs s grants"
    using LeastI_ex[OF exists] by blast
  show ?thesis unfolding selected by (rule unreserved)
next
  case False
  have "recovery_job_for_observation s grants requested = Some requested"
    by (rule an_unreserved_observation_keeps_its_job_id[OF False])
  then have "job = requested" using chosen by simp
  then show ?thesis using False by blast
qed

lemma an_observation_can_replace_a_reserved_id_when_used_ids_are_finite:
  assumes reserved: "requested \<in> outstanding_join_jobs s grants"
    and finite: "finite (pending_ids s)" "finite (completion_log s)" "finite (outstanding_join_jobs s grants)"
  shows "\<exists>job. recovery_job_for_observation s grants requested = Some job \<and> fresh_work s job \<and>
    job \<notin> outstanding_join_jobs s grants"
proof -
  let ?used = "pending_ids s \<union> completion_log s \<union> outstanding_join_jobs s grants"
  have "finite ?used" using finite by simp
  then obtain limit where upper: "\<forall>i\<in>?used. i < limit"
    unfolding finite_nat_set_iff_bounded by blast
  have outside: "limit \<notin> ?used" using upper by auto
  let ?usable = "\<lambda>job. fresh_work s job \<and> job \<notin> outstanding_join_jobs s grants"
  have valid: "?usable limit" using outside by (auto simp: fresh_work_def pending_ids_def domIff)
  have can: "\<exists>job. ?usable job" using valid by blast
  have selected: "recovery_job_for_observation s grants requested = Some (LEAST job. ?usable job)"
    using reserved can by (simp add: recovery_job_for_observation_def Let_def)
  show ?thesis
  proof (rule exI[of _ "LEAST job. ?usable job"])
    show "recovery_job_for_observation s grants requested = Some (LEAST job. ?usable job) \<and>
      fresh_work s (LEAST job. ?usable job) \<and> (LEAST job. ?usable job) \<notin> outstanding_join_jobs s grants"
      using selected LeastI_ex[OF can] by blast
  qed
qed

fun product_native_repair where
  "product_native_repair a grants s (Activate_Route change epoch boundary) = Activate change epoch boundary (consensus_now a)"
| "product_native_repair a grants s (Register_Divergence job domain observed) =
    (case recovery_job_for_observation s grants job of None \<Rightarrow> Wait_For_Source
     | Some assigned \<Rightarrow> Notice_Divergence assigned domain observed)"
| "product_native_repair a grants s (Repair_Replica job seq) = Apply_Repair job seq"
| "product_native_repair a grants s (Resolve_Rollback approval job seq) = Governance_Resync (approval_id approval) job seq"
| "product_native_repair a grants s (Trade_After_Recovery tx) = Ordinary_Trade tx"
| "product_native_repair a grants s Await_Recovery_Evidence = Wait_For_Source"

type_synonym scheduled_routing_change = "nat route_change \<times> nat \<times> nat"

definition outstanding_routing_grants where
  "outstanding_routing_grants s grants = {entry \<in> grants. route_epoch s < fst (snd entry)}"

fun routing_updates_are_executable ::
  "nat routing_grants \<Rightarrow> nat recovery_state \<Rightarrow> scheduled_routing_change list \<Rightarrow> bool" where
  "routing_updates_are_executable grants s [] = True"
| "routing_updates_are_executable grants s ((change,epoch,boundary) # rest) =
    (\<exists>updated outcome. recovery_step grants {} s (Activate change epoch boundary boundary)
      (transition_result.Accepted outcome) updated \<and> routing_updates_are_executable grants updated rest)"

lemma an_executable_routing_plan_has_an_applicable_first_update:
  assumes "routing_updates_are_executable grants s ((change,epoch,boundary) # rest)"
  shows "\<exists>updated outcome. recovery_step grants {} s (Activate change epoch boundary boundary)
    (transition_result.Accepted outcome) updated \<and> routing_updates_are_executable grants updated rest"
  using assms by simp

definition valid_routing_approval_plan where
  "valid_routing_approval_plan s proposed plan \<longleftrightarrow>
    set plan = outstanding_routing_grants s proposed \<and>
    sorted_wrt (\<lambda>(_,epoch,second) (_,later,later_second). epoch < later \<and> second \<le> later_second) plan \<and>
    routing_updates_are_executable proposed s plan"

lemma an_approved_plan_reserves_only_finitely_many_job_ids:
  assumes "valid_routing_approval_plan s grants plan"
  shows "finite (outstanding_join_jobs s grants)"
proof -
  let ?job = "\<lambda>(change,epoch,boundary). case change of Join_Domain domain job \<Rightarrow> Some job | _ \<Rightarrow> None"
  have finite: "finite (vimage Some (image ?job (set plan)))"
    by (rule finite_vimageI) (simp_all add: inj_on_def)
  have subset: "outstanding_join_jobs s grants \<subseteq> vimage Some (image ?job (set plan))"
  proof
    fix job assume "job \<in> outstanding_join_jobs s grants"
    then obtain d epoch boundary where pending: "(Join_Domain d job,epoch,boundary) \<in> grants" "route_epoch s < epoch"
      unfolding outstanding_join_jobs_def by blast
    have "(Join_Domain d job,epoch,boundary) \<in> set plan"
      using pending assms by (auto simp: valid_routing_approval_plan_def outstanding_routing_grants_def)
    then have "?job (Join_Domain d job,epoch,boundary) \<in> image ?job (set plan)"
      by (rule imageI)
    then show "job \<in> vimage Some (image ?job (set plan))" by simp
  qed
  show ?thesis by (rule finite_subset[OF subset finite])
qed

datatype routing_approval_status = Routing_Approvals_Accepted | Routing_Approvals_Conflict

definition new_routing_grants_are_prospective where
  "new_routing_grants_are_prospective (root_time::nat) current proposed \<longleftrightarrow>
    (\<forall>entry\<in>proposed - current. root_time < snd (snd entry))"

definition review_routing_approvals where
  "review_routing_approvals s root_time current proposed plan =
    (if outstanding_routing_grants s current \<subseteq> proposed \<and> valid_routing_approval_plan s proposed plan \<and>
       new_routing_grants_are_prospective root_time current proposed
     then (proposed,Routing_Approvals_Accepted) else (current,Routing_Approvals_Conflict))"

lemma an_accepted_approval_checks_the_whole_order_and_keeps_outstanding_grants:
  assumes "review_routing_approvals s root_time current proposed plan = (grants,Routing_Approvals_Accepted)"
  shows "grants = proposed \<and> outstanding_routing_grants s current \<subseteq> grants \<and>
    valid_routing_approval_plan s grants plan \<and> new_routing_grants_are_prospective root_time current grants"
  using assms by (auto simp: review_routing_approvals_def split: if_splits)

lemma a_conflicting_route_plan_is_refused_and_keeps_the_previous_approvals:
  assumes "\<not> valid_routing_approval_plan s proposed plan"
  shows "review_routing_approvals s root_time current proposed plan = (current,Routing_Approvals_Conflict)"
  using assms by (simp add: review_routing_approvals_def)

definition replica_cell where
  "replica_cell s d = (if d \<in> active_domains s then Some (replica s d) else None)"

definition requested_repair_can_run ::
  "nat recovery_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "requested_repair_can_run s job seq \<longleftrightarrow>
    (\<exists>d. work_owner s job = Some d \<and> d \<in> active_domains s) \<and>
    source_ready s \<and> seq = primary_sequence s"

definition product_repair_command_enabled ::
  "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat recovery_state \<Rightarrow>
    (resync_approval \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> product_recovery_command \<Rightarrow> bool"
where
  "product_repair_command_enabled current right_asset valid_replay s approved command \<longleftrightarrow>
    current \<and> right_asset \<and> valid_replay \<and> (case command of
       Repair_Replica job seq \<Rightarrow> requested_repair_can_run s job seq \<and> \<not> rollback_incomplete s
     | Resolve_Rollback approval job seq \<Rightarrow>
         approved approval job seq \<and> requested_repair_can_run s job seq \<and> rollback_incomplete s
     | _ \<Rightarrow> False)"

context integrated_dosp_authority
begin

definition publication_matches_current_state where
  "publication_matches_current_state a sources head offers s \<longleftrightarrow>
    (\<exists>authority receipt. select_current_publication sources head offers (route_epoch s) = Some (authority,receipt) \<and>
      issued_receipt a (head_sequence head) = Some receipt \<and>
      Suc (head_sequence head) = next_publication_sequence a)"

definition product_recovery_step where
  "product_recovery_step a authorities confirmed sources head offers grants s command reply t \<longleftrightarrow>
    (case command of
       Activate_Route change epoch boundary \<Rightarrow>
         (if route_change_is_applicable s change \<and> \<not> earlier_route_update_is_pending s grants epoch \<and>
             route_grant_matches_its_epoch grants change epoch boundary
          then consensus_membership_step a sources head offers grants s change epoch boundary reply t
          else reply = transition_result.Rejected Stale_Route \<and> t = s)
     | Register_Divergence job domain observed \<Rightarrow>
         (case recovery_job_for_observation s grants job of
           None \<Rightarrow> reply = transition_result.Operational_Failure Evidence_Unavailable \<and> t = s
         | Some assigned \<Rightarrow> offered_recovery_step sources head offers grants {} s (Notice_Divergence assigned domain observed) reply t)
     | Repair_Replica job sequence \<Rightarrow>
         (if selected_asset sources head offers s = Some (registered_asset (current_operational a)) \<and>
             publication_matches_current_state a sources head offers s \<and>
             requested_repair_can_run s job sequence \<and> \<not> rollback_incomplete s
          then offered_recovery_step sources head offers grants {} s (Apply_Repair job sequence) reply t
          else reply = transition_result.Operational_Failure Evidence_Unavailable \<and> t = s)
     | Resolve_Rollback approval job sequence \<Rightarrow>
         (if \<not> resync_permitted authorities confirmed (registered_asset (current_operational a)) s approval job sequence \<or>
             (publication_matches_current_state a sources head offers s \<and>
               requested_repair_can_run s job sequence \<and> rollback_incomplete s)
          then scoped_resync authorities confirmed (registered_asset (current_operational a)) sources head offers grants s approval job sequence reply t
          else reply = transition_result.Operational_Failure Evidence_Unavailable \<and> t = s)
     | Trade_After_Recovery tx \<Rightarrow> offered_recovery_step sources head offers grants {} s (Ordinary_Trade tx) reply t
     | Await_Recovery_Evidence \<Rightarrow> offered_recovery_step sources head offers grants {} s Wait_For_Source reply t)"

lemma product_rollback_uses_the_registry_asset_and_the_issued_receipt:
  assumes step: "product_recovery_step a authorities confirmed sources head offers grants s
    (Resolve_Rollback approval job sequence) (transition_result.Accepted (Installed job d sequence)) t"
  shows "resync_permitted authorities confirmed (registered_asset (current_operational a)) s approval job sequence \<and>
    selected_asset sources head offers s = Some (registered_asset (current_operational a)) \<and>
    publication_matches_current_state a sources head offers s \<and>
    irreversible_facts t = irreversible_facts s"
proof -
  have exact: "scoped_resync authorities confirmed (registered_asset (current_operational a)) sources head offers grants s
      approval job sequence (transition_result.Accepted (Installed job d sequence)) t"
    using step by (auto simp: product_recovery_step_def split: if_splits)
  show ?thesis using accepted_governance_requires_the_exact_scope_and_preserves_irreversibility[OF exact] step
    by (auto simp: product_recovery_step_def split: if_splits)
qed

lemma product_repair_cannot_install_a_receipt_missing_from_current_consensus:
  assumes absent: "issued_receipt a (head_sequence head) = None"
  shows "product_recovery_step a authorities confirmed sources head offers grants s (Repair_Replica job sequence)
    (transition_result.Operational_Failure Evidence_Unavailable) s"
  using absent by (simp add: product_recovery_step_def publication_matches_current_state_def)

lemma an_older_issued_publication_cannot_become_the_current_product_repair:
  assumes older: "Suc (head_sequence head) \<noteq> next_publication_sequence a"
  shows "product_recovery_step a authorities confirmed sources head offers grants s (Repair_Replica job sequence)
    (transition_result.Operational_Failure Evidence_Unavailable) s"
  using older by (simp add: product_recovery_step_def publication_matches_current_state_def)

lemma product_recovery_rejects_a_duplicate_join_and_a_completed_install:
  "domain \<in> active_domains s \<Longrightarrow>
    product_recovery_step a authorities confirmed sources head offers grants s (Activate_Route (Join_Domain domain job) epoch boundary)
      (transition_result.Rejected Stale_Route) s"
  "work_owner s job = None \<Longrightarrow>
    product_recovery_step a authorities confirmed sources head offers grants s (Repair_Replica job seq)
      (transition_result.Operational_Failure Evidence_Unavailable) s"
  by (simp_all add: product_recovery_step_def requested_repair_can_run_def)

lemma an_authorized_governance_retry_with_no_pending_job_returns_refusal:
  assumes "resync_permitted authorities confirmed (registered_asset (current_operational a)) s approval job sequence"
    "work_owner s job = None"
  shows "product_recovery_step a authorities confirmed sources head offers grants s (Resolve_Rollback approval job sequence)
    (transition_result.Operational_Failure Evidence_Unavailable) s"
  using assms by (simp add: product_recovery_step_def requested_repair_can_run_def)

lemma a_later_activation_cannot_skip_an_outstanding_authorized_epoch:
  assumes "earlier_route_update_is_pending s grants epoch"
  shows "product_recovery_step a authorities confirmed sources head offers grants s (Activate_Route change epoch boundary) reply t
    \<longleftrightarrow> reply = transition_result.Rejected Stale_Route \<and> t = s"
  using assms by (simp add: product_recovery_step_def)

lemma observing_divergence_cannot_consume_an_outstanding_join_job:
  assumes "product_recovery_step a authorities confirmed sources head offers grants s
    (Register_Divergence requested domain observed) (transition_result.Accepted (Opened job)) t"
  shows "job \<notin> outstanding_join_jobs s grants"
proof -
  obtain assigned where picked: "recovery_job_for_observation s grants requested = Some assigned"
    and opened: "recovery_step grants {} s (Notice_Divergence assigned domain observed) (transition_result.Accepted (Opened job)) t"
    using assms by (auto simp: product_recovery_step_def offered_recovery_step_def split: option.splits)
  have "job = assigned" using opened by (cases rule: recovery_step.cases) auto
  then show ?thesis using a_selected_observation_job_is_never_reserved[OF picked] by simp
qed

lemma conflicting_grants_cannot_both_supply_one_routing_epoch:
  assumes "(other,epoch,second) \<in> grants" "other \<noteq> change \<or> second \<noteq> boundary"
  shows "product_recovery_step a authorities confirmed sources head offers grants s (Activate_Route change epoch boundary) reply t
    \<longleftrightarrow> reply = transition_result.Rejected Stale_Route \<and> t = s"
proof -
  have "\<not> route_grant_matches_its_epoch grants change epoch boundary"
    using assms unfolding route_grant_matches_its_epoch_def by blast
  then show ?thesis by (simp add: product_recovery_step_def)
qed

lemma joining_initializes_the_new_cell_and_frames_existing_replica_and_work:
  assumes step: "product_recovery_step a authorities confirmed sources head offers grants s
    (Activate_Route (Join_Domain d job) epoch boundary) (transition_result.Accepted (Joined d job)) t"
  shows "replica_cell s d = None \<and> replica_cell t d = Some (replica s d) \<and>
    (\<forall>x. x \<noteq> d \<longrightarrow> replica_cell t x = replica_cell s x) \<and>
    replica t = replica s \<and> work_owner t job = Some d \<and>
    (\<forall>i. i \<noteq> job \<longrightarrow> work_owner t i = work_owner s i) \<and>
    irreversible_facts t = irreversible_facts s"
proof -
  have actual: "recovery_step grants {} s (Activate (Join_Domain d job) epoch boundary (consensus_now a))
    (transition_result.Accepted (Joined d job)) t"
    using step by (auto simp: product_recovery_step_def consensus_membership_step_def
      activation_uses_the_existing_grant_and_handoff split: if_splits)
  from actual show ?thesis by (cases rule: recovery_step.cases) (auto simp: replica_cell_def)
qed

lemma a_ready_product_repair_uses_actual_permission_and_finishes:
  assumes ready: "product_repair_command_enabled
      (publication_matches_current_state a sources head offers s)
      (selected_asset sources head offers s = Some (registered_asset (current_operational a)))
      (\<exists>authority receipt. select_current_publication sources head offers (route_epoch s) = Some (authority,receipt) \<and>
        primary_receipt_matches authority receipt s) s
      (\<lambda>approval job seq. resync_permitted authorities confirmed (registered_asset (current_operational a)) s approval job seq) command"
    and occurs: "product_recovery_step a authorities confirmed sources head offers grants s command result t"
  shows "\<exists>i d seq. result = transition_result.Accepted (Installed i d seq)"
proof -
  have current: "publication_matches_current_state a sources head offers s"
    using ready by (simp add: product_repair_command_enabled_def)
  have right: "selected_asset sources head offers s = Some (registered_asset (current_operational a))"
    using ready by (simp add: product_repair_command_enabled_def)
  obtain authority receipt where selected: "select_current_publication sources head offers (route_epoch s) = Some (authority,receipt)"
    and matches: "primary_receipt_matches authority receipt s"
    using ready by (auto simp: product_repair_command_enabled_def)
  show ?thesis
  proof (cases command)
    case (Repair_Replica job seq)
    have available: "requested_repair_can_run s job seq \<and> \<not> rollback_incomplete s"
      using ready by (auto simp: product_repair_command_enabled_def Repair_Replica)
    have actual: "recovery_step grants {} s (Apply_Repair job seq) result t"
      using occurs Repair_Replica current right selected matches available
      by (simp add: product_recovery_step_def offered_recovery_step_def receipt_repair_step_def)
    from actual show ?thesis by (cases rule: recovery_step.cases) auto
  next
    case (Resolve_Rollback approval job seq)
    have permit: "resync_permitted authorities confirmed (registered_asset (current_operational a)) s approval job seq"
      using ready by (auto simp: product_repair_command_enabled_def Resolve_Rollback)
    have rollback: "rollback_incomplete s" using ready by (auto simp: product_repair_command_enabled_def Resolve_Rollback)
    have available: "requested_repair_can_run s job seq"
      using ready by (auto simp: product_repair_command_enabled_def Resolve_Rollback)
    obtain d where owner: "work_owner s job = Some d" "d \<in> active_domains s"
      using available by (auto simp: requested_repair_can_run_def)
    have flags: "source_ready s" "seq = primary_sequence s" using available by (simp_all add: requested_repair_can_run_def)
    have identity: "approval_id approval \<in> {approval_id approval}" by simp
    have exists: "\<exists>outcome updated. offered_recovery_step sources head offers grants {approval_id approval}
       s (Governance_Resync (approval_id approval) job seq) outcome updated"
      using prepared_governance_repair_uses_the_verified_record[OF selected matches owner flags(1) rollback identity,
        where grants=grants] flags(2) by blast
    have actual: "recovery_step grants {approval_id approval} s (Governance_Resync (approval_id approval) job seq) result t"
      using occurs permit current right exists selected matches available rollback Resolve_Rollback
      by (simp add: product_recovery_step_def scoped_resync_def offered_recovery_step_def receipt_repair_step_def Let_def)
    from actual show ?thesis by (cases rule: recovery_step.cases) auto
  qed (use ready in \<open>simp_all add: product_repair_command_enabled_def\<close>)
qed

end

lemma correct_resolution_respects_the_same_registry_after_membership_handoff:
  "joined_dosp.product_recovery_step actual_authority {71} {resolution_for_job_eight} two_journals current_repair_head
    [prior_offer,live_offer] joined_recovery_grants flagged_handoff (Resolve_Rollback resolution_for_job_eight 8 51)
    (transition_result.Accepted (Installed 8 6 51)) (after_job_eight\<lparr>rollback_incomplete := True\<rparr>)"
  "joined_dosp.product_recovery_step actual_authority {71} {wrong_asset_approval} two_journals current_repair_head
    [live_offer] joined_recovery_grants flagged_handoff (Resolve_Rollback wrong_asset_approval 8 51)
    (transition_result.Rejected Recovery_Blocks_Trade) flagged_handoff"
proof -
  have asset: "registered_asset (current_operational actual_authority) = 17"
    by (simp add: joined_authority_normal_form second_metered_operational_def second_meter_operational_fields(2))
  have seq: "head_sequence current_repair_head = 51" by (simp add: current_repair_head_def)
  have current: "joined_dosp.publication_matches_current_state actual_authority two_journals current_repair_head
      [prior_offer,live_offer] flagged_handoff"
    by (simp add: joined_dosp.publication_matches_current_state_def actual_publication_fields(2) seq
      handoff_has_a_real_primary_and_current_epoch(1)
      current_source_chosen_from_two_actual_histories(1)
      the_same_asset_was_metered_and_published_on_both_sides_of_promotion(5))
  have ready: "requested_repair_can_run flagged_handoff 8 51"
    by (simp add: requested_repair_can_run_def handed_off_recovery_def joined_recovery_def noticed_recovery_def
      published_recovery_state_def carry_owner_def actual_publication_fields issued_second_receipt_def Let_def)
  show "joined_dosp.product_recovery_step actual_authority {71} {resolution_for_job_eight} two_journals current_repair_head
    [prior_offer,live_offer] joined_recovery_grants flagged_handoff (Resolve_Rollback resolution_for_job_eight 8 51)
    (transition_result.Accepted (Installed 8 6 51)) (after_job_eight\<lparr>rollback_incomplete := True\<rparr>)"
    by (simp add: joined_dosp.product_recovery_step_def asset current ready
      exact_governance_can_resync_the_same_pending_job_and_leaves_the_other_pending)
  show "joined_dosp.product_recovery_step actual_authority {71} {wrong_asset_approval} two_journals current_repair_head
    [live_offer] joined_recovery_grants flagged_handoff (Resolve_Rollback wrong_asset_approval 8 51)
    (transition_result.Rejected Recovery_Blocks_Trade) flagged_handoff"
    by (simp add: joined_dosp.product_recovery_step_def joined_dosp.scoped_resync_def asset resync_permitted_def
      resolution_for_job_eight_def)
qed

lemma a_retained_old_receipt_is_not_used_after_the_next_actual_publication:
  "issued_receipt actual_authority 50 = Some fixture_receipt"
  "joined_dosp.product_recovery_step actual_authority {} {} two_journals
     (current_repair_head\<lparr>head_issuer := 41, head_sequence := 50, head_key := (0,17)\<rparr>)
     [prior_offer,live_offer] joined_recovery_grants handed_off_recovery (Repair_Replica 8 50)
     (transition_result.Operational_Failure Evidence_Unavailable) handed_off_recovery"
  by (rule actual_publication_fields(1) joined_dosp.an_older_issued_publication_cannot_become_the_current_product_repair |
    simp add: the_same_asset_was_metered_and_published_on_both_sides_of_promotion(5))+

end
