theory DOSP_Route_And_Recovery_Cases
  imports DOSP_Pending_Renewal_Cases DOSP_Retained_Settlement_Cases DOSP_Same_Sequence_Cases
begin

abbreviation before_the_first_credit where
  "before_the_first_credit \<equiv> early_product finality_sample_initial Idle_Cycle early_recovery"

abbreviation ordered_leave_grants where
  "ordered_leave_grants \<equiv> {(Leave_Domain (0::nat) 4,2,86398), (Leave_Domain 4 2,3,86399)}"

theorem a_routing_approval_rejects_a_successor_removed_by_an_earlier_approved_leave:
  fixes prior proposed :: "nat routing_grants"
  defines "prior \<equiv> {(Leave_Domain 0 4,2,86398)}"
    and "proposed \<equiv> prior \<union> {(Leave_Domain 2 0,3,86399), (Join_Domain 6 99,4,86399)}"
  shows "review_routing_approvals early_recovery 86397 {} prior [(Leave_Domain 0 4,2,86398)] =
      (prior,Routing_Approvals_Accepted)"
    "review_routing_approvals early_recovery 86397 prior proposed
      [(Leave_Domain 0 4,2,86398),(Leave_Domain 2 0,3,86399),(Join_Domain 6 99,4,86399)] =
      (prior,Routing_Approvals_Conflict)"
    "review_routing_approvals early_recovery 86399 {} prior [(Leave_Domain 0 4,2,86398)] =
      ({},Routing_Approvals_Conflict)"
proof -
  have empty: "carry_owner (0::nat) 4 Map.empty = Map.empty"
    by (rule ext) (simp add: carry_owner_def)
  have first: "recovery_step prior {} early_recovery (Activate (Leave_Domain 0 4) 2 86398 86398)
    (transition_result.Accepted (Left 0 4)) early_retired"
    using recovery_step.Leave_Route[where s=early_recovery and old=0 and successor=4 and epoch=2 and boundary=86398
      and root_time=86398 and grants=prior and governance="{}"]
    by (simp add: current_grant_def prior_def empty)
  have valid: "valid_routing_approval_plan early_recovery prior [(Leave_Domain 0 4,2,86398)]"
    unfolding valid_routing_approval_plan_def
    using first by (auto simp: prior_def outstanding_routing_grants_def intro!: exI[of _ early_retired] exI[of _ "Left 0 4"])
  show "review_routing_approvals early_recovery 86397 {} prior [(Leave_Domain 0 4,2,86398)] =
      (prior,Routing_Approvals_Accepted)"
    using valid by (simp add: review_routing_approvals_def outstanding_routing_grants_def
      new_routing_grants_are_prospective_def prior_def)
  let ?later = "[(Leave_Domain (2::nat) 0,3,86399),(Join_Domain 6 99,4,86399)]"
  have conflict: "\<not> routing_updates_are_executable proposed early_recovery ((Leave_Domain 0 4,2,86398) # ?later)"
  proof
    assume executable: "routing_updates_are_executable proposed early_recovery ((Leave_Domain 0 4,2,86398) # ?later)"
    from an_executable_routing_plan_has_an_applicable_first_update[OF executable] obtain mid outcome where first_actual:
      "recovery_step proposed {} early_recovery (Activate (Leave_Domain 0 4) 2 86398 86398)
        (transition_result.Accepted outcome) mid"
      and later: "routing_updates_are_executable proposed mid ?later"
      by blast
    have exited: "0 \<notin> active_domains mid"
      using first_actual by (cases rule: recovery_step.cases) auto
    from an_executable_routing_plan_has_an_applicable_first_update[OF later] obtain after outcome where invalid:
      "recovery_step proposed {} mid (Activate (Leave_Domain 2 0) 3 86399 86399)
        (transition_result.Accepted outcome) after" by blast
    from invalid exited show False by (cases rule: recovery_step.cases) auto
  qed
  show "review_routing_approvals early_recovery 86397 prior proposed
      [(Leave_Domain 0 4,2,86398),(Leave_Domain 2 0,3,86399),(Join_Domain 6 99,4,86399)] =
      (prior,Routing_Approvals_Conflict)"
    by (rule a_conflicting_route_plan_is_refused_and_keeps_the_previous_approvals)
      (use conflict in \<open>auto simp: valid_routing_approval_plan_def\<close>)
  show "review_routing_approvals early_recovery 86399 {} prior [(Leave_Domain 0 4,2,86398)] =
      ({},Routing_Approvals_Conflict)"
    by (simp add: review_routing_approvals_def new_routing_grants_are_prospective_def prior_def)
qed

theorem two_due_leaves_apply_in_epoch_order_and_then_refuse_the_old_origin:
  fixes q t :: product_source_state
  defines "q \<equiv> before_the_first_credit\<lparr>source_recovery := early_retired\<rparr>"
    and "t \<equiv> q\<lparr>source_recovery := early_retired\<lparr>active_domains := {2}, route_epoch := 3\<rparr>\<rparr>"
  shows "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    ordered_leave_grants before_the_first_credit (Update_Recovery (Activate_Route (Leave_Domain 4 2) 3 86399))
    (Recovery_Outcome (transition_result.Rejected Stale_Route)) before_the_first_credit"
  "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    ordered_leave_grants before_the_first_credit (Update_Recovery (Activate_Route (Leave_Domain 0 4) 2 86398))
    (Recovery_Outcome (transition_result.Accepted (Left 0 4))) q"
  "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    ordered_leave_grants q (Update_Recovery (Activate_Route (Leave_Domain 4 2) 3 86399))
    (Recovery_Outcome (transition_result.Accepted (Left 4 2))) t"
  "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    ordered_leave_grants t (Prepare_Native early_reserve) (Binding_Outcome Precommit_Refused) t"
proof -
  have earlier: "earlier_route_update_is_pending early_recovery ordered_leave_grants 3"
    unfolding earlier_route_update_is_pending_def
    by (intro exI[of _ "Leave_Domain 0 4"] exI[of _ 2] exI[of _ 86398]) simp
  have denied_later: "joined_dosp.product_recovery_step (source_consensus before_the_first_credit)
      {} {} two_journals current_repair_head [] ordered_leave_grants early_recovery
      (Activate_Route (Leave_Domain 4 2) 3 86399) (transition_result.Rejected Stale_Route) early_recovery"
    by (rule joined_dosp.a_later_activation_cannot_skip_an_outstanding_authorized_epoch[OF earlier, THEN iffD2]) simp
  show "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    ordered_leave_grants before_the_first_credit (Update_Recovery (Activate_Route (Leave_Domain 4 2) 3 86399))
    (Recovery_Outcome (transition_result.Rejected Stale_Route)) before_the_first_credit"
    using denied_later unfolding joined_dosp.product_source_step_def by (auto simp: Let_def)
  have empty: "carry_owner retiring successor Map.empty = Map.empty" for retiring successor :: nat
    by (rule ext) (simp add: carry_owner_def)
  have first: "recovery_step ordered_leave_grants {} early_recovery (Activate (Leave_Domain 0 4) 2 86398 86399)
    (transition_result.Accepted (Left 0 4)) early_retired"
    using recovery_step.Leave_Route[where s=early_recovery and old=0 and successor=4 and epoch=2 and boundary=86398
      and root_time=86399 and grants=ordered_leave_grants and governance="{}"]
    by (simp add: current_grant_def empty)
  show "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    ordered_leave_grants before_the_first_credit (Update_Recovery (Activate_Route (Leave_Domain 0 4) 2 86398))
    (Recovery_Outcome (transition_result.Accepted (Left 0 4))) q"
    unfolding q_def using first
    by (auto simp: joined_dosp.product_source_step_def joined_dosp.product_recovery_step_def
      joined_dosp.consensus_membership_step_def joined_dosp.activation_uses_the_existing_grant_and_handoff
      earlier_route_update_is_pending_def route_grant_matches_its_epoch_def
      with_finality_core_def with_operational_state_def joined_initial_def Let_def)
  have remaining: "{(2::nat),4} - {4} = {2}" by auto
  have second: "recovery_step ordered_leave_grants {} early_retired (Activate (Leave_Domain 4 2) 3 86399 86399)
    (transition_result.Accepted (Left 4 2)) (early_retired\<lparr>active_domains := {2}, route_epoch := 3\<rparr>)"
    using recovery_step.Leave_Route[where s=early_retired and old=4 and successor=2 and epoch=3 and boundary=86399
      and root_time=86399 and grants=ordered_leave_grants and governance="{}"]
    by (simp add: current_grant_def empty remaining)
  show "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    ordered_leave_grants q (Update_Recovery (Activate_Route (Leave_Domain 4 2) 3 86399))
    (Recovery_Outcome (transition_result.Accepted (Left 4 2))) t"
    unfolding t_def q_def using second
    by (auto simp: joined_dosp.product_source_step_def joined_dosp.product_recovery_step_def
      joined_dosp.consensus_membership_step_def joined_dosp.activation_uses_the_existing_grant_and_handoff
      earlier_route_update_is_pending_def route_grant_matches_its_epoch_def
      with_finality_core_def with_operational_state_def joined_initial_def Let_def)
  have denied: "\<not> (\<exists>response updated. joined_dosp.prepare_product_credit t early_reserve response updated)"
    unfolding joined_dosp.prepare_product_credit_def joined_dosp.native_preparation_ready_def t_def q_def
    by (simp add: early_native_request_fields Let_def)
  show "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    ordered_leave_grants t (Prepare_Native early_reserve) (Binding_Outcome Precommit_Refused) t"
    unfolding joined_dosp.product_source_step_def using denied by (simp add: Let_def)
qed

lemma at_the_effective_second_the_old_route_cannot_take_the_native_lock:
  "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    cleanup_grant before_the_first_credit (Prepare_Native early_reserve) (Binding_Outcome Precommit_Refused) before_the_first_credit"
proof -
  have due: "route_activation_is_due (source_consensus before_the_first_credit) (source_recovery before_the_first_credit) cleanup_grant"
    unfolding route_activation_is_due_def
    by (intro exI[of _ "Leave_Domain 0 4"] exI[of _ 2] exI[of _ 86399])
       (simp add: current_grant_def with_finality_core_def with_operational_state_def joined_initial_def)
  show ?thesis using joined_dosp.fresh_native_preparation_waits_for_due_route_activation[OF due, of early_reserve]
    by simp
qed

lemma an_unrelated_endpoint_cannot_take_the_actual_reservation:
  "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    {} before_the_first_credit (Prepare_Native (Client_Protocol 9 0 (Reserve_Intent (sample_request 17) [] 10)))
    (Binding_Outcome Precommit_Refused) before_the_first_credit"
proof -
  let ?wrong = "Client_Protocol 9 0 (Reserve_Intent (sample_request 17) [] 10)"
  have absent: "\<not> (\<exists>response updated. joined_dosp.prepare_product_credit before_the_first_credit ?wrong response updated)"
  proof
    assume "\<exists>response updated. joined_dosp.prepare_product_credit before_the_first_credit ?wrong response updated"
    then obtain response updated where "joined_dosp.prepare_product_credit before_the_first_credit ?wrong response updated" by blast
    from joined_dosp.a_source_preparation_uses_the_exact_active_endpoint[OF this] show False
      by (simp add: early_native_request_fields)
  qed
  show ?thesis unfolding joined_dosp.product_source_step_def using absent by (simp add: Let_def)
qed

theorem an_observed_divergence_before_the_first_publication_blocks_reserve:
  fixes q :: product_source_state
  defines "q \<equiv> before_the_first_credit\<lparr>source_recovery := early_recovery\<lparr>replica := (\<lambda>_. 0)(4 := 1),
      work_owner := Map.empty(99 \<mapsto> 4)\<rparr>, observed_divergence_work := {99}\<rparr>"
  shows "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    {} before_the_first_credit (Update_Recovery (Register_Divergence 99 4 1))
    (Recovery_Outcome (transition_result.Accepted (Opened 99))) q"
  "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    {} q (Prepare_Native early_reserve) (Binding_Outcome Precommit_Refused) q"
proof -
  have raw: "recovery_step {} {} early_recovery (Notice_Divergence 99 4 1)
      (transition_result.Accepted (Opened 99))
      (early_recovery\<lparr>replica := (replica early_recovery)(4 := 1), work_owner := (work_owner early_recovery)(99 \<mapsto> 4)\<rparr>)"
    by (rule recovery_step.Detect_Divergence) (simp_all add: fresh_work_def)
  show actual: "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    {} before_the_first_credit (Update_Recovery (Register_Divergence 99 4 1))
    (Recovery_Outcome (transition_result.Accepted (Opened 99))) q"
    unfolding joined_dosp.product_source_step_def q_def using raw
    by (auto simp: joined_dosp.product_recovery_step_def joined_dosp.offered_recovery_step_def Let_def)
  have blocked: "\<not> recovery_permits_native_credit q"
    using joined_dosp.recorded_divergence_blocks_new_native_credit_even_before_first_publication[OF actual] by blast
  have none: "\<not> (\<exists>response updated. joined_dosp.prepare_product_credit q early_reserve response updated)"
  proof
    assume "\<exists>response updated. joined_dosp.prepare_product_credit q early_reserve response updated"
    then obtain response updated where "joined_dosp.prepare_product_credit q early_reserve response updated" by blast
    from joined_dosp.a_new_native_preparation_waits_for_required_recovery[OF this] blocked show False by simp
  qed
  show "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    {} q (Prepare_Native early_reserve) (Binding_Outcome Precommit_Refused) q"
    unfolding joined_dosp.product_source_step_def using none by (simp add: Let_def)
qed

lemma the_second_issued_receipt_is_the_current_primary:
  "current_primary_is_recorded actual_authority published_recovery_state"
  "issued_receipt actual_authority (primary_sequence published_recovery_state) = Some issued_second_receipt"
  "registered_asset (current_operational actual_authority) = 17"
proof -
  show "current_primary_is_recorded actual_authority published_recovery_state"
    unfolding current_primary_is_recorded_def
    by (simp add: published_recovery_state_def actual_publication_fields(2)
      the_same_asset_was_metered_and_published_on_both_sides_of_promotion(5) issued_second_receipt_def Let_def)
  show "issued_receipt actual_authority (primary_sequence published_recovery_state) = Some issued_second_receipt"
    by (simp add: published_recovery_state_def actual_publication_fields(2) issued_second_receipt_def Let_def)
  show "registered_asset (current_operational actual_authority) = 17"
    by (simp add: joined_authority_normal_form second_metered_operational_def second_meter_operational_fields(2))
qed

lemma the_first_issued_receipt_is_historical_at_the_second_primary:
  "joined_dosp.a_replica_shows_a_different_issued_receipt actual_authority sources published_recovery_state fixture_receipt"
proof -
  have previous: "issued_receipt actual_authority (published_sequence fixture_receipt) = Some fixture_receipt"
    by (simp add: fixture_receipt_def actual_publication_fields(1))
  have different: "fixture_receipt \<noteq> issued_second_receipt"
    by (simp add: fixture_receipt_def issued_second_receipt_def)
  show ?thesis unfolding joined_dosp.a_replica_shows_a_different_issued_receipt_def
    using the_second_issued_receipt_is_the_current_primary previous different
    by (auto simp: fixture_receipt_def fixture_binding(3) intro!: exI[of _ issued_second_receipt])
qed

theorem the_two_actual_equal_valued_receipts_have_different_recovery_observations:
  fixes p q :: product_source_state
  defines "p \<equiv> second_candidate_product\<lparr>source_consensus := actual_authority, source_recovery := published_recovery_state\<rparr>"
    and "q \<equiv> p\<lparr>source_recovery := published_recovery_state\<lparr>work_owner := Map.empty(99 \<mapsto> 4)\<rparr>,
      observed_divergence_work := {99}\<rparr>"
  shows "primary_transfer_value fixture_receipt = primary_transfer_value issued_second_receipt"
  "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    {} p (Report_Replica_Receipt 99 4 fixture_receipt) (Recovery_Outcome (transition_result.Accepted (Opened 99))) q"
  "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    {} p (Report_Replica_Receipt 99 4 issued_second_receipt) (Recovery_Outcome (transition_result.Internal ())) p"
proof -
  show "primary_transfer_value fixture_receipt = primary_transfer_value issued_second_receipt"
    by (simp add: primary_transfer_value_def fixture_receipt_def issued_second_receipt_def
      sample_binding_def example_binding_def)
  have recovery: "source_recovery p = published_recovery_state" "source_consensus p = actual_authority"
    "observed_divergence_work p = {}"
    by (simp_all add: p_def)
  have owners: "work_owner published_recovery_state = Map.empty"
    by (simp add: published_recovery_state_def Let_def)
  have member: "4 \<in> active_domains (source_recovery p)" "fresh_work (source_recovery p) 99"
    by (simp_all add: recovery published_recovery_state_def Let_def fresh_work_def)
  have stale: "joined_dosp.a_replica_shows_a_different_issued_receipt (source_consensus p) two_journals (source_recovery p) fixture_receipt"
    using the_first_issued_receipt_is_historical_at_the_second_primary by (simp only: recovery)
  have opened: "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    {} p (Report_Replica_Receipt 99 4 fixture_receipt) (Recovery_Outcome (transition_result.Accepted (Opened 99)))
    (p\<lparr>source_recovery := (source_recovery p)\<lparr>work_owner := (work_owner (source_recovery p))(99 \<mapsto> 4)\<rparr>,
      observed_divergence_work := insert 99 (observed_divergence_work p)\<rparr>)"
    by (rule joined_dosp.a_receipt_regression_opens_work_even_when_its_replica_value_matches[OF member stale]) simp
  show "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    {} p (Report_Replica_Receipt 99 4 fixture_receipt) (Recovery_Outcome (transition_result.Accepted (Opened 99))) q"
    using opened by (simp add: q_def recovery owners)
  show "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    {} p (Report_Replica_Receipt 99 4 issued_second_receipt) (Recovery_Outcome (transition_result.Internal ())) p"
    unfolding p_def
    by (subst joined_dosp.observing_the_current_receipt_cannot_create_divergent_work)
      (simp_all add: the_second_issued_receipt_is_the_current_primary(2) Let_def)
qed

theorem a_competing_issued_receipt_at_the_same_number_opens_replica_work:
  fixes sources :: available_journals
  defines "sources \<equiv> two_journals(41 \<mapsto> competing_publisher_journal)"
  shows "published_sequence competing_receipt = primary_sequence published_recovery_state"
    "\<exists>p q t. joined_dosp.product_source_step example_versions {} measured_second_input {} {} sources current_repair_head []
      {} second_candidate_product (Meter_Native quoted_request 0 Bypass_Route (sample_request 23))
      (Binding_Outcome (Cycle_Result (transition_result.Accepted Binding_Committed))) p \<and>
      joined_dosp.product_source_step example_versions {} measured_second_input {} {} sources current_repair_head []
        {} p (Report_Replica_Receipt 99 4 competing_receipt) (Recovery_Outcome (transition_result.Accepted (Opened 99))) q \<and>
      work_owner (source_recovery q) 99 = Some 4 \<and> primary_sequence (source_recovery q) = 51 \<and>
      99 \<in> observed_divergence_work q \<and>
      joined_dosp.product_source_step example_versions {} measured_second_input {} {} sources
        (current_repair_head\<lparr>head_route_epoch := 1\<rparr>) [live_offer] {} q (Update_Recovery (Repair_Replica 99 51))
        (Recovery_Outcome (transition_result.Accepted (Installed 99 4 51))) t \<and>
      99 \<in> completion_log (source_recovery t) \<and> 99 \<notin> observed_divergence_work t \<and>
      work_owner (source_recovery t) 8 = Some 2 \<and> irreversible_facts (source_recovery t) = irreversible_facts (source_recovery q)"
proof -
  let ?repair = "published_recovery_state\<lparr>active_domains := {0,2,4}, work_owner := second_publication_work\<rparr>"
  obtain p where raw: "joined_dosp.joint_credit_step Active_Credit_Route example_versions {} measured_second_input second_candidate_product
      quoted_request 0 Bypass_Route (sample_request 23) (Cycle_Result (transition_result.Accepted Binding_Committed)) p"
    and state: "source_consensus p = actual_authority" "source_recovery p = ?repair"
    and seq: "primary_sequence (source_recovery p) = 51"
    using the_actual_eab_credit_and_matching_public_row_commit_together by blast
  have published: "joined_dosp.product_source_step example_versions {} measured_second_input {} {} sources current_repair_head []
      {} second_candidate_product (Meter_Native quoted_request 0 Bypass_Route (sample_request 23))
      (Binding_Outcome (Cycle_Result (transition_result.Accepted Binding_Committed))) p"
    using raw unfolding joined_dosp.product_source_step_def
    by (auto simp: route_activation_is_due_def current_grant_def Let_def)
  have number: "published_sequence competing_receipt = 51" by (simp add: fixture_receipt_def)
  show "published_sequence competing_receipt = primary_sequence published_recovery_state"
    by (simp add: number published_recovery_state_def actual_publication_fields(2) issued_second_receipt_def Let_def)
  have distinct: "competing_receipt \<noteq> issued_second_receipt"
    by (simp add: fixture_receipt_def issued_second_receipt_def)
  have evidence: "\<exists>issuer original. sources issuer = Some original \<and>
      joined_dosp.journal.checked_current_replay original (current_source_candidate original) = Some (call_authority_state original) \<and>
      issued_receipt (call_authority_state original) (published_sequence competing_receipt) = Some competing_receipt"
    by (intro exI[of _ 41] exI[of _ competing_publisher_journal])
      (simp add: sources_def competing_journal_replays_its_issued_record competing_journal_receipt number)
  have anchor: "current_primary_is_recorded actual_authority ?repair"
    using the_second_issued_receipt_is_the_current_primary(1) by (simp add: current_primary_is_recorded_def)
  have current: "issued_receipt actual_authority (primary_sequence ?repair) = Some issued_second_receipt"
    using the_second_issued_receipt_is_the_current_primary(2) by simp
  have stale: "joined_dosp.a_replica_shows_a_different_issued_receipt actual_authority sources ?repair competing_receipt"
    unfolding joined_dosp.a_replica_shows_a_different_issued_receipt_def
    using anchor current the_second_issued_receipt_is_the_current_primary(3) distinct evidence
    by (auto simp: fixture_receipt_def fixture_binding(3) intro!: exI[of _ issued_second_receipt])
  have mismatch: "joined_dosp.a_replica_shows_a_different_issued_receipt (source_consensus p) sources (source_recovery p) competing_receipt"
    using stale by (simp only: state)
  have ready: "4 \<in> active_domains (source_recovery p)" "fresh_work (source_recovery p) 99"
    by (simp_all add: state published_recovery_state_def fresh_work_def Let_def)
  let ?q = "p\<lparr>source_recovery := (source_recovery p)\<lparr>work_owner := (work_owner (source_recovery p))(99 \<mapsto> 4)\<rparr>,
        observed_divergence_work := insert 99 (observed_divergence_work p)\<rparr>"
  have observed: "joined_dosp.product_source_step example_versions {} measured_second_input {} {} sources current_repair_head []
      {} p (Report_Replica_Receipt 99 4 competing_receipt) (Recovery_Outcome (transition_result.Accepted (Opened 99)))
      ?q"
    by (rule joined_dosp.a_receipt_regression_opens_work_even_when_its_replica_value_matches[OF ready mismatch]) simp
  let ?head = "current_repair_head\<lparr>head_route_epoch := 1\<rparr>"
  let ?r = "source_recovery ?q"
  let ?t = "?q\<lparr>source_recovery := install_replica ?r 99 4, observed_divergence_work := observed_divergence_work ?q - {99}\<rparr>"
  have r_epoch: "route_epoch ?r = 1"
    by (simp add: state published_recovery_state_def Let_def)
  have selected_at_one: "joined_dosp.select_current_publication sources ?head [live_offer] 1 =
      Some (current_publication_authority actual_authority, issued_second_receipt)"
    by (simp add: joined_dosp.select_current_publication_def sources_def two_journals_def current_repair_head_def
      replay_of_the_metered_journal actual_publication_fields(2) issued_second_receipt_def Let_def)
  have selected: "joined_dosp.select_current_publication sources ?head [live_offer] (route_epoch ?r) =
      Some (current_publication_authority actual_authority, issued_second_receipt)"
    by (simp only: r_epoch selected_at_one)
  have matches: "primary_receipt_matches (current_publication_authority actual_authority) issued_second_receipt ?r"
    using handoff_has_a_real_primary_and_current_epoch(2)
    by (simp add: primary_receipt_matches_def state handed_off_recovery_def joined_recovery_def noticed_recovery_def)
  have issued_number: "published_sequence issued_second_receipt = 51"
    by (simp add: issued_second_receipt_def)
  have request: "requested_repair_can_run ?r 99 51" "\<not> rollback_incomplete ?r"
    by (simp_all add: requested_repair_can_run_def state seq published_recovery_state_def actual_publication_fields issued_number Let_def)
  have job: "joined_dosp.verified_job_ready sources ?head [live_offer] ?r 99 4 51"
    using selected matches seq
    by (auto simp: joined_dosp.verified_job_ready_def state r_epoch selected_at_one published_recovery_state_def
      actual_publication_fields issued_number Let_def)
  have asset: "joined_dosp.selected_asset sources ?head [live_offer] ?r =
      Some (registered_asset (current_operational (source_consensus ?q)))"
    using selected the_second_issued_receipt_is_the_current_primary(3)
    by (simp add: joined_dosp.selected_asset_def state r_epoch selected_at_one issued_second_receipt_def second_request_fields)
  have current_pub: "joined_dosp.publication_matches_current_state (source_consensus ?q) sources ?head [live_offer] ?r"
    using selected by (simp add: joined_dosp.publication_matches_current_state_def state r_epoch selected_at_one current_repair_head_def
      actual_publication_fields(2) the_same_asset_was_metered_and_published_on_both_sides_of_promotion(5))
  have repaired: "joined_dosp.product_recovery_step (source_consensus ?q) {} {} sources ?head [live_offer] {}
      ?r (Repair_Replica 99 51) (transition_result.Accepted (Installed 99 4 51)) (install_replica ?r 99 4)"
    using asset current_pub request joined_dosp.ready_job_can_install[OF job, where grants="{}" and governance="{}"]
    by (simp add: joined_dosp.product_recovery_step_def)
  have installed: "joined_dosp.product_source_step example_versions {} measured_second_input {} {} sources
      ?head [live_offer] {} ?q (Update_Recovery (Repair_Replica 99 51))
      (Recovery_Outcome (transition_result.Accepted (Installed 99 4 51))) ?t"
    unfolding joined_dosp.product_source_step_def using repaired by (auto simp: Let_def)
  show "\<exists>p q t. joined_dosp.product_source_step example_versions {} measured_second_input {} {} sources current_repair_head []
      {} second_candidate_product (Meter_Native quoted_request 0 Bypass_Route (sample_request 23))
      (Binding_Outcome (Cycle_Result (transition_result.Accepted Binding_Committed))) p \<and>
      joined_dosp.product_source_step example_versions {} measured_second_input {} {} sources current_repair_head []
        {} p (Report_Replica_Receipt 99 4 competing_receipt) (Recovery_Outcome (transition_result.Accepted (Opened 99))) q \<and>
      work_owner (source_recovery q) 99 = Some 4 \<and> primary_sequence (source_recovery q) = 51 \<and>
      99 \<in> observed_divergence_work q \<and>
      joined_dosp.product_source_step example_versions {} measured_second_input {} {} sources
        ?head [live_offer] {} q (Update_Recovery (Repair_Replica 99 51))
        (Recovery_Outcome (transition_result.Accepted (Installed 99 4 51))) t \<and>
      99 \<in> completion_log (source_recovery t) \<and> 99 \<notin> observed_divergence_work t \<and>
      work_owner (source_recovery t) 8 = Some 2 \<and> irreversible_facts (source_recovery t) = irreversible_facts (source_recovery q)"
    using published observed installed seq
    by (intro exI[of _ p] exI[of _ ?q] exI[of _ ?t])
      (simp add: install_replica_def state published_recovery_state_def actual_publication_fields issued_number Let_def)
qed

theorem the_actual_join_exposes_the_new_replica_and_keeps_the_old_cells:
  "replica_cell noticed_recovery 6 = None"
  "replica_cell joined_recovery 6 = Some (replica noticed_recovery 6)"
  "\<And>d. d \<noteq> 6 \<Longrightarrow> replica_cell joined_recovery d = replica_cell noticed_recovery d"
  "work_owner joined_recovery 8 = Some 2" "work_owner joined_recovery 9 = Some 6"
  "irreversible_facts joined_recovery = irreversible_facts noticed_recovery"
proof -
  have clock: "consensus_now actual_authority = 86400"
    by (simp add: joined_authority_normal_form second_meter_operational_fields(6))
  have step: "joined_dosp.product_recovery_step actual_authority {} {} two_journals current_repair_head []
    joined_recovery_grants noticed_recovery (Activate_Route (Join_Domain 6 9) 2 86400)
    (transition_result.Accepted (Joined 6 9)) joined_recovery"
    unfolding joined_dosp.product_recovery_step_def joined_dosp.consensus_membership_step_def
    using this_publication_produces_a_job_that_moves_to_the_new_domain(2)
    by (auto simp: joined_dosp.activation_uses_the_existing_grant_and_handoff clock
      earlier_route_update_is_pending_def route_grant_matches_its_epoch_def joined_recovery_grants_def
      noticed_recovery_def published_recovery_state_def fresh_work_def Let_def)
  note frame = joined_dosp.joining_initializes_the_new_cell_and_frames_existing_replica_and_work[OF step]
  from frame show "replica_cell noticed_recovery 6 = None" "replica_cell joined_recovery 6 = Some (replica noticed_recovery 6)"
    "\<And>d. d \<noteq> 6 \<Longrightarrow> replica_cell joined_recovery d = replica_cell noticed_recovery d"
    "work_owner joined_recovery 9 = Some 6" "irreversible_facts joined_recovery = irreversible_facts noticed_recovery"
    by blast+
  from frame show "work_owner joined_recovery 8 = Some 2"
    by (auto simp: noticed_recovery_def)
qed

abbreviation future_join_grants :: "nat routing_grants" where
  "future_join_grants \<equiv> {(Join_Domain (6::nat) 99,2,86401)}"

lemma the_reserved_fixture_job_is_replaced_with_the_first_free_id:
  fixes s :: "nat recovery_state"
  assumes "route_epoch s = 1" "work_owner s = Map.empty" "completion_log s = {}"
  shows "recovery_job_for_observation s future_join_grants 99 = Some 0"
proof -
  have reserved: "outstanding_join_jobs s future_join_grants = {99}"
    using assms(1) by (auto simp: outstanding_join_jobs_def)
  let ?usable = "\<lambda>job. fresh_work s job \<and> job \<notin> outstanding_join_jobs s future_join_grants"
  have zero: "?usable 0" using assms reserved by (simp add: fresh_work_def)
  have best: "(LEAST job. ?usable job) = 0"
  proof (rule Least_equality[where P="?usable" and x="0::nat"])
    show "?usable 0" by (rule zero)
    show "\<And>job. ?usable job \<Longrightarrow> (0::nat) \<le> job" by (rule le0)
  qed
  have some: "\<exists>job. ?usable job" using zero by blast
  have held: "99 \<in> outstanding_join_jobs s future_join_grants" by (simp add: reserved)
  have picked: "recovery_job_for_observation s future_join_grants 99 = Some (LEAST job. ?usable job)"
    by (simp only: recovery_job_for_observation_def Let_def held some if_True)
  show ?thesis using picked best by simp
qed

theorem stale_observations_get_new_jobs_without_using_the_scheduled_join_id:
  "\<exists>q. joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    future_join_grants before_the_first_credit (Update_Recovery (Register_Divergence 99 4 1))
    (Recovery_Outcome (transition_result.Accepted (Opened 0))) q \<and>
    work_owner (source_recovery q) 0 = Some 4 \<and> fresh_work (source_recovery q) 99 \<and> observed_divergence_work q = {0}"
  "\<exists>q. joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    future_join_grants
    (second_candidate_product\<lparr>source_consensus := actual_authority, source_recovery := published_recovery_state\<rparr>)
    (Report_Replica_Receipt 99 4 fixture_receipt) (Recovery_Outcome (transition_result.Accepted (Opened 0))) q \<and>
    work_owner (source_recovery q) 0 = Some 4 \<and> fresh_work (source_recovery q) 99 \<and> observed_divergence_work q = {0}"
proof -
  let ?opened = "early_recovery\<lparr>replica := (replica early_recovery)(4 := 1), work_owner := Map.empty(0 \<mapsto> 4)\<rparr>"
  let ?q = "before_the_first_credit\<lparr>source_recovery := ?opened, observed_divergence_work := {0}\<rparr>"
  have chosen: "recovery_job_for_observation early_recovery future_join_grants 99 = Some 0"
    by (rule the_reserved_fixture_job_is_replaced_with_the_first_free_id) simp_all
  have notice: "recovery_step future_join_grants {} early_recovery (Notice_Divergence 0 4 1)
      (transition_result.Accepted (Opened 0)) ?opened"
    using recovery_step.Detect_Divergence[where s=early_recovery and d=4 and i=0 and observed=1 and grants=future_join_grants and governance="{}"]
    by (simp add: fresh_work_def)
  have accepted: "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    future_join_grants before_the_first_credit (Update_Recovery (Register_Divergence 99 4 1))
    (Recovery_Outcome (transition_result.Accepted (Opened 0))) ?q"
    unfolding joined_dosp.product_source_step_def using notice chosen
    by (auto simp: joined_dosp.product_recovery_step_def joined_dosp.offered_recovery_step_def Let_def)
  show "\<exists>q. joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    future_join_grants before_the_first_credit (Update_Recovery (Register_Divergence 99 4 1))
    (Recovery_Outcome (transition_result.Accepted (Opened 0))) q \<and>
    work_owner (source_recovery q) 0 = Some 4 \<and> fresh_work (source_recovery q) 99 \<and> observed_divergence_work q = {0}"
    using accepted by (intro exI[of _ ?q]) (simp add: fresh_work_def)
  let ?current = "second_candidate_product\<lparr>source_consensus := actual_authority, source_recovery := published_recovery_state\<rparr>"
  let ?after = "?current\<lparr>source_recovery := published_recovery_state\<lparr>work_owner := Map.empty(0 \<mapsto> 4)\<rparr>,
    observed_divergence_work := {0}\<rparr>"
  have post_choice: "recovery_job_for_observation published_recovery_state future_join_grants 99 = Some 0"
    by (rule the_reserved_fixture_job_is_replaced_with_the_first_free_id) (simp_all add: published_recovery_state_def Let_def)
  have received: "joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
      future_join_grants ?current (Report_Replica_Receipt 99 4 fixture_receipt)
      (Recovery_Outcome (transition_result.Accepted (Opened 0))) ?after"
    unfolding joined_dosp.product_source_step_def
    using the_first_issued_receipt_is_historical_at_the_second_primary post_choice
    by (simp add: published_recovery_state_def fresh_work_def Let_def)
  show "\<exists>q. joined_dosp.product_source_step example_versions {} measured_second_input {} {} two_journals current_repair_head []
    future_join_grants ?current (Report_Replica_Receipt 99 4 fixture_receipt) (Recovery_Outcome (transition_result.Accepted (Opened 0))) q \<and>
    work_owner (source_recovery q) 0 = Some 4 \<and> fresh_work (source_recovery q) 99 \<and> observed_divergence_work q = {0}"
    using received by (intro exI[of _ ?after]) (simp add: fresh_work_def published_recovery_state_def Let_def)
qed

end
