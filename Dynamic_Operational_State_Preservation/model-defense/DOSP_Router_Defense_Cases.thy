theory DOSP_Router_Defense_Cases
  imports DOSP_Commit_Defense
begin

definition initial_registry_record ::
  "tvo_features \<Rightarrow> operational_level \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> cutover_metadata option" where
  "initial_registry_record features path version epoch =
    (case tvo_required_level features of None \<Rightarrow> None
     | Some required \<Rightarrow> if level_rank required \<le> level_rank path then
        Some \<lparr>required_level = required, chosen_path = path, meter_version = version, cutover_epoch = epoch\<rparr>
       else None)"

lemma first_matching_registry_rule_is_the_one_consumed:
  "initial_registry_record features path version epoch = Some meta \<longleftrightarrow>
    (\<exists>required. tvo_required_level features = Some required \<and> level_rank required \<le> level_rank path \<and>
      meta = \<lparr>required_level = required, chosen_path = path, meter_version = version, cutover_epoch = epoch\<rparr>)"
  by (auto simp: initial_registry_record_def split: option.splits if_splits)

lemma routed_flow_naturality_uses_the_same_ticket_and_result:
  assumes keep: "participants action \<subseteq> domains"
  shows "route_and_execute registry (restrict_policy domains policy) asset ticket healthy
      (forget_outside domains s) action =
    map_prod (forget_outside domains) id (route_and_execute registry policy asset ticket healthy s action)"
proof -
  have legal: "\<And>level. legal_at (restrict_policy domains policy) level action = legal_at policy level action"
    using keep by (cases action) (auto simp: restrict_policy_def)
  let ?path = "chosen_path (ticket_metadata ticket)"
  obtain t reply where actual: "evaluate_flow policy ?path healthy s action = (t, reply)"
    by (cases "evaluate_flow policy ?path healthy s action") auto
  have base: "flow_step policy ?path healthy s action reply t" using actual by (simp add: flow_step_def)
  have projected: "evaluate_flow (restrict_policy domains policy) ?path healthy (forget_outside domains s) action =
    (forget_outside domains t, reply)"
    using flow_naturality_in_scope[OF keep base] by (simp add: flow_step_def)
  have guard:
    "ticket_authorizes registry (restrict_policy domains policy) asset ticket action =
      ticket_authorizes registry policy asset ticket action"
    by (simp add: ticket_authorizes_def legal)
  show ?thesis by (simp add: route_and_execute_def guard actual projected)
qed

definition quiet_asset :: tvo_features where
  "quiet_asset = \<lparr>regulatory_subject = False, periodic_payments = False, maturity = False,
     off_chain_integration = False, variable_rate_linkage = False, bidirectional_required = False\<rparr>"

abbreviation only_rate :: tvo_features where
  "only_rate \<equiv> quiet_asset\<lparr>variable_rate_linkage := True\<rparr>"

abbreviation two_conditions_asset :: tvo_features where
  "two_conditions_asset \<equiv> only_rate\<lparr>periodic_payments := True\<rparr>"

lemma registered_metadata_follows_all_decided_tvo_branches:
  "initial_registry_record quiet_asset Static 4 8 =
    Some \<lparr>required_level = Static, chosen_path = Static, meter_version = 4, cutover_epoch = 8\<rparr>"
  "initial_registry_record only_rate Atomic 4 8 = Some observation_metadata"
  "initial_registry_record (only_rate\<lparr>bidirectional_required := True\<rparr>) Atomic 4 8 = None"
  "initial_registry_record two_conditions_asset Atomic 3 11 = Some coupling_ticket"
  "initial_registry_record (two_conditions_asset\<lparr>regulatory_subject := True\<rparr>) Coupled 3 11 = None"
  "initial_registry_record (two_conditions_asset\<lparr>regulatory_subject := True\<rparr>) Atomic 4 12 =
    Some (promoted_metadata 12 4)"
  by (simp_all add: initial_registry_record_def tvo_required_level_def quiet_asset_def observation_metadata_def
      coupling_ticket_def promoted_metadata_def)

theorem classified_registry_asset_reaches_the_recorded_native_usage:
  "\<exists>meta ticket. initial_registry_record two_conditions_asset Atomic 3 11 = Some meta \<and>
    issue_route_ticket (authority_registry joined_initial) 17 0 = Some ticket \<and> ticket_metadata ticket = meta \<and>
    joined_dosp.run_registered_meter ticket (17,7,3) 0 Bypass_Route (sample_request 17) joined_initial =
      Some (after_first_meter, Credit_Result (Some (Credit_Metered fixture_billed_usage))) \<and>
    fixture_billed_usage = billing_record (prod_encode (0,17)) meta (transfer_commit (request_binding (sample_request 17)))"
proof -
  have metadata: "initial_registry_record two_conditions_asset Atomic 3 11 = Some coupling_ticket"
    by (rule registered_metadata_follows_all_decided_tvo_branches(4))
  have ticket: "issue_route_ticket (authority_registry joined_initial) 17 0 = Some (joined_ticket 0 coupling_ticket)"
    by (simp add: joined_ticket_def authority_registry_def issue_route_ticket_def joined_initial_def
      cycle_fixture_def meter_fixture_def)
  have meter: "joined_dosp.run_registered_meter (joined_ticket 0 coupling_ticket) (17,7,3) 0 Bypass_Route
      (sample_request 17) joined_initial =
       Some (after_first_meter, Credit_Result (Some (Credit_Metered fixture_billed_usage)))"
    by (rule current_registry_ticket_reaches_actual_native_metering)
  have price: "fixture_billed_usage = billing_record (prod_encode (0,17)) coupling_ticket
    (transfer_commit (request_binding (sample_request 17)))"
    by (simp only: fixture_binding)
  show ?thesis using metadata ticket meter price by (force simp: joined_ticket_def)
qed

lemma an_initiator_cannot_use_another_initiators_path:
  "snd (route_and_execute soft_registry two_origin_policy 17 (joined_ticket 1 (route_metadata soft_start)) True
      (binding_state soft_start) (Commit_From 1 2 10)) = transition_result.Accepted (Committed_Value 10)"
  "snd (route_and_execute soft_registry two_origin_policy 17 (joined_ticket 2 (route_metadata soft_start)) True
      (binding_state soft_start) (Commit_From 2 1 10)) = transition_result.Accepted (Committed_Value 10)"
  "route_and_execute soft_registry two_origin_policy 17 (joined_ticket 1 (route_metadata soft_start)) True
      (binding_state soft_start) (Commit_From 2 1 10) = (binding_state soft_start, transition_result.Rejected ())"
  "route_and_execute soft_registry two_origin_policy 18 (joined_ticket 1 (route_metadata soft_start)) True
      (binding_state soft_start) (Commit_From 1 2 10) = (binding_state soft_start, transition_result.Rejected ())"
  by (simp_all add: route_and_execute_def ticket_authorizes_def issue_route_ticket_def soft_registry_def joined_ticket_def
      two_origin_policy_def soft_start_def cutover_start_def old_plan_def)

lemma omitting_an_initiator_does_not_preserve_the_router_result:
  "snd (route_and_execute soft_registry (restrict_policy {2} two_origin_policy) 17
      (joined_ticket 1 (route_metadata soft_start)) True (forget_outside {2} (binding_state soft_start))
      (Commit_From 1 2 10)) = transition_result.Rejected ()"
  "snd (route_and_execute soft_registry two_origin_policy 17 (joined_ticket 1 (route_metadata soft_start)) True
      (binding_state soft_start) (Commit_From 1 2 10)) \<noteq> transition_result.Rejected ()"
  by (simp_all add: route_and_execute_def ticket_authorizes_def issue_route_ticket_def soft_registry_def joined_ticket_def
      two_origin_policy_def restrict_policy_def soft_start_def cutover_start_def old_plan_def)

lemma same_routed_commit_distinguishes_soft_failure_and_atomic_rollback:
  defines "atomic_path \<equiv> (route_metadata soft_start)\<lparr>chosen_path := Atomic\<rparr>"
  shows "snd (route_and_execute soft_registry two_origin_policy 17 (joined_ticket 1 (route_metadata soft_start)) False
      (binding_state soft_start) (Commit_From 1 2 10)) = transition_result.Operational_Failure Partial_Write"
    "route_and_execute (Map.empty(17 \<mapsto> atomic_path)) two_origin_policy 17 (joined_ticket 1 atomic_path) False
      (binding_state soft_start) (Commit_From 1 2 10) = (binding_state soft_start, transition_result.Operational_Failure Rolled_Back)"
  unfolding atomic_path_def by (simp_all add: route_and_execute_def ticket_authorizes_def issue_route_ticket_def soft_registry_def
      joined_ticket_def two_origin_policy_def soft_start_def cutover_start_def old_plan_def)

end
