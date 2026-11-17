theory DOSP_Registry_Defense
  imports DOSP_Integrated_Recovery.Integrated_Recovery_Path DOSP_Degree.Degree_Examples
begin

record tvo_features =
  regulatory_subject :: bool
  periodic_payments :: bool
  maturity :: bool
  off_chain_integration :: bool
  variable_rate_linkage :: bool
  bidirectional_required :: bool

definition tvo_required_level :: "tvo_features \<Rightarrow> operational_level option" where
  "tvo_required_level features =
    (if regulatory_subject features then Some Atomic
     else if periodic_payments features \<or> maturity features \<or> off_chain_integration features then Some Coupled
     else if variable_rate_linkage features then
       (if bidirectional_required features then None else Some Observation)
     else Some Static)"

lemma regulatory_subject_overrides_the_other_features:
  "regulatory_subject features \<Longrightarrow> tvo_required_level features = Some Atomic"
  by (simp add: tvo_required_level_def)

lemma periodic_external_rate_asset_is_coupled:
  "\<not> regulatory_subject features \<Longrightarrow> periodic_payments features \<Longrightarrow>
    variable_rate_linkage features \<Longrightarrow> tvo_required_level features = Some Coupled"
  by (simp add: tvo_required_level_def)

type_synonym registry_snapshot = "nat \<Rightarrow> cutover_metadata option"

record route_ticket =
  ticket_asset :: nat
  ticket_initiator :: nat
  ticket_metadata :: cutover_metadata

fun flow_initiator :: "nat flow_action \<Rightarrow> nat" where
  "flow_initiator (Read_From source target) = source"
| "flow_initiator (Commit_From source target value) = source"

definition issue_route_ticket :: "registry_snapshot \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> route_ticket option" where
  "issue_route_ticket registry asset initiator =
    map_option (\<lambda>meta. \<lparr>ticket_asset = asset, ticket_initiator = initiator, ticket_metadata = meta\<rparr>)
      (registry asset)"

definition ticket_authorizes :: "registry_snapshot \<Rightarrow> nat flow_policy \<Rightarrow> nat \<Rightarrow>
    route_ticket \<Rightarrow> nat flow_action \<Rightarrow> bool" where
  "ticket_authorizes registry policy asset presented action \<longleftrightarrow>
    issue_route_ticket registry asset (flow_initiator action) = Some presented \<and>
    legal_at policy (required_level (ticket_metadata presented)) action \<and>
    level_rank (required_level (ticket_metadata presented)) \<le> level_rank (chosen_path (ticket_metadata presented))"

definition route_and_execute :: "registry_snapshot \<Rightarrow> nat flow_policy \<Rightarrow> nat \<Rightarrow>
    route_ticket \<Rightarrow> bool \<Rightarrow> nat flow_state \<Rightarrow> nat flow_action \<Rightarrow> nat flow_state \<times> flow_result" where
  "route_and_execute registry policy asset ticket healthy s action =
    (if ticket_authorizes registry policy asset ticket action then
      evaluate_flow policy (chosen_path (ticket_metadata ticket)) healthy s action
     else (s, transition_result.Rejected ()))"

lemma issued_ticket_names_the_same_registry_record:
  "issue_route_ticket registry asset initiator = Some ticket \<Longrightarrow>
    ticket_asset ticket = asset \<and> ticket_initiator ticket = initiator \<and>
    registry asset = Some (ticket_metadata ticket)"
  by (auto simp: issue_route_ticket_def split: option.splits)

lemma routed_success_records_the_same_authority:
  assumes "route_and_execute registry policy asset ticket healthy s action = (t, transition_result.Accepted result)"
  shows "ticket_asset ticket = asset \<and> ticket_initiator ticket = flow_initiator action \<and>
    registry asset = Some (ticket_metadata ticket) \<and>
    legal_at policy (required_level (ticket_metadata ticket)) action \<and>
    flow_step policy (chosen_path (ticket_metadata ticket)) healthy s action (transition_result.Accepted result) t"
proof -
  have authorized: "ticket_authorizes registry policy asset ticket action"
    using assms by (auto simp: route_and_execute_def split: if_splits)
  then show ?thesis using assms
    by (auto simp: ticket_authorizes_def route_and_execute_def flow_step_def
        dest: issued_ticket_names_the_same_registry_record)
qed

definition authority_registry :: "integrated_authority \<Rightarrow> registry_snapshot" where
  "authority_registry a asset =
    (if registered_asset (current_operational a) = asset
     then Some (route_metadata (degree_state (current_operational a))) else None)"

context integrated_dosp_authority
begin

definition run_registered_meter :: "route_ticket \<Rightarrow> oracle_session_identity \<Rightarrow> nat
    \<Rightarrow> message_route \<Rightarrow> execution_request \<Rightarrow>      integrated_authority \<Rightarrow> (integrated_authority \<times> integrated_reply) option" where
  "run_registered_meter ticket session index route r a =
    (if ticket_authorizes (authority_registry a) flow_policy (binding_asset (request_binding r))
         ticket (transfer_commit (request_binding r)) then
      Some (execute_integrated_client (Meter_Credit session (ticket_metadata ticket) index route r) a)
     else None)"

lemma authorized_registry_meter_calls_the_native_meter:
  assumes "ticket_authorizes (authority_registry a) flow_policy (binding_asset (request_binding r))
    ticket (transfer_commit (request_binding r))"
  shows "run_registered_meter ticket session index route r a =
    Some (execute_integrated_client (Meter_Credit session (ticket_metadata ticket) index route r) a)"
  using assms by (simp only: run_registered_meter_def if_True)

theorem registry_routing_and_billing_use_the_same_request:
  assumes "run_registered_meter ticket session index route r a =
    Some (b, Credit_Result (Some (Credit_Metered charge)))"
  shows "ticket_asset ticket = binding_asset (request_binding r) \<and>
    ticket_initiator ticket = fst (binding_key (request_binding r)) \<and>
    authority_registry a (ticket_asset ticket) = Some (ticket_metadata ticket) \<and>
    (\<exists>cycle. consensus_binding cycle = binding_key (request_binding r) \<and>
       consensus_session cycle = session \<and> consensus_route_ticket cycle = ticket_metadata ticket \<and>
       consensus_commit_second cycle = consensus_now a \<and>
       consensus_publication_sequence cycle = next_publication_sequence a \<and>
       committed_cycles (metered_ledger b) = committed_cycles (metered_ledger a) @ [successful_cycle cycle charge])"
proof -
  have checks: "ticket_authorizes (authority_registry a) flow_policy (binding_asset (request_binding r))
    ticket (transfer_commit (request_binding r))"
    using assms by (auto simp: run_registered_meter_def split: if_splits)
  have execution: "execute_integrated_client (Meter_Credit session (ticket_metadata ticket) index route r) a =
    (b, Credit_Result (Some (Credit_Metered charge)))"
    using assms checks by (simp add: run_registered_meter_def)
  have fields: "ticket_asset ticket = binding_asset (request_binding r) \<and>
    ticket_initiator ticket = fst (binding_key (request_binding r)) \<and>
    authority_registry a (ticket_asset ticket) = Some (ticket_metadata ticket)"
    using checks by (auto simp: ticket_authorizes_def dest: issued_ticket_names_the_same_registry_record)
  from a_metered_command_uses_the_authority_clock_and_issued_sequence[OF execution] fields
  show ?thesis by blast
qed

end

definition observation_metadata :: cutover_metadata where
  "observation_metadata = \<lparr>required_level = Observation, chosen_path = Atomic,
     meter_version = 4, cutover_epoch = 8\<rparr>"

definition observation_registry :: registry_snapshot where
  "observation_registry = Map.empty(17 \<mapsto> observation_metadata)"

definition observation_ticket :: "nat \<Rightarrow> route_ticket" where
  "observation_ticket source = \<lparr>ticket_asset = 17, ticket_initiator = source, ticket_metadata = observation_metadata\<rparr>"

lemma observed_hub_reads_and_overprovision_cannot_write:
  "snd (route_and_execute observation_registry two_origin_policy 17 (observation_ticket 0) True
      (binding_state cutover_start) (Read_From 0 2)) = transition_result.Accepted (Read_Value 0)"
  "route_and_execute observation_registry two_origin_policy 17 (observation_ticket 1) True
      (binding_state cutover_start) (Commit_From 1 2 10) =
    (binding_state cutover_start, transition_result.Rejected ())"
  by (simp_all add: route_and_execute_def ticket_authorizes_def issue_route_ticket_def observation_metadata_def
      observation_registry_def observation_ticket_def two_origin_policy_def cutover_start_def)

definition joined_ticket :: "nat \<Rightarrow> cutover_metadata \<Rightarrow> route_ticket" where
  "joined_ticket origin meta = \<lparr>ticket_asset = 17, ticket_initiator = origin, ticket_metadata = meta\<rparr>"

lemma current_registry_ticket_reaches_actual_native_metering:
  "joined_dosp.run_registered_meter (joined_ticket 0 coupling_ticket) (17,7,3) 0 Bypass_Route
      (sample_request 17) joined_initial =
       Some (after_first_meter, Credit_Result (Some (Credit_Metered fixture_billed_usage)))"
proof -
  have actual: "joined_dosp.execute_integrated_client first_meter joined_initial =
       (after_first_meter, Credit_Result (Some (Credit_Metered fixture_billed_usage)))"
    using after_first_meter_def after_first_meter_shape(2) by (metis prod.collapse)
  have guard: "ticket_authorizes (authority_registry joined_initial) coupling_policy
    (binding_asset (request_binding (sample_request 17))) (joined_ticket 0 coupling_ticket)
    (transfer_commit (request_binding (sample_request 17)))"
    by (simp add: ticket_authorizes_def joined_ticket_def authority_registry_def issue_route_ticket_def
        joined_initial_def cycle_fixture_def meter_fixture_def coupling_ticket_def fixture_binding)
  show ?thesis using joined_dosp.authorized_registry_meter_calls_the_native_meter[OF guard,
      where session="(17,7,3)" and index=0 and route=Bypass_Route]
    by (simp only: joined_ticket_def route_ticket.select_convs actual)
qed

lemma router_rejects_same_path_but_superseded_ticket_and_initiator:
  "joined_dosp.run_registered_meter (joined_ticket 0 coupling_ticket) (17,7,3) 0 Bypass_Route
       (sample_request 23) before_second_meter = None"
  "joined_dosp.run_registered_meter (joined_ticket 2 (promoted_metadata 12 4)) (17,7,3) 0 Bypass_Route
       (sample_request 23) before_second_meter = None"
  by (simp_all add: joined_dosp.run_registered_meter_def ticket_authorizes_def
      issue_route_ticket_def authority_registry_def joined_ticket_def second_meter_operational_fields
      second_request_fields coupling_ticket_def promoted_metadata_def)

end
