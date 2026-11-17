theory DOSP_Commit_Defense
  imports DOSP_Registry_Defense
begin

datatype request_check = Current_Ticket | Wrong_Ticket | Illegal_Path | Wrong_Session

context integrated_dosp_authority
begin

definition check_recorded_request ::
  "route_ticket \<Rightarrow> oracle_session_identity \<Rightarrow> execution_request \<Rightarrow> integrated_authority \<Rightarrow> request_check" where
  "check_recorded_request ticket session r a =
    (let action = transfer_commit (request_binding r);
         asset = binding_asset (request_binding r);
         registry = authority_registry a
     in if issue_route_ticket registry asset (flow_initiator action) \<noteq> Some ticket then Wrong_Ticket
        else if \<not> ticket_authorizes registry flow_policy asset ticket action then Illegal_Path
        else if session \<noteq> active_session then Wrong_Session else Current_Ticket)"

lemma observed_request_check_matches_execution:
  "check_recorded_request ticket session r a \<in> {Wrong_Ticket, Illegal_Path} \<Longrightarrow>
     run_registered_meter ticket session index route r a = None"
  "check_recorded_request ticket session r a = Wrong_Session \<Longrightarrow>
     run_registered_meter ticket session index route r a = Some (a, Credit_Result None)"
  by (auto simp: check_recorded_request_def ticket_authorizes_def run_registered_meter_def Let_def split: if_splits)

lemma observed_check_is_a_condition_of_native_charge:
  assumes "run_registered_meter ticket session index route r a =
    Some (b, Credit_Result (Some (Credit_Metered charge)))"
  shows "check_recorded_request ticket session r a = Current_Ticket"
proof -
  have authorized: "ticket_authorizes (authority_registry a) flow_policy (binding_asset (request_binding r))
      ticket (transfer_commit (request_binding r))"
    using assms by (auto simp: run_registered_meter_def split: if_splits)
  have session: "session = active_session"
    using assms by (auto simp: run_registered_meter_def split: if_splits)
  show ?thesis using authorized session by (simp add: check_recorded_request_def ticket_authorizes_def Let_def)
qed

end

lemma recorded_replay_distinguishes_wrong_initiator_and_session:
  "joined_dosp.check_recorded_request (joined_ticket 2 (promoted_metadata 12 4)) (17,7,3)
    (sample_request 23) before_second_meter = Wrong_Ticket"
  "joined_dosp.check_recorded_request (joined_ticket 0 (promoted_metadata 12 4)) (17,9,3)
    (sample_request 23) before_second_meter = Wrong_Session"
  by (simp_all add: joined_dosp.check_recorded_request_def joined_ticket_def
      issue_route_ticket_def authority_registry_def ticket_authorizes_def second_request_fields
      second_meter_operational_fields promoted_metadata_def Let_def)

datatype protocol_stage = Binding | Verifying | Committing

datatype observed_fault =
    Client_Invalid_Transition | Client_Regulation_Failure | Client_Authority_Failure
  | Peer_Refusal | External_Reorganization | Driver_Refusal
  | Node_Outage | Consensus_Delay | Lock_Timeout | Undetermined_Fault

datatype abort_responsibility = Client_Abort | Counterparty_Abort | Network_Abort

fun blame_of :: "observed_fault \<Rightarrow> abort_responsibility" where
  "blame_of Client_Invalid_Transition = Client_Abort"
| "blame_of Client_Regulation_Failure = Client_Abort"
| "blame_of Client_Authority_Failure = Client_Abort"
| "blame_of Peer_Refusal = Counterparty_Abort"
| "blame_of External_Reorganization = Counterparty_Abort"
| "blame_of Driver_Refusal = Counterparty_Abort"
| "blame_of _ = Network_Abort"

fun resolved_responsibility :: "observed_fault list \<Rightarrow> abort_responsibility" where
  "resolved_responsibility [] = Network_Abort"
| "resolved_responsibility (first # reports) =
    (if list_all (\<lambda>report. blame_of report = blame_of first) reports then blame_of first else Network_Abort)"

lemma liability_requires_attributable_client_evidence:
  "resolved_responsibility reports = Client_Abort \<longleftrightarrow>
    reports \<noteq> [] \<and> (\<forall>report \<in> set reports. blame_of report = Client_Abort)"
  by (cases reports) (auto simp: list_all_iff split: if_splits)

record meter_schedule =
  degree_weight :: "operational_level \<Rightarrow> nat"
  fanout_base :: "operational_level \<Rightarrow> nat"
  fanout_slope :: nat
  payload_base :: nat
  failure_fraction :: nat

text \<open>The ledger uses a common fixed-point precision. The fanout slope
  and the failure fraction are numerators in that precision.\<close>

definition usage_units :: "nat \<Rightarrow> meter_schedule \<Rightarrow> operational_level \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "usage_units precision price level written leaves =
    degree_weight price level *
      (precision + fanout_slope price * (written - fanout_base price level)) *
      ((leaves + (payload_base price - 1)) div payload_base price)"

record accounted_cycle =
  accounted_attempt :: client_call_id
  accounted_binding :: nat
  accounted_session :: oracle_session_identity
  accounted_ticket :: route_ticket
  accounted_clock :: nat
  accounted_footprint :: "nat set"
  accounted_payload :: nat
  accounted_abort :: "abort_responsibility option"
  accounted_tariff :: nat
  accounted_schedule :: meter_schedule

definition charge_of :: "nat \<Rightarrow> accounted_cycle \<Rightarrow> nat" where
  "charge_of precision entry =
    (let price = accounted_schedule entry;
         usage = usage_units precision price (required_level (ticket_metadata (accounted_ticket entry)))
           (card (accounted_footprint entry)) (accounted_payload entry)
     in case accounted_abort entry of
          None \<Rightarrow> precision * usage
        | Some Client_Abort \<Rightarrow> failure_fraction price * usage
        | Some _ \<Rightarrow> 0)"

definition settlement_epoch :: "accounted_cycle \<Rightarrow> nat" where
  "settlement_epoch entry = billing_day (accounted_clock entry)"

definition observed_commit_charge ::
  "nat flow_policy \<Rightarrow> promotion_grants \<Rightarrow> registry_snapshot \<Rightarrow> protocol_stage \<Rightarrow>
    client_call_id \<Rightarrow> oracle_session_identity \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> route_ticket \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
    nat cutover_state \<Rightarrow> cutover_result \<Rightarrow> nat cutover_state \<Rightarrow>
    observed_fault list \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> meter_schedule option) \<Rightarrow> accounted_cycle option"
where
  "observed_commit_charge policy grants registry phase attempt session tariff clock ticket binding source target value healthy
      s reply t reports leaves versions =
    (let action = Commit_From source target value;
         emit = (\<lambda>price cause. \<lparr>accounted_attempt = attempt, accounted_binding = binding,
           accounted_session = session, accounted_ticket = ticket, accounted_clock = clock,
           accounted_footprint = participants action, accounted_payload = leaves,
           accounted_abort = cause, accounted_tariff = tariff, accounted_schedule = price\<rparr>)
     in if phase = Committing \<and> ticket_authorizes registry policy (fst session) ticket action \<and>
          cutover_step policy grants s (Commit_Binding binding (ticket_metadata ticket) source target value healthy) reply t
        then case versions tariff of
          None \<Rightarrow> None
        | Some price \<Rightarrow> (case reply of
            transition_result.Accepted Binding_Committed \<Rightarrow> Some (emit price None)
          | transition_result.Operational_Failure failure \<Rightarrow> Some (emit price (Some (resolved_responsibility reports)))
          | _ \<Rightarrow> None)
        else None)"

definition append_accounted_cycle :: "accounted_cycle list \<Rightarrow> accounted_cycle \<Rightarrow> accounted_cycle list" where
  "append_accounted_cycle history entry =
    (if accounted_attempt entry \<in> image accounted_attempt (set history) \<or>
         (accounted_abort entry = None \<and>
           (\<exists>old \<in> set history. accounted_abort old = None \<and> accounted_session old = accounted_session entry \<and>
             accounted_binding old = accounted_binding entry))
     then history else history @ [entry])"

definition invoice_usage :: "nat \<Rightarrow> oracle_session_identity \<Rightarrow> accounted_cycle list \<Rightarrow> nat" where
  "invoice_usage precision session history =
    sum_list (map (charge_of precision) (filter (\<lambda>entry. accounted_session entry = session) history))"

lemma repeated_attempt_does_not_charge_twice:
  "append_accounted_cycle (append_accounted_cycle history entry) entry = append_accounted_cycle history entry"
  by (auto simp: append_accounted_cycle_def)

lemma an_abort_does_not_consume_the_success_binding:
  assumes "accounted_abort failed \<noteq> None" "accounted_abort later = None"
    "accounted_attempt failed \<noteq> accounted_attempt later"
  shows "append_accounted_cycle [failed] later = [failed, later]"
  using assms by (simp add: append_accounted_cycle_def)

theorem accepted_invoice_row_has_one_registry_policy_and_one_commit_time:
  assumes "observed_commit_charge p grants registry phase attempt session tariff clock ticket binding source target value healthy
    s reply t reports leaves versions = Some entry"
  shows "phase = Committing \<and> ticket_metadata ticket = route_metadata s \<and>
    registry (fst session) = Some (route_metadata s) \<and>
    ticket_initiator ticket = source \<and> accounted_session entry = session \<and>
    accounted_binding entry = binding \<and> settlement_epoch entry = billing_day clock \<and>
    accounted_tariff entry = tariff \<and> versions tariff = Some (accounted_schedule entry)"
proof -
  have check: "ticket_authorizes registry p (fst session) ticket (Commit_From source target value)"
    and actual: "cutover_step p grants s (Commit_Binding binding (ticket_metadata ticket) source target value healthy) reply t"
    using assms by (auto simp: observed_commit_charge_def Let_def split: if_splits option.splits transition_result.splits cutover_ok.splits)
  have uses_current: "route_metadata s = ticket_metadata ticket"
    using assms actual
    by (auto simp: observed_commit_charge_def can_commit_def Let_def split: if_splits option.splits
        transition_result.splits cutover_ok.splits elim: cutover_step.cases)
  have registry: "registry (fst session) = Some (ticket_metadata ticket)" and initiator: "ticket_initiator ticket = source"
    using check by (auto simp: ticket_authorizes_def dest: issued_ticket_names_the_same_registry_record)
  show ?thesis using assms uses_current registry initiator
    by (auto simp: observed_commit_charge_def settlement_epoch_def Let_def
        split: if_splits option.splits transition_result.splits cutover_ok.splits)
qed

lemma binding_and_verification_publish_no_charge:
  "observed_commit_charge p grants registry Binding attempt session tariff clock ticket binding source target value healthy
    s reply t reports leaves versions = None"
  "observed_commit_charge p grants registry Verifying attempt session tariff clock ticket binding source target value healthy
    s reply t reports leaves versions = None"
  by (simp_all add: observed_commit_charge_def Let_def)

lemma before_commit_refusal_publishes_no_abort_charge:
  "observed_commit_charge p grants registry phase attempt session tariff clock ticket binding source target value healthy
    s (transition_result.Rejected reason) t reports leaves versions = None"
  by (simp add: observed_commit_charge_def Let_def split: if_splits option.splits)

lemma network_or_counterparty_never_increases_the_invoice:
  assumes "accounted_abort entry \<in> {Some Network_Abort, Some Counterparty_Abort}"
  shows "invoice_usage precision session (append_accounted_cycle history entry) = invoice_usage precision session history"
  using assms by (auto simp: charge_of_def invoice_usage_def append_accounted_cycle_def Let_def split: if_splits)

definition example_price :: meter_schedule where
  "example_price = \<lparr>degree_weight = level_rank, fanout_base = (\<lambda>_. 2), fanout_slope = 50,
    payload_base = 4, failure_fraction = 25\<rparr>"

definition example_versions :: "nat \<Rightarrow> meter_schedule option" where
  "example_versions = Map.empty(3 \<mapsto> example_price, 4 \<mapsto> example_price,
    5 \<mapsto> example_price\<lparr>failure_fraction := 50, degree_weight := level_rank(Atomic := 4)\<rparr>)"

definition soft_ticket :: route_ticket where
  "soft_ticket = joined_ticket 1 (route_metadata soft_start)"

definition soft_registry :: registry_snapshot where
  "soft_registry = Map.empty(17 \<mapsto> route_metadata soft_start)"

abbreviation observed_soft_failure :: "protocol_stage \<Rightarrow> observed_fault list \<Rightarrow> accounted_cycle option" where
  "observed_soft_failure phase reports \<equiv>
    observed_commit_charge two_origin_policy {(9,5)} soft_registry phase (34,9) (17,7,3) 4 86400
      soft_ticket 1 1 2 10 False soft_start
      (transition_result.Operational_Failure Partial_Write) partial_commit reports 5 example_versions"

definition observed_failure_row :: "abort_responsibility \<Rightarrow> accounted_cycle" where
  "observed_failure_row cause =
    \<lparr>accounted_attempt=(34,9), accounted_binding=1, accounted_session=(17,7,3),
      accounted_ticket=soft_ticket, accounted_clock=86400, accounted_footprint={1,2}, accounted_payload=5,
      accounted_abort=Some cause, accounted_tariff=4, accounted_schedule=example_price\<rparr>"

lemma charge_from_the_actual_partial_write_path:
  "observed_soft_failure Committing reports = Some (observed_failure_row (resolved_responsibility reports))"
proof -
  have check: "ticket_authorizes soft_registry two_origin_policy 17 soft_ticket (Commit_From 1 2 10)"
    by (simp add: soft_registry_def soft_ticket_def joined_ticket_def ticket_authorizes_def issue_route_ticket_def
        soft_start_def cutover_start_def old_plan_def two_origin_policy_def)
  have version: "example_versions 4 = Some example_price" by (simp add: example_versions_def)
  show ?thesis
    unfolding observed_commit_charge_def Let_def
    using check partial_soft_commit_occurs version
    by (simp add: soft_ticket_def joined_ticket_def observed_failure_row_def)
qed

theorem failed_commit_price_requires_attribution_and_survives_replay:
  "observed_soft_failure Binding [Client_Regulation_Failure] = None"
  "observed_soft_failure Verifying [Client_Regulation_Failure] = None"
  "observed_soft_failure Committing [Client_Regulation_Failure] = Some (observed_failure_row Client_Abort)"
  "observed_soft_failure Committing [Peer_Refusal] = Some (observed_failure_row Counterparty_Abort)"
  "observed_soft_failure Committing [Client_Regulation_Failure, Consensus_Delay] = Some (observed_failure_row Network_Abort)"
  "invoice_usage 100 (17,7,3) (append_accounted_cycle [observed_failure_row Client_Abort]
    (observed_failure_row Client_Abort)) = 10000"
  "invoice_usage 100 (17,7,3) [observed_failure_row Network_Abort] = 0"
  "settlement_epoch (observed_failure_row Client_Abort) = 1"
  unfolding binding_and_verification_publish_no_charge charge_from_the_actual_partial_write_path
  by (simp_all add: invoice_usage_def observed_failure_row_def append_accounted_cycle_def charge_of_def usage_units_def
      example_price_def soft_ticket_def joined_ticket_def soft_start_def old_plan_def cutover_start_def
      settlement_epoch_def billing_day_def Let_def)

end
