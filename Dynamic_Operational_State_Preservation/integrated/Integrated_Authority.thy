theory Integrated_Authority
  imports
    DOSP_EAB_Coupling.EAB_Cycle_Accounting
    DOSP_EAB_Coupling.EAB_Lifecycle_Cutover
    Evidence_Binding_Composition.Source_Call_Realization
begin

record integrated_authority =
  consensus_now :: nat
  next_publication_sequence :: nat
  metered_ledger :: cycle_ledger_state

datatype integrated_client_command =
    Prepare_Credit client_command
  | Reconcile_Current_Lock nat execution_request nat version_vector
  | Settle_Lock pending_resolution nat execution_request nat
  | Meter_Credit oracle_session_identity cutover_metadata nat message_route execution_request

datatype integrated_consensus_command =
    Advance_Consensus_Time nat
  | Confirm_Promotion_At_Consensus nat nat

datatype integrated_reply =
    Preparation_Result finality_reply
  | Lock_Result reservation_reply
  | Credit_Result "metered_credit_reply option"
  | Clock_Result bool
  | Promotion_Result cutover_result
  | Rejected_Preparation

fun credit_preparation :: "client_command \<Rightarrow> bool" where
  "credit_preparation (Client_Terminal cert) = True"
| "credit_preparation (Client_Protocol endpoint index (Reserve_Intent r versions duration)) = True"
| "credit_preparation (Client_Protocol endpoint index (Dispatch_Intent r generation versions)) = True"
| "credit_preparation (Client_Protocol endpoint index (Source_Intent r generation versions)) = True"
| "credit_preparation (Client_Protocol endpoint index (Certificate_Intent cert)) = True"
| "credit_preparation _ = False"

abbreviation current_operational :: "integrated_authority \<Rightarrow> metered_source_state" where
  "current_operational a \<equiv> operational_state (metered_ledger a)"

abbreviation current_publication_authority :: "integrated_authority \<Rightarrow> eab_primary_authority" where
  "current_publication_authority a \<equiv> source_authority (current_operational a)"

definition with_operational_state :: "metered_source_state \<Rightarrow> integrated_authority \<Rightarrow> integrated_authority" where
  "with_operational_state s a =
     a\<lparr>metered_ledger := (metered_ledger a)\<lparr>operational_state := s\<rparr>\<rparr>"

definition with_finality_core :: "finality_core \<Rightarrow> integrated_authority \<Rightarrow> integrated_authority" where
  "with_finality_core c a = with_operational_state
     ((current_operational a)\<lparr>source_authority := (current_publication_authority a)
       \<lparr>terminal_authority := c\<rparr>\<rparr>) a"

definition issued_receipt :: "integrated_authority \<Rightarrow> nat \<Rightarrow> eab_primary_receipt option" where
  "issued_receipt a seq =
    (case publication_slots (current_publication_authority a) seq of
       None \<Rightarrow> None
     | Some key \<Rightarrow> published_transfer_receipt key seq (credit_core (current_operational a)))"

type_synonym integrated_journal =
  "(integrated_authority, integrated_client_command, integrated_reply,
    integrated_consensus_command) durable_call_machine"

type_synonym integrated_recovery_candidate =
  "(integrated_authority, integrated_client_command, integrated_reply,
    integrated_consensus_command) recovery_candidate"

type_synonym integrated_event = "integrated_client_command + integrated_consensus_command"

fun integrated_call_program ::
  "nat \<Rightarrow> nat \<Rightarrow> integrated_event list \<Rightarrow>
    (integrated_client_command, integrated_consensus_command) client_call_action list"
where
  "integrated_call_program ns index [] = []"
| "integrated_call_program ns index (Inl command # events) =
    complete_call_program (ns, index) command @ integrated_call_program ns (Suc index) events"
| "integrated_call_program ns index (Inr input # events) =
    Apply_Authority_Input input # integrated_call_program ns index events"

locale integrated_dosp_authority = source_attestation +
  fixes flow_policy :: "nat flow_policy"
    and promotion_authorizations :: promotion_grants
    and active_session :: oracle_session_identity
begin

fun execute_integrated_client ::
  "integrated_client_command \<Rightarrow> integrated_authority \<Rightarrow> integrated_authority \<times> integrated_reply"
where
  "execute_integrated_client (Prepare_Credit command) a =
    (if credit_preparation command then
       let step = execute_finality_client command (credit_core (current_operational a))
       in (with_finality_core (fst step) a, Preparation_Result (snd step))
     else (a, Rejected_Preparation))"
| "execute_integrated_client (Reconcile_Current_Lock index r generation versions) a =
    (let endpoint = fst (binding_key (request_binding r));
         step = execute_finality_client (Client_Protocol endpoint index (Reconcile_Intent r generation versions))
                  (credit_core (current_operational a))
     in (with_finality_core (fst step) a, Lock_Result (reservation_outcome (snd step))))"
| "execute_integrated_client (Settle_Lock mode index r duration) a =
    (let s = current_operational a;
         step = resolve_cutover_lock mode (core_epoch (credit_core s)) index r duration s
     in (with_operational_state (fst step) a, Lock_Result (snd step)))"
| "execute_integrated_client (Meter_Credit session ticket index route r) a =
    (if session \<noteq> active_session then (a, Credit_Result None)
     else let cycle = \<lparr>consensus_session = session, consensus_binding = binding_key (request_binding r),
          consensus_publication_sequence = next_publication_sequence a,
          consensus_commit_second = consensus_now a, consensus_route_ticket = ticket\<rparr>;
         prior = set (map billed_consensus (committed_cycles (metered_ledger a)));
         step = meter_consensus_cycle flow_policy (insert cycle prior) cycle
           (core_epoch (credit_core (current_operational a))) index route r (metered_ledger a);
         next = (case snd step of Some (Credit_Metered entry) \<Rightarrow> Suc (next_publication_sequence a)
                   | _ \<Rightarrow> next_publication_sequence a)
     in (a\<lparr>metered_ledger := fst step, next_publication_sequence := next\<rparr>, Credit_Result (snd step)))"

fun execute_integrated_consensus ::
  "integrated_consensus_command \<Rightarrow> integrated_authority \<Rightarrow> integrated_authority \<times> integrated_reply"
where
  "execute_integrated_consensus (Advance_Consensus_Time t) a =
    (if t < consensus_now a then (a, Clock_Result False)
     else let step = execute_finality_client
                     (Client_Protocol (hub flow_policy) 0 (Time_Intent (t - consensus_now a)))
                     (credit_core (current_operational a))
          in ((with_finality_core (fst step) a)\<lparr>consensus_now := t\<rparr>, Clock_Result True))"
| "execute_integrated_consensus (Confirm_Promotion_At_Consensus epoch version) a =
    (let step = promote_settled_asset flow_policy promotion_authorizations epoch version (current_operational a)
     in (with_operational_state (fst step) a, Promotion_Result (snd step)))"

sublocale journal: durable_call_protocol execute_integrated_client execute_integrated_consensus .

fun run_integrated_events :: "integrated_event list \<Rightarrow> integrated_authority \<Rightarrow> integrated_authority" where
  "run_integrated_events [] a = a"
| "run_integrated_events (Inl command # events) a =
    run_integrated_events events (fst (execute_integrated_client command a))"
| "run_integrated_events (Inr input # events) a =
    run_integrated_events events (fst (execute_integrated_consensus input a))"

theorem integrated_event_program_uses_the_actual_journal_callbacks:
  assumes "source_call_ready ns index source"
  shows "call_authority_state (journal.run_calls (integrated_call_program ns index events) source) =
    run_integrated_events events (call_authority_state source)"
  using assms
proof (induction events arbitrary: index source)
  case Nil
  then show ?case by simp
next
  case (Cons event events)
  then show ?case
  proof (cases event)
    case (Inl command)
    let ?prefix = "complete_call_program (ns,index) command"
    note ready = journal.fresh_program_advances_the_identifier_supply[OF Cons.prems, where command=command]
    note callback = journal.fresh_program_uses_the_actual_callback(2)[OF Cons.prems, where command=command]
    show ?thesis
      unfolding Inl integrated_call_program.simps journal.run_calls_append run_integrated_events.simps
      by (simp only: Cons.IH[OF ready] callback)
  next
    case (Inr input)
    have ready: "source_call_ready ns index (journal.apply_authority_input input source)"
      using Cons.prems by (simp only: journal.primitive_authority_input_keeps_source_call_ready)
    have callback: "call_authority_state (journal.apply_authority_input input source) =
      fst (execute_integrated_consensus input (call_authority_state source))"
      by (simp add: journal.apply_authority_input_def Let_def)
    show ?thesis
      unfolding Inr integrated_call_program.simps journal.run_calls.simps journal.call_step.simps run_integrated_events.simps
      by (simp only: Cons.IH[OF ready] callback)
  qed
qed

definition install_from_current_integrated_replay ::
  "nat routing_grants \<Rightarrow> nat set \<Rightarrow> integrated_journal \<Rightarrow> integrated_recovery_candidate
    \<Rightarrow> nat \<Rightarrow> (nat recovery_state, nat repair_action, nat repair_result) step_rel"
where
  "install_from_current_integrated_replay grants governance source candidate seq s action reply t \<longleftrightarrow>
    (case journal.checked_current_replay source candidate of
       None \<Rightarrow> replica_repair action \<and> reply = transition_result.Operational_Failure Evidence_Unavailable \<and> t = s
     | Some restored \<Rightarrow>
         (case issued_receipt restored seq of
            None \<Rightarrow> replica_repair action \<and> reply = transition_result.Operational_Failure Evidence_Unavailable \<and> t = s
          | Some receipt \<Rightarrow>
              receipt_repair_step grants governance (current_publication_authority restored) receipt s action reply t))"

theorem a_metered_command_uses_the_authority_clock_and_issued_sequence:
  assumes step: "execute_integrated_client (Meter_Credit session ticket index route r) a =
      (b, Credit_Result (Some (Credit_Metered charge)))"
  shows "\<exists>cycle. session = active_session \<and> consensus_binding cycle = binding_key (request_binding r) \<and>
      consensus_session cycle = session \<and> consensus_route_ticket cycle = ticket \<and>
      consensus_commit_second cycle = consensus_now a \<and>
      consensus_publication_sequence cycle = next_publication_sequence a \<and>
      committed_cycles (metered_ledger b) =
         committed_cycles (metered_ledger a) @ [successful_cycle cycle charge] \<and>
      next_publication_sequence b = Suc (next_publication_sequence a)"
proof -
  let ?cycle = "\<lparr>consensus_session = session, consensus_binding = binding_key (request_binding r),
    consensus_publication_sequence = next_publication_sequence a,
    consensus_commit_second = consensus_now a, consensus_route_ticket = ticket\<rparr>"
  let ?prior = "set (map billed_consensus (committed_cycles (metered_ledger a)))"
  let ?epoch = "core_epoch (credit_core (current_operational a))"
  let ?step = "meter_consensus_cycle flow_policy (insert ?cycle ?prior) ?cycle ?epoch index route r (metered_ledger a)"
  have session: "session = active_session"
    using step by (cases "session = active_session") simp_all
  have reply: "snd ?step = Some (Credit_Metered charge)"
    and saved: "metered_ledger b = fst ?step"
    and advanced: "next_publication_sequence b = Suc (next_publication_sequence a)"
    using step session by (auto simp: Let_def split: option.splits metered_credit_reply.splits)
  have journaled: "?step = (metered_ledger b, Some (Credit_Metered charge))"
    using reply saved by (cases ?step) simp
  have charges: "committed_cycles (metered_ledger b) =
       committed_cycles (metered_ledger a) @ [successful_cycle ?cycle charge]"
    using consensus_cycle_records_the_same_success_on_its_billing_day[OF journaled] by blast
  show ?thesis
    by (rule exI[where x="?cycle"]) (simp add: session charges advanced)
qed

lemma another_session_cannot_meter:
  assumes "session \<noteq> active_session"
  shows "execute_integrated_client (Meter_Credit session ticket index route r) a = (a, Credit_Result None)"
  using assms by simp

lemma admitted_promotion_pins_the_new_session_version:
  assumes "execute_integrated_consensus (Confirm_Promotion_At_Consensus epoch version) a =
    (b, Promotion_Result (transition_result.Accepted Promotion_Finalized))"
  shows "route_metadata (degree_state (current_operational b)) = promoted_metadata epoch version"
    and "committed_cycles (metered_ledger b) = committed_cycles (metered_ledger a)"
  using assms by (auto simp: with_operational_state_def promote_settled_asset_def Let_def split: if_splits)

lemma generated_integrated_journal_recovers_its_own_issued_receipts:
  fixes actions :: "(integrated_client_command, integrated_consensus_command) client_call_action list"
    and initial :: integrated_authority
  defines "source \<equiv> journal.run_calls actions (initial_call_machine initial)"
  shows "map_option (\<lambda>a. issued_receipt a seq)
         (journal.checked_current_replay source (current_source_candidate source)) =
         Some (issued_receipt (call_authority_state source) seq)"
  unfolding source_def by (simp only: journal.generated_source_supplies_recovery_without_a_truth_flag option.map)

lemma generated_integrated_receipt_drives_repair_after_replay:
  fixes actions :: "(integrated_client_command, integrated_consensus_command) client_call_action list"
    and initial :: integrated_authority
  defines "source \<equiv> journal.run_calls actions (initial_call_machine initial)"
  assumes issued: "issued_receipt (call_authority_state source) seq = Some receipt"
  shows "install_from_current_integrated_replay grants governance source (current_source_candidate source) seq s action reply t =
    receipt_repair_step grants governance (current_publication_authority (call_authority_state source)) receipt s action reply t"
  using issued journal.generated_source_supplies_recovery_without_a_truth_flag[of actions initial]
  by (simp add: source_def install_from_current_integrated_replay_def)

lemma a_different_integrated_journal_cannot_install:
  assumes "candidate_entries candidate \<noteq> call_authority_log source"
  shows "\<not> install_from_current_integrated_replay grants governance source candidate seq s action
     (transition_result.Accepted (Installed job domain seq)) t"
  using assms by (simp add: install_from_current_integrated_replay_def journal.checked_current_replay_def)

end

end
