(* SPDX-License-Identifier: BSD-3-Clause *)
theory Sourced_Observations
  imports Source_Coupling Abstract_Response_Link
begin

record sourced_observation_state =
  observation_source :: source_coupling_state
  observation_caches :: "nat \<Rightarrow> endpoint_snapshot option"
  observation_history :: "nat \<Rightarrow> endpoint_snapshot option"
  observation_secondary :: "nat \<Rightarrow> nat"
  observation_source_available :: bool

definition sourced_view :: "sourced_observation_state \<Rightarrow> observed_finality" where
  "sourced_view s=\<lparr>observed_core=coupled_core(observation_source s),
    endpoint_cache=observation_caches s,historical_snapshots=observation_history s,
    secondary_progress=observation_secondary s\<rparr>"

definition install_sourced_view :: "source_coupling_state \<Rightarrow> observed_finality \<Rightarrow>
  sourced_observation_state \<Rightarrow> sourced_observation_state" where
  "install_sourced_view provider view s=s\<lparr>observation_source:=provider,
    observation_caches:=endpoint_cache view,observation_history:=historical_snapshots view,
    observation_secondary:=secondary_progress view\<rparr>"

definition initial_sourced_observations :: "(source_account \<Rightarrow> nat) \<Rightarrow> global_state
  \<Rightarrow> (nat \<Rightarrow> lock_context) \<Rightarrow> sourced_observation_state" where
  "initial_sourced_observations balances regulatory contexts=(let
    provider=initial_source_coupling balances regulatory contexts;
    view=initial_observed_finality(coupled_core provider)
    in \<lparr>observation_source=provider,observation_caches=endpoint_cache view,
      observation_history=historical_snapshots view,observation_secondary=secondary_progress view,
      observation_source_available=True\<rparr>)"

datatype sourced_request =
    Endpoint_Request observed_command
  | Inspect_Source_Units source_account
  | Inspect_Source_Effects

datatype sourced_environment =
    Source_Exchange bool bool controlled_source_command
  | Source_Receipt_Arrival bool source_certificate
  | View_Environment observed_environment
  | Set_Source_Availability bool

datatype sourced_reply =
    Sourced_Observation observed_reply
  | Sourced_Adapter source_coupling_reply
  | Source_Unit_Value nat
  | Source_Effect_History "transfer_binding list"

fun current_source_query :: "observed_command \<Rightarrow> source_account option" where
  "current_source_query(Read_Current endpoint(Source_Balance account))=Some account"
| "current_source_query(Read_Protected_Current endpoint index r(Source_Balance account))=Some account"
| "current_source_query _=None"

definition source_view_is_reconciled :: "source_coupling_state \<Rightarrow> source_account \<Rightarrow> bool" where
  "source_view_is_reconciled provider account \<longleftrightarrow>
    source_debit_gap(coupled_source provider)(core_parent(coupled_core provider))account=0 \<and>
    source_return_gap(coupled_source provider)(core_parent(coupled_core provider))account=0"

context source_attestation
begin

definition sourced_effect_call :: "nat \<Rightarrow> client_command \<Rightarrow> sourced_observation_state
  \<Rightarrow> sourced_observation_state \<times> sourced_reply" where
  "sourced_effect_call endpoint command s=(let view=sourced_view s in
    if \<not>current_cache_valid view endpoint then (s,Sourced_Observation Observation_Busy)
    else let result=source_coupling_step(Coupling_Client(observation_source_available s)command)(observation_source s)
    in case snd result of Coupling_Client_Reply reply \<Rightarrow>
      (install_sourced_view(fst result)(fst(store_core_result(coupled_core(fst result),reply)view))s,
        Sourced_Observation(Effect_Reply reply))
     | _ \<Rightarrow> (s,Sourced_Observation Observation_Rejected))"

definition sourced_application_read :: "nat \<Rightarrow> nat \<Rightarrow> execution_request \<Rightarrow> nat
  \<Rightarrow> sourced_observation_state \<Rightarrow> sourced_observation_state \<times> sourced_reply" where
  "sourced_application_read endpoint index r asset s=(let view=sourced_view s in
    if \<not>protected_read_access endpoint index r(Application_Value asset)view
    then (s,Sourced_Observation Observation_Rejected)
    else case current_query_reply endpoint(Application_Value asset)view of
      Current_Value revision value \<Rightarrow>
        (let result=source_coupling_step
          (Coupling_Client(observation_source_available s)(Client_Protocol endpoint index(Data_Read_Intent r)))
          (observation_source s)
         in case snd result of Coupling_Client_Reply(Protocol_Response(Value_Response amount)) \<Rightarrow>
           (install_sourced_view(fst result)
              (fst(store_core_result(coupled_core(fst result),Protocol_Response(Value_Response amount))view))s,
             Sourced_Observation(Current_Value revision value))
         | Coupling_Client_Reply reply \<Rightarrow>
           (install_sourced_view(fst result)(fst(store_core_result(coupled_core(fst result),reply)view))s,
             Sourced_Observation(Effect_Reply reply))
         | _ \<Rightarrow> (s,Sourced_Observation Observation_Rejected))
    | reply \<Rightarrow> (s,Sourced_Observation reply))"

fun execute_sourced_endpoint :: "observed_command \<Rightarrow> sourced_observation_state
  \<Rightarrow> sourced_observation_state \<times> sourced_reply" where
  "execute_sourced_endpoint(Execute_Current endpoint command)s=sourced_effect_call endpoint command s"
| "execute_sourced_endpoint(Read_Protected_Current endpoint index r(Application_Value asset))s=
    sourced_application_read endpoint index r asset s"
| "execute_sourced_endpoint command s=(let result=execute_observed command(sourced_view s)
    in (install_sourced_view(observation_source s)(fst result)s,Sourced_Observation(snd result)))"

fun execute_sourced_request :: "sourced_request \<Rightarrow> sourced_observation_state
  \<Rightarrow> sourced_observation_state \<times> sourced_reply" where
  "execute_sourced_request(Endpoint_Request command)s=
    (case current_source_query command of None \<Rightarrow> execute_sourced_endpoint command s
     | Some account \<Rightarrow>
       if \<not>observation_source_available s then (s,Sourced_Observation Observation_Unavailable)
       else if \<not>source_view_is_reconciled(observation_source s)account then (s,Sourced_Observation Observation_Busy)
       else execute_sourced_endpoint command s)"
| "execute_sourced_request(Inspect_Source_Units account)s=
    (s,if observation_source_available s
      then Source_Unit_Value(boundary_units(controlled_endpoint(coupled_source(observation_source s)))account)
      else Sourced_Observation Observation_Unavailable)"
| "execute_sourced_request Inspect_Source_Effects s=
    (s,if observation_source_available s
      then Source_Effect_History(boundary_effects(controlled_endpoint(coupled_source(observation_source s))))
      else Sourced_Observation Observation_Unavailable)"

fun execute_sourced_environment :: "sourced_environment \<Rightarrow> sourced_observation_state
  \<Rightarrow> sourced_observation_state \<times> sourced_reply" where
  "execute_sourced_environment(Source_Exchange arrived replied command)s=
    (let result=source_coupling_step(Coupling_Source arrived replied command)(observation_source s)
     in (s\<lparr>observation_source:=fst result\<rparr>,Sourced_Adapter(snd result)))"
| "execute_sourced_environment(Source_Receipt_Arrival available cert)s=
    (let result=source_coupling_step(Coupling_Issue available cert)(observation_source s)
     in (s\<lparr>observation_source:=fst result\<rparr>,Sourced_Adapter(snd result)))"
| "execute_sourced_environment(View_Environment(Replace_Current_Context endpoint c))s=
    (let result=source_coupling_step(Coupling_Environment endpoint c)(observation_source s)
     in case snd result of Coupling_Client_Reply reply \<Rightarrow>
       (install_sourced_view(fst result)(fst(store_core_result(coupled_core(fst result),reply)(sourced_view s)))s,
         Sourced_Observation(Effect_Reply reply))
      | _ \<Rightarrow> (s,Sourced_Adapter(snd result)))"
| "execute_sourced_environment(View_Environment input)s=
    (let result=execute_observed_environment input(sourced_view s)
     in (install_sourced_view(observation_source s)(fst result)s,Sourced_Observation(snd result)))"
| "execute_sourced_environment(Set_Source_Availability available)s=
    (s\<lparr>observation_source_available:=available\<rparr>,Sourced_Observation Cache_Refreshed)"

sublocale sourced_calls: durable_call_protocol execute_sourced_request execute_sourced_environment .

theorem sourced_endpoint_preserves_the_joint_source_contract:
  assumes "source_coupling_invariant balances(observation_source s)"
  shows "source_coupling_invariant balances(observation_source(fst(execute_sourced_endpoint command s)))"
proof (cases command)
  case (Read_Protected_Current endpoint index r query)
  show ?thesis using assms by (cases query)
    (auto simp: Read_Protected_Current sourced_application_read_def install_sourced_view_def Let_def
      intro: client_action_preserves_coupling_invariant
      split: if_splits observed_reply.splits source_coupling_reply.splits
        finality_reply.splits reservation_reply.splits)
qed (use assms in \<open>auto simp: sourced_effect_call_def install_sourced_view_def Let_def
  intro: client_action_preserves_coupling_invariant split: if_splits source_coupling_reply.splits\<close>)

theorem sourced_request_preserves_the_joint_source_contract:
  assumes "source_coupling_invariant balances(observation_source s)"
  shows "source_coupling_invariant balances(observation_source(fst(execute_sourced_request request s)))"
  using assms by (cases request)
    (auto intro: sourced_endpoint_preserves_the_joint_source_contract split: option.splits if_splits)

theorem sourced_environment_preserves_the_joint_source_contract:
  assumes "source_coupling_invariant balances(observation_source s)"
  shows "source_coupling_invariant balances(observation_source(fst(execute_sourced_environment input s)))"
proof (cases input)
  case (Source_Exchange arrived replied command)
  have actual: "source_coupling_invariant balances
    (fst(source_coupling_step(Coupling_Source arrived replied command)(observation_source s)))"
    by (rule source_coupling_step_preserves_invariant[OF assms])
  show ?thesis using actual by (simp add: Source_Exchange Let_def)
next
  case (Source_Receipt_Arrival available cert)
  have actual: "source_coupling_invariant balances
    (fst(source_coupling_step(Coupling_Issue available cert)(observation_source s)))"
    by (rule source_coupling_step_preserves_invariant[OF assms])
  show ?thesis using actual by (simp add: Source_Receipt_Arrival Let_def)
next
  case (View_Environment view_input)
  show ?thesis
  proof (cases view_input)
    case (Replace_Current_Context endpoint c)
    have actual: "source_coupling_invariant balances
      (fst(source_coupling_step(Coupling_Environment endpoint c)(observation_source s)))"
      by (rule source_coupling_step_preserves_invariant[OF assms])
    show ?thesis using actual
      by (simp add: View_Environment Replace_Current_Context install_sourced_view_def Let_def)
  qed (use assms View_Environment in \<open>simp_all add: install_sourced_view_def Let_def\<close>)
qed (use assms in simp)

lemma sourced_call_step_keeps_the_joint_contract:
  assumes "source_coupling_invariant balances(observation_source(call_authority_state m))"
  shows "source_coupling_invariant balances(observation_source(call_authority_state(sourced_calls.call_step action m)))"
  using assms by (cases action)
    (auto simp: sourced_calls.call_definitions Let_def
      intro: sourced_request_preserves_the_joint_source_contract sourced_environment_preserves_the_joint_source_contract
      split: option.splits prod.splits if_splits)

theorem all_sourced_call_histories_preserve_the_joint_contract:
  "source_coupling_invariant balances(observation_source(call_authority_state
    (sourced_calls.run_calls actions(initial_call_machine(initial_sourced_observations balances regulatory contexts)))))"
proof -
  have preserve: "\<And>m. source_coupling_invariant balances(observation_source(call_authority_state m)) \<Longrightarrow>
    source_coupling_invariant balances(observation_source(call_authority_state(sourced_calls.run_calls actions m)))"
    by (induction actions) (auto intro: sourced_call_step_keeps_the_joint_contract)
  show ?thesis by (rule preserve)
    (simp add: initial_call_machine_def initial_sourced_observations_def Let_def initial_source_coupling_invariant)
qed

theorem the_actual_sourced_call_consumer_has_exact_mirror_provenance:
  fixes actions :: "(sourced_request,sourced_environment) client_call_action list"
    and balances :: "source_account \<Rightarrow> nat" and regulatory :: global_state
    and contexts :: "nat \<Rightarrow> lock_context"
  defines "m \<equiv> sourced_calls.run_calls actions
    (initial_call_machine(initial_sourced_observations balances regulatory contexts))"
  shows "source_mirror_provenance
    (coupled_source(observation_source(call_authority_state m)))
    (core_parent(coupled_core(observation_source(call_authority_state m))))"
  using all_sourced_call_histories_preserve_the_joint_contract[of balances actions regulatory contexts]
  unfolding m_def source_coupling_invariant_def by blast

theorem sourced_requests_complete_at_most_once:
  "distinct(completion_ids(call_history(sourced_calls.run_calls actions(initial_call_machine initial))))"
  using sourced_calls.at_most_one_authority_execution_and_completion[of actions initial] by simp

theorem sourced_current_view_uses_the_coupled_authority:
  "observed_core(sourced_view s)=coupled_core(observation_source s)"
  by (simp add: sourced_view_def)

theorem a_source_gap_cannot_be_a_successful_current_source_response:
  assumes "current_source_query command=Some account"
    "\<not>source_view_is_reconciled(observation_source s)account"
  shows "snd(execute_sourced_request(Endpoint_Request command)s)\<noteq>
    Sourced_Observation(Current_Value revision value)"
  using assms by simp

theorem reconciled_source_view_is_one_resource:
  assumes source: "controlled_source_invariant balances(coupled_source(observation_source s))"
    and parent: "financial_history_agreement balances(core_parent(coupled_core(observation_source s)))"
    and reconciled: "source_view_is_reconciled(observation_source s)account"
  shows "boundary_units(controlled_endpoint(coupled_source(observation_source s)))account=
    source_units(machine_state(core_parent(observed_core(sourced_view s))))account"
  using synchronized_views_have_equal_available_units[where account=account, OF source parent] reconciled
  by (simp add: source_view_is_reconciled_def sourced_view_def)

theorem a_missing_source_witness_rejects_the_actual_effect_entrypoint:
  assumes "\<not>coupling_guard(observation_source_available s)(observation_source s)command"
  shows "snd(sourced_effect_call endpoint command s)\<noteq>Sourced_Observation(Effect_Reply reply)"
  using assms by (simp add: sourced_effect_call_def coupling_client_step_def Let_def)

text \<open>The endpoint effect and protected application-read paths use the
  same source-coupling dispatcher before committing their actual core result.
  Pure public, historical and raw observations retain their separate semantics.
  A current source-unit query additionally checks the actual debit and return
  reconciliation gaps; a local mirror is not silently substituted for a
  physically different source balance. Raw source units and source-effect
  history have their own operations and are not deleted to obtain atomicity.
  The durable call protocol supplies the same invocation, once, response-loss
  and completion machinery to these requests. Physical source authentication,
  sender-journal durability and the authority read remain explicit obligations.\<close>

end

end
