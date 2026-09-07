(* SPDX-License-Identifier: BSD-3-Clause *)
theory Sourced_Response_Link
  imports Sourced_Observations
begin

definition sourced_response_alpha :: "sourced_observation_state \<Rightarrow> observation_target" where
  "sourced_response_alpha s=observation_alpha(coupled_core(observation_source s))"

definition sourced_history_is_capture :: "sourced_observation_state \<Rightarrow> sourced_observation_state \<Rightarrow> bool" where
  "sourced_history_is_capture before after \<longleftrightarrow>
    (\<forall>revision cache. observation_history after revision=Some cache \<longrightarrow>
      observation_history before revision=Some cache \<or>
      (cache=capture_snapshot(coupled_core(observation_source after)) \<and> snapshot_revision cache=revision))"

lemma sourced_history_refl [simp]: "sourced_history_is_capture s s"
  by (simp add: sourced_history_is_capture_def)

lemma sourced_install_keeps_existing_history:
  assumes "historical_snapshots view=observation_history s"
  shows "sourced_history_is_capture s(install_sourced_view provider view s)"
  using assms by (simp add: sourced_history_is_capture_def install_sourced_view_def)

lemma sourced_install_captures_its_actual_provider:
  "sourced_history_is_capture s
    (install_sourced_view provider(fst(store_core_result(coupled_core provider,reply)(sourced_view s)))s)"
  by (auto simp: sourced_history_is_capture_def install_sourced_view_def store_core_result_def
      sourced_view_def Let_def captured_snapshot_has_the_source_revision split: if_splits)

lemma sourced_current_query_has_independent_fields:
  assumes response: "current_query_reply endpoint query(sourced_view s)=Current_Value revision payload"
  shows "payload=abstract_query_value query(sourced_response_alpha s) \<and>
    revision=target_revision(sourced_response_alpha s)"
proof -
  have concrete: "payload=stored_query query(capture_snapshot(coupled_core(observation_source s)))"
    and cut: "revision=core_epoch(coupled_core(observation_source s))"
    using response by (auto simp: current_query_reply_def current_cache_valid_def
        sourced_view_def capture_snapshot_def split: option.splits if_splits)
  have readers: "stored_query query(capture_snapshot(coupled_core(observation_source s))) =
    abstract_query_value query(observation_alpha(coupled_core(observation_source s)))"
    by (rule independent_stored_and_abstract_query_readers_agree[OF captured_state_supplies_snapshot_correspondence])
  show ?thesis using concrete cut readers
    by (simp add: sourced_response_alpha_def observation_alpha_def)
qed

context source_attestation
begin

section \<open>Current Replies Follow the Actual Sourced Callback\<close>

lemma sourced_application_current_uses_its_actual_query:
  assumes "snd(sourced_application_read endpoint index r asset s)=Sourced_Observation(Current_Value revision payload)"
  shows "current_query_reply endpoint(Application_Value asset)(sourced_view s)=Current_Value revision payload"
  using assms
  by (auto simp: sourced_application_read_def Let_def
      split: if_splits observed_reply.splits source_coupling_reply.splits finality_reply.splits reservation_reply.splits)

lemma sourced_current_endpoint_has_an_actual_query_origin:
  assumes "snd(execute_sourced_endpoint command s)=Sourced_Observation(Current_Value revision payload)"
  shows "snd(execute_observed command(sourced_view s))=Current_Value revision payload \<or>
    (\<exists>endpoint index r asset. command=Read_Protected_Current endpoint index r(Application_Value asset) \<and>
      snd(sourced_application_read endpoint index r asset s)=Sourced_Observation(Current_Value revision payload))"
proof (cases command)
  case (Read_Protected_Current endpoint index r query)
  then show ?thesis using assms by (cases query) (auto simp: Let_def)
qed (use assms in \<open>auto simp: sourced_effect_call_def Let_def split: source_coupling_reply.splits if_splits\<close>)

theorem sourced_current_endpoint_has_independent_abstract_fields:
  assumes response: "snd(execute_sourced_endpoint command s)=Sourced_Observation(Current_Value revision payload)"
  shows "\<exists>query. command_query command=Some query \<and>
    payload=abstract_query_value query(sourced_response_alpha s) \<and>
    revision=target_revision(sourced_response_alpha s)"
proof -
  have origin: "snd(execute_observed command(sourced_view s))=Current_Value revision payload \<or>
    (\<exists>endpoint index r asset. command=Read_Protected_Current endpoint index r(Application_Value asset) \<and>
      snd(sourced_application_read endpoint index r asset s)=Sourced_Observation(Current_Value revision payload))"
    by (rule sourced_current_endpoint_has_an_actual_query_origin[OF response])
  show ?thesis
  proof (cases "snd(execute_observed command(sourced_view s))=Current_Value revision payload")
    case True
    show ?thesis using any_successful_current_command_has_an_independent_abstract_query[OF True]
      by (simp add: sourced_response_alpha_def sourced_view_def)
  next
    case False
    obtain endpoint index r asset where command:
      "command=Read_Protected_Current endpoint index r(Application_Value asset)"
      and application: "snd(sourced_application_read endpoint index r asset s)=
        Sourced_Observation(Current_Value revision payload)"
      using origin False by blast
    have query: "current_query_reply endpoint(Application_Value asset)(sourced_view s)=Current_Value revision payload"
      by (rule sourced_application_current_uses_its_actual_query[OF application])
    show ?thesis using sourced_current_query_has_independent_fields[OF query]
      by (auto simp: command)
  qed
qed

lemma sourced_current_request_reaches_its_endpoint:
  assumes "snd(execute_sourced_request request s)=Sourced_Observation(Current_Value revision payload)"
  shows "\<exists>command. request=Endpoint_Request command \<and>
    snd(execute_sourced_endpoint command s)=Sourced_Observation(Current_Value revision payload) \<and>
    (\<forall>account. current_source_query command=Some account \<longrightarrow>
      observation_source_available s \<and> source_view_is_reconciled(observation_source s)account)"
  using assms by (cases request) (auto split: option.splits if_splits)

theorem sourced_current_request_preserves_its_fields_and_source_guards:
  assumes "snd(execute_sourced_request request s)=Sourced_Observation(Current_Value revision payload)"
  shows "\<exists>command query. request=Endpoint_Request command \<and> command_query command=Some query \<and>
    payload=abstract_query_value query(sourced_response_alpha s) \<and>
    revision=target_revision(sourced_response_alpha s) \<and>
    (\<forall>account. current_source_query command=Some account \<longrightarrow>
      observation_source_available s \<and> source_view_is_reconciled(observation_source s)account)"
  using sourced_current_request_reaches_its_endpoint[OF assms]
    sourced_current_endpoint_has_independent_abstract_fields by blast

lemma current_source_unavailability_is_an_actual_completed_reply:
  assumes "current_source_query command=Some account" "\<not>observation_source_available s"
  shows "execute_sourced_request(Endpoint_Request command)s=(s,Sourced_Observation Observation_Unavailable)"
  using assms by simp

lemma current_source_gap_is_an_actual_busy_reply:
  assumes "current_source_query command=Some account" "observation_source_available s"
    "\<not>source_view_is_reconciled(observation_source s)account"
  shows "execute_sourced_request(Endpoint_Request command)s=(s,Sourced_Observation Observation_Busy)"
  using assms by simp

section \<open>Historical Snapshots Come from Sourced Execution\<close>

lemma sourced_endpoint_history_is_capture:
  "sourced_history_is_capture s(fst(execute_sourced_endpoint command s))"
proof (cases command)
  case (Read_Protected_Current endpoint index r query)
  then show ?thesis by (cases query)
    (auto simp: sourced_application_read_def execute_protected_current_def sourced_view_def
        install_sourced_view_def sourced_history_is_capture_def store_core_result_def Let_def
        captured_snapshot_has_the_source_revision
      split: if_splits observed_reply.splits source_coupling_reply.splits finality_reply.splits reservation_reply.splits)
qed (auto simp: sourced_effect_call_def Let_def sourced_view_def install_sourced_view_def
    sourced_history_is_capture_def store_core_result_def captured_snapshot_has_the_source_revision
    split: if_splits source_coupling_reply.splits)

lemma sourced_request_history_is_capture:
  "sourced_history_is_capture s(fst(execute_sourced_request request s))"
  by (cases request) (auto intro: sourced_endpoint_history_is_capture split: option.splits if_splits)

lemma sourced_environment_history_is_capture:
  "sourced_history_is_capture s(fst(execute_sourced_environment input s))"
proof (cases input)
  case (View_Environment view_input)
  then show ?thesis by (cases view_input)
    (auto simp: Let_def sourced_view_def install_sourced_view_def sourced_history_is_capture_def
        store_core_result_def captured_snapshot_has_the_source_revision split: source_coupling_reply.splits if_splits)
qed (auto simp: sourced_history_is_capture_def Let_def)

fun sourced_response_entry_after :: "(sourced_request,sourced_reply,sourced_environment) authority_call_entry
  \<Rightarrow> sourced_observation_state \<Rightarrow> sourced_observation_state" where
  "sourced_response_entry_after(Authority_Executed call_id request reply)s=fst(execute_sourced_request request s)"
| "sourced_response_entry_after(Authority_Input input reply)s=fst(execute_sourced_environment input s)"

lemma sourced_response_entry_captures_history:
  "sourced_history_is_capture s(sourced_response_entry_after entry s)"
  by (cases entry) (simp_all add: sourced_request_history_is_capture sourced_environment_history_is_capture)

lemma sourced_response_replay_cons:
  "sourced_calls.replay_call_authority(entry#entries)s=
    sourced_calls.replay_call_authority entries(sourced_response_entry_after entry s)"
  by (cases entry)
    (simp_all only: sourced_calls.replay_call_authority.simps sourced_response_entry_after.simps)

fun sourced_response_states :: "(sourced_request,sourced_reply,sourced_environment) authority_call_entry list
  \<Rightarrow> sourced_observation_state \<Rightarrow> sourced_observation_state list" where
  "sourced_response_states [] s=[s]"
| "sourced_response_states(entry#entries)s=s#sourced_response_states entries(sourced_response_entry_after entry s)"

lemma sourced_initial_state_is_a_cut [simp]: "s\<in>set(sourced_response_states entries s)"
  by (cases entries) simp_all

lemma sourced_replayed_history_has_a_real_origin:
  assumes "observation_history(sourced_calls.replay_call_authority entries initial)revision=Some cache"
  shows "observation_history initial revision=Some cache \<or>
    (\<exists>cut\<in>set(sourced_response_states entries initial).
      cache=capture_snapshot(coupled_core(observation_source cut)) \<and> snapshot_revision cache=revision)"
  using assms
proof (induction entries arbitrary:initial)
  case Nil
  then show ?case by simp
next
  case (Cons entry entries)
  let ?following = "sourced_response_entry_after entry initial"
  have stored: "observation_history(sourced_calls.replay_call_authority entries ?following)revision=Some cache"
    using Cons.prems by (simp only: sourced_response_replay_cons)
  have tail: "observation_history ?following revision=Some cache \<or>
    (\<exists>cut\<in>set(sourced_response_states entries ?following).
      cache=capture_snapshot(coupled_core(observation_source cut)) \<and> snapshot_revision cache=revision)"
    by (rule Cons.IH[OF stored])
  have created: "observation_history ?following revision=Some cache \<Longrightarrow>
    observation_history initial revision=Some cache \<or>
    (cache=capture_snapshot(coupled_core(observation_source ?following)) \<and> snapshot_revision cache=revision)"
    using sourced_response_entry_captures_history[of initial entry]
    unfolding sourced_history_is_capture_def by blast
  show ?case using tail created sourced_initial_state_is_a_cut[of ?following entries] by auto
qed

lemma sourced_cut_is_an_actual_replay_prefix:
  assumes "source_cut\<in>set(sourced_response_states entries initial)"
  shows "\<exists>index\<le>length entries. source_cut=sourced_calls.replay_call_authority(take index entries)initial"
  using assms
proof (induction entries arbitrary:initial)
  case Nil
  then show ?case by simp
next
  case (Cons entry entries)
  show ?case
  proof (cases "source_cut=initial")
    case True
    show ?thesis by (intro exI[where x=0]) (simp add: True)
  next
    case False
    have member: "source_cut\<in>set(sourced_response_states entries(sourced_response_entry_after entry initial))"
      using Cons.prems False by simp
    obtain index where bound: "index\<le>length entries"
      and at: "source_cut=sourced_calls.replay_call_authority(take index entries)(sourced_response_entry_after entry initial)"
      using Cons.IH[OF member] by blast
    show ?thesis by (intro exI[where x="Suc index"])
      (simp add: bound at sourced_response_replay_cons)
  qed
qed

theorem sourced_snapshot_has_an_actual_replay_prefix:
  assumes stored: "observation_history(sourced_calls.replay_call_authority entries
    (initial_sourced_observations balances regulatory contexts))revision=Some cache"
  shows "\<exists>index\<le>length entries.
    cache=capture_snapshot(coupled_core(observation_source(sourced_calls.replay_call_authority(take index entries)
      (initial_sourced_observations balances regulatory contexts)))) \<and> snapshot_revision cache=revision"
proof -
  let ?initial = "initial_sourced_observations balances regulatory contexts"
  have origin: "observation_history ?initial revision=Some cache \<or>
    (\<exists>cut\<in>set(sourced_response_states entries ?initial).
      cache=capture_snapshot(coupled_core(observation_source cut)) \<and> snapshot_revision cache=revision)"
    by (rule sourced_replayed_history_has_a_real_origin[OF stored])
  show ?thesis
  proof (cases "observation_history ?initial revision=Some cache")
    case True
    have snapshot: "cache=capture_snapshot(coupled_core(observation_source ?initial))"
      and revision: "snapshot_revision cache=revision"
      using True by (auto simp: initial_sourced_observations_def initial_observed_finality_def Let_def
          captured_snapshot_has_the_source_revision split: if_splits)
    have initial_revision: "snapshot_revision(capture_snapshot(coupled_core(observation_source ?initial)))=revision"
      using revision by (simp only: snapshot)
    show ?thesis by (intro exI[where x=0]) (simp add: snapshot initial_revision)
  next
    case False
    obtain cut where member: "cut\<in>set(sourced_response_states entries ?initial)"
      and snapshot: "cache=capture_snapshot(coupled_core(observation_source cut))"
      and revision: "snapshot_revision cache=revision" using origin False by blast
    obtain index where bound: "index\<le>length entries"
      and at: "cut=sourced_calls.replay_call_authority(take index entries)?initial"
      using sourced_cut_is_an_actual_replay_prefix[OF member] by blast
    show ?thesis using bound at snapshot revision by blast
  qed
qed

lemma sourced_historical_endpoint_uses_the_actual_history:
  assumes "snd(execute_sourced_endpoint command s)=Sourced_Observation(Historical_Value revision payload)"
  shows "\<exists>query cache. command_query command=Some query \<and>
    requested_history_revision command=Some revision \<and> observation_history s revision=Some cache \<and>
    payload=stored_query query cache"
proof (cases command)
  case (Read_Protected_Current endpoint index r query)
  then show ?thesis using assms by (cases query)
    (auto simp: sourced_application_read_def execute_protected_current_def current_query_reply_def
        sourced_view_def Let_def split: option.splits if_splits observed_reply.splits
          source_coupling_reply.splits finality_reply.splits reservation_reply.splits)
qed (use assms in \<open>auto simp: sourced_effect_call_def sourced_view_def Let_def
    historical_query_reply_def current_query_reply_def
    split: option.splits if_splits source_coupling_reply.splits\<close>)

lemma sourced_historical_request_uses_the_actual_history:
  assumes "snd(execute_sourced_request request s)=Sourced_Observation(Historical_Value revision payload)"
  shows "\<exists>command query cache. request=Endpoint_Request command \<and> command_query command=Some query \<and>
    requested_history_revision command=Some revision \<and> observation_history s revision=Some cache \<and>
    payload=stored_query query cache"
  using assms sourced_historical_endpoint_uses_the_actual_history
  by (cases request) (auto split: option.splits if_splits)

theorem sourced_historical_reply_has_an_independent_past_value:
  assumes response: "snd(execute_sourced_request request(sourced_calls.replay_call_authority entries
    (initial_sourced_observations balances regulatory contexts)))=Sourced_Observation(Historical_Value revision payload)"
  shows "\<exists>command query index. index\<le>length entries \<and> request=Endpoint_Request command \<and>
    command_query command=Some query \<and> requested_history_revision command=Some revision \<and>
    payload=abstract_query_value query(sourced_response_alpha(sourced_calls.replay_call_authority(take index entries)
      (initial_sourced_observations balances regulatory contexts))) \<and>
    target_revision(sourced_response_alpha(sourced_calls.replay_call_authority(take index entries)
      (initial_sourced_observations balances regulatory contexts)))=revision"
proof -
  let ?initial = "initial_sourced_observations balances regulatory contexts"
  obtain command query cache where request: "request=Endpoint_Request command"
    and query: "command_query command=Some query" and requested: "requested_history_revision command=Some revision"
    and stored: "observation_history(sourced_calls.replay_call_authority entries ?initial)revision=Some cache"
    and payload: "payload=stored_query query cache"
    using sourced_historical_request_uses_the_actual_history[OF response] by blast
  obtain index where bound: "index\<le>length entries"
    and snapshot: "cache=capture_snapshot(coupled_core(observation_source
      (sourced_calls.replay_call_authority(take index entries)?initial)))"
    and revision: "snapshot_revision cache=revision"
    using sourced_snapshot_has_an_actual_replay_prefix[OF stored] by blast
  have readers: "stored_query query cache=abstract_query_value query
    (sourced_response_alpha(sourced_calls.replay_call_authority(take index entries)?initial))"
    unfolding snapshot sourced_response_alpha_def
    by (rule independent_stored_and_abstract_query_readers_agree[OF captured_state_supplies_snapshot_correspondence])
  have at_revision: "target_revision(sourced_response_alpha(sourced_calls.replay_call_authority(take index entries)?initial))=revision"
    using revision by (simp add: snapshot sourced_response_alpha_def observation_alpha_def
        captured_snapshot_has_the_source_revision)
  show ?thesis using bound request query requested payload readers at_revision by blast
qed

section \<open>Raw and Operational Replies Retain Their Distinct Data\<close>

lemma sourced_raw_query_has_its_independent_value:
  "snd(execute_sourced_request(Endpoint_Request(Read_Raw query))s)=
    Sourced_Observation(Raw_Value(abstract_query_value query(sourced_response_alpha s)))"
proof -
  have actual: "snd(execute_sourced_request(Endpoint_Request(Read_Raw query))s)=
    Sourced_Observation(Raw_Value(stored_query query(capture_snapshot(coupled_core(observation_source s)))))"
    by (simp add: sourced_view_def Let_def)
  have readers: "stored_query query(capture_snapshot(coupled_core(observation_source s))) =
    abstract_query_value query(observation_alpha(coupled_core(observation_source s)))"
    by (rule independent_stored_and_abstract_query_readers_agree[OF captured_state_supplies_snapshot_correspondence])
  show ?thesis by (simp only: actual readers sourced_response_alpha_def)
qed

lemma sourced_operational_query_has_its_exact_fields:
  "snd(execute_sourced_request(Endpoint_Request(Read_Operation endpoint key))s)=
    Sourced_Observation(Operation_Status(target_phase(sourced_response_alpha s)key)(observation_secondary s endpoint))"
  "snd(execute_sourced_request(Endpoint_Request Read_Raw_Journal)s)=
    Sourced_Observation(Journal_Events(target_journal(sourced_response_alpha s)))"
  by (simp_all add: sourced_view_def sourced_response_alpha_def observation_alpha_def Let_def)

lemma sourced_physical_inspection_retains_source_availability:
  "snd(execute_sourced_request(Inspect_Source_Units account)s)=
    (if observation_source_available s then Source_Unit_Value
      (boundary_units(controlled_endpoint(coupled_source(observation_source s)))account)
     else Sourced_Observation Observation_Unavailable)"
  "snd(execute_sourced_request Inspect_Source_Effects s)=
    (if observation_source_available s then Source_Effect_History
      (boundary_effects(controlled_endpoint(coupled_source(observation_source s))))
     else Sourced_Observation Observation_Unavailable)"
  by simp_all

section \<open>Completed Sourced Replies Have Actual Indexed Executions\<close>

theorem every_completed_sourced_reply_has_its_actual_source:
  fixes actions :: "(sourced_request,sourced_environment) client_call_action list"
    and initial :: sourced_observation_state
  defines "m \<equiv> sourced_calls.run_calls actions(initial_call_machine initial)"
  assumes completed: "call_completions m call_id=Some reply"
  shows "\<exists>request index. call_authority_results m call_id=Some(request,reply,index) \<and>
    index<length(call_authority_log m) \<and>
    reply=snd(execute_sourced_request request
      (sourced_calls.replay_call_authority(take index(call_authority_log m))initial))"
proof -
  have life: "call_lifecycle_contract m" unfolding m_def by (rule sourced_calls.generated_call_lifecycle_contract)
  obtain request index where found: "call_authority_results m call_id=Some(request,reply,index)"
    using completed_result_has_source[OF life completed] by blast
  have cache: "authority_cache_contract m" and replay: "sourced_calls.authority_replay_contract m"
    using sourced_calls.generated_call_contracts[of actions initial] by (simp_all add: m_def)
  have genesis: "call_genesis m=initial" by (simp add: m_def initial_call_machine_def)
  have bound: "index<length(call_authority_log m)" by (rule authority_cache_lookup(1)[OF cache found])
  have actual: "reply=snd(execute_sourced_request request
    (sourced_calls.replay_call_authority(take index(call_authority_log m))initial))"
    using sourced_calls.cached_result_is_the_actual_indexed_reply[OF cache replay found] by (simp only: genesis)
  show ?thesis using found bound actual by blast
qed

theorem completed_sourced_known_request_has_its_actual_source:
  fixes actions :: "(sourced_request,sourced_environment) client_call_action list"
    and initial :: sourced_observation_state
  defines "m \<equiv> sourced_calls.run_calls actions(initial_call_machine initial)"
  assumes invoked: "call_invocations m call_id=Some(request,began)"
    and completed: "call_completions m call_id=Some reply"
  shows "\<exists>index. call_authority_results m call_id=Some(request,reply,index) \<and>
    index<length(call_authority_log m) \<and>
    reply=snd(execute_sourced_request request
      (sourced_calls.replay_call_authority(take index(call_authority_log m))initial))"
proof -
  have completed_run: "call_completions(sourced_calls.run_calls actions(initial_call_machine initial))call_id=Some reply"
    using completed by (simp only: m_def)
  obtain actual_request index where found: "call_authority_results m call_id=Some(actual_request,reply,index)"
    and bound: "index<length(call_authority_log m)"
    and actual: "reply=snd(execute_sourced_request actual_request
      (sourced_calls.replay_call_authority(take index(call_authority_log m))initial))"
    using every_completed_sourced_reply_has_its_actual_source[OF completed_run] unfolding m_def by blast
  have life: "call_lifecycle_contract m" unfolding m_def by (rule sourced_calls.generated_call_lifecycle_contract)
  obtain actual_began where original: "call_invocations m call_id=Some(actual_request,actual_began)"
    using source_result_has_invocation[OF life found] by blast
  have same: "actual_request=request" using invoked original by simp
  show ?thesis using found bound actual by (simp only: same) blast
qed

theorem completed_sourced_raw_and_operational_queries_keep_their_fields:
  fixes actions :: "(sourced_request,sourced_environment) client_call_action list"
    and initial :: sourced_observation_state
  defines "m \<equiv> sourced_calls.run_calls actions(initial_call_machine initial)"
  assumes invoked: "call_invocations m call_id=Some(Endpoint_Request command,began)"
    and completed: "call_completions m call_id=Some(Sourced_Observation reply)"
  shows "\<exists>index. call_authority_results m call_id=Some(Endpoint_Request command,Sourced_Observation reply,index) \<and>
    index<length(call_authority_log m) \<and>
    (\<forall>query. command=Read_Raw query \<longrightarrow>
      reply=Raw_Value(abstract_query_value query(sourced_response_alpha
        (sourced_calls.replay_call_authority(take index(call_authority_log m))initial)))) \<and>
    (\<forall>endpoint key. command=Read_Operation endpoint key \<longrightarrow>
      reply=Operation_Status(target_phase(sourced_response_alpha
        (sourced_calls.replay_call_authority(take index(call_authority_log m))initial))key)
        (observation_secondary(sourced_calls.replay_call_authority(take index(call_authority_log m))initial)endpoint)) \<and>
    (command=Read_Raw_Journal \<longrightarrow>
      reply=Journal_Events(target_journal(sourced_response_alpha
        (sourced_calls.replay_call_authority(take index(call_authority_log m))initial))))"
proof -
  have invoked_run: "call_invocations(sourced_calls.run_calls actions(initial_call_machine initial))call_id=
    Some(Endpoint_Request command,began)" using invoked by (simp only: m_def)
  have completed_run: "call_completions(sourced_calls.run_calls actions(initial_call_machine initial))call_id=
    Some(Sourced_Observation reply)" using completed by (simp only: m_def)
  obtain index where found:
    "call_authority_results m call_id=Some(Endpoint_Request command,Sourced_Observation reply,index)"
    and bound: "index<length(call_authority_log m)"
    and actual: "Sourced_Observation reply=snd(execute_sourced_request(Endpoint_Request command)
      (sourced_calls.replay_call_authority(take index(call_authority_log m))initial))"
    using completed_sourced_known_request_has_its_actual_source[OF invoked_run completed_run] unfolding m_def by blast
  have raw: "\<forall>query. command=Read_Raw query \<longrightarrow>
    reply=Raw_Value(abstract_query_value query(sourced_response_alpha
      (sourced_calls.replay_call_authority(take index(call_authority_log m))initial)))"
    using actual sourced_raw_query_has_its_independent_value by (metis sourced_reply.inject)
  have operational: "\<forall>endpoint key. command=Read_Operation endpoint key \<longrightarrow>
    reply=Operation_Status(target_phase(sourced_response_alpha
      (sourced_calls.replay_call_authority(take index(call_authority_log m))initial))key)
      (observation_secondary(sourced_calls.replay_call_authority(take index(call_authority_log m))initial)endpoint)"
    using actual sourced_operational_query_has_its_exact_fields(1) by (metis sourced_reply.inject)
  have journal: "command=Read_Raw_Journal \<longrightarrow>
    reply=Journal_Events(target_journal(sourced_response_alpha
      (sourced_calls.replay_call_authority(take index(call_authority_log m))initial)))"
    using actual sourced_operational_query_has_its_exact_fields(2) by (metis sourced_reply.inject)
  show ?thesis using found bound raw operational journal by blast
qed

theorem completed_sourced_physical_inspections_keep_the_source_fields:
  fixes actions :: "(sourced_request,sourced_environment) client_call_action list"
    and initial :: sourced_observation_state
  defines "m \<equiv> sourced_calls.run_calls actions(initial_call_machine initial)"
  assumes invoked: "call_invocations m call_id=Some(request,began)"
    and completed: "call_completions m call_id=Some reply"
  shows "\<exists>index. call_authority_results m call_id=Some(request,reply,index) \<and>
    index<length(call_authority_log m) \<and>
    (\<forall>account. request=Inspect_Source_Units account \<longrightarrow>
      reply=(if observation_source_available(sourced_calls.replay_call_authority(take index(call_authority_log m))initial)
        then Source_Unit_Value(boundary_units(controlled_endpoint(coupled_source(observation_source
          (sourced_calls.replay_call_authority(take index(call_authority_log m))initial))))account)
        else Sourced_Observation Observation_Unavailable)) \<and>
    (request=Inspect_Source_Effects \<longrightarrow>
      reply=(if observation_source_available(sourced_calls.replay_call_authority(take index(call_authority_log m))initial)
        then Source_Effect_History(boundary_effects(controlled_endpoint(coupled_source(observation_source
          (sourced_calls.replay_call_authority(take index(call_authority_log m))initial)))))
        else Sourced_Observation Observation_Unavailable))"
proof -
  have invoked_run: "call_invocations(sourced_calls.run_calls actions(initial_call_machine initial))call_id=Some(request,began)"
    using invoked by (simp only: m_def)
  have completed_run: "call_completions(sourced_calls.run_calls actions(initial_call_machine initial))call_id=Some reply"
    using completed by (simp only: m_def)
  obtain index where found: "call_authority_results m call_id=Some(request,reply,index)"
    and bound: "index<length(call_authority_log m)"
    and actual: "reply=snd(execute_sourced_request request
      (sourced_calls.replay_call_authority(take index(call_authority_log m))initial))"
    using completed_sourced_known_request_has_its_actual_source[OF invoked_run completed_run] unfolding m_def by blast
  let ?cut = "sourced_calls.replay_call_authority(take index(call_authority_log m))initial"
  have units: "\<forall>account. request=Inspect_Source_Units account \<longrightarrow>
    reply=(if observation_source_available ?cut
      then Source_Unit_Value(boundary_units(controlled_endpoint(coupled_source(observation_source ?cut)))account)
      else Sourced_Observation Observation_Unavailable)"
    using actual sourced_physical_inspection_retains_source_availability(1) by metis
  have effects: "request=Inspect_Source_Effects \<longrightarrow>
    reply=(if observation_source_available ?cut
      then Source_Effect_History(boundary_effects(controlled_endpoint(coupled_source(observation_source ?cut))))
      else Sourced_Observation Observation_Unavailable)"
    using actual sourced_physical_inspection_retains_source_availability(2) by metis
  show ?thesis using found bound units effects by blast
qed

theorem completed_sourced_current_preserves_value_revision_and_source_guards:
  fixes actions :: "(sourced_request,sourced_environment) client_call_action list"
    and initial :: sourced_observation_state
  defines "m \<equiv> sourced_calls.run_calls actions(initial_call_machine initial)"
  assumes completed: "call_completions m call_id=Some(Sourced_Observation(Current_Value revision payload))"
  shows "\<exists>command query index.
    call_authority_results m call_id=Some(Endpoint_Request command,Sourced_Observation(Current_Value revision payload),index) \<and>
    index<length(call_authority_log m) \<and> command_query command=Some query \<and>
    payload=abstract_query_value query(sourced_response_alpha
      (sourced_calls.replay_call_authority(take index(call_authority_log m))initial)) \<and>
    revision=target_revision(sourced_response_alpha
      (sourced_calls.replay_call_authority(take index(call_authority_log m))initial)) \<and>
    (\<forall>account. current_source_query command=Some account \<longrightarrow>
      observation_source_available(sourced_calls.replay_call_authority(take index(call_authority_log m))initial) \<and>
      source_view_is_reconciled(observation_source
        (sourced_calls.replay_call_authority(take index(call_authority_log m))initial))account)"
proof -
  have completed_run: "call_completions(sourced_calls.run_calls actions(initial_call_machine initial))call_id=
    Some(Sourced_Observation(Current_Value revision payload))" using completed by (simp only: m_def)
  obtain request index where found:
    "call_authority_results m call_id=Some(request,Sourced_Observation(Current_Value revision payload),index)"
    and bound: "index<length(call_authority_log m)"
    and actual: "Sourced_Observation(Current_Value revision payload)=snd(execute_sourced_request request
      (sourced_calls.replay_call_authority(take index(call_authority_log m))initial))"
    using every_completed_sourced_reply_has_its_actual_source[OF completed_run] unfolding m_def by blast
  show ?thesis using found bound sourced_current_request_preserves_its_fields_and_source_guards[OF actual[symmetric]] by blast
qed

theorem completed_sourced_historical_has_a_prior_actual_snapshot:
  fixes actions :: "(sourced_request,sourced_environment) client_call_action list"
    and balances :: "source_account \<Rightarrow> nat" and regulatory :: global_state
    and contexts :: "nat \<Rightarrow> lock_context"
  defines "m \<equiv> sourced_calls.run_calls actions
    (initial_call_machine(initial_sourced_observations balances regulatory contexts))"
  assumes completed: "call_completions m call_id=Some(Sourced_Observation(Historical_Value revision payload))"
  shows "\<exists>command query execution_index snapshot_index.
    call_authority_results m call_id=Some(Endpoint_Request command,Sourced_Observation(Historical_Value revision payload),execution_index) \<and>
    execution_index<length(call_authority_log m) \<and> snapshot_index\<le>execution_index \<and>
    command_query command=Some query \<and> requested_history_revision command=Some revision \<and>
    payload=abstract_query_value query(sourced_response_alpha(sourced_calls.replay_call_authority
      (take snapshot_index(call_authority_log m))(initial_sourced_observations balances regulatory contexts))) \<and>
    target_revision(sourced_response_alpha(sourced_calls.replay_call_authority
      (take snapshot_index(call_authority_log m))(initial_sourced_observations balances regulatory contexts)))=revision"
proof -
  let ?initial = "initial_sourced_observations balances regulatory contexts"
  have completed_run: "call_completions(sourced_calls.run_calls actions(initial_call_machine ?initial))call_id=
    Some(Sourced_Observation(Historical_Value revision payload))" using completed by (simp only: m_def)
  obtain request execution_index where found:
    "call_authority_results m call_id=Some(request,Sourced_Observation(Historical_Value revision payload),execution_index)"
    and bound: "execution_index<length(call_authority_log m)"
    and actual: "Sourced_Observation(Historical_Value revision payload)=snd(execute_sourced_request request
      (sourced_calls.replay_call_authority(take execution_index(call_authority_log m))?initial))"
    using every_completed_sourced_reply_has_its_actual_source[OF completed_run] unfolding m_def by blast
  obtain command query snapshot_index where history_bound:
    "snapshot_index\<le>length(take execution_index(call_authority_log m))"
    and request: "request=Endpoint_Request command" and query: "command_query command=Some query"
    and requested: "requested_history_revision command=Some revision"
    and payload: "payload=abstract_query_value query(sourced_response_alpha(sourced_calls.replay_call_authority
      (take snapshot_index(take execution_index(call_authority_log m)))?initial))"
    and revision: "target_revision(sourced_response_alpha(sourced_calls.replay_call_authority
      (take snapshot_index(take execution_index(call_authority_log m)))?initial))=revision"
    using sourced_historical_reply_has_an_independent_past_value[OF actual[symmetric]] by blast
  have execution_le: "execution_index\<le>length(call_authority_log m)" using bound by simp
  have length_prefix: "length(take execution_index(call_authority_log m))=execution_index"
    using execution_le by (auto simp: length_take min_def; linarith)
  have snapshot_bound: "snapshot_index\<le>execution_index" using history_bound by (simp only: length_prefix)
  have prefix: "take snapshot_index(take execution_index(call_authority_log m))=take snapshot_index(call_authority_log m)"
    using snapshot_bound by (simp add: take_take min_def)
  show ?thesis using found bound request query requested payload revision snapshot_bound
    by (simp only: prefix) blast
qed

lemma sourced_completion_survives_every_step:
  assumes "call_completions m call_id=Some reply"
  shows "call_completions(sourced_calls.call_step action m)call_id=Some reply"
  using assms by (cases action)
    (auto simp: sourced_calls.call_definitions Let_def split: option.splits prod.splits if_splits)

theorem sourced_completed_replies_survive_finite_continuations:
  assumes "call_completions m call_id=Some reply"
  shows "call_completions(sourced_calls.run_calls actions m)call_id=Some reply"
  using assms by (induction actions arbitrary:m) (auto intro: sourced_completion_survives_every_step)

corollary completed_sourced_busy_and_unavailable_remain_completed:
  "call_completions m call_id=Some(Sourced_Observation Observation_Busy) \<Longrightarrow>
    call_completions(sourced_calls.run_calls actions m)call_id=Some(Sourced_Observation Observation_Busy)"
  "call_completions m call_id=Some(Sourced_Observation Observation_Unavailable) \<Longrightarrow>
    call_completions(sourced_calls.run_calls actions m)call_id=Some(Sourced_Observation Observation_Unavailable)"
  by (auto intro: sourced_completed_replies_survive_finite_continuations)

text \<open>These results use the sourced callbacks and their own durable
  replay. The observed callback is reused only where the actual sourced
  endpoint delegates to it; the protected application path and current source
  availability and reconciliation checks are handled separately. History
  capture is proved for actual sourced requests and environmental inputs.
  Completed current and historical values retain their actual source cuts.
  Busy, unavailable and all other completed replies retain their indexed
  execution and remain completed across subsequent source changes.

  Endpoint raw and operational queries use the independent observation target.
  Physical source inspections keep the authoritative source fields and the
  source-availability result. They are not silently equated with a lagging
  local mirror or with a successful current-source query.\<close>

end

end
