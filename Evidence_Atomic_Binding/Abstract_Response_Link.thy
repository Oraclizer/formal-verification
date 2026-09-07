(* SPDX-License-Identifier: BSD-3-Clause *)
theory Abstract_Response_Link
  imports Historical_Snapshot_Provenance
begin

fun command_query :: "observed_command \<Rightarrow> application_query option" where
  "command_query(Read_Current endpoint query)=Some query"
| "command_query(Read_Protected_Current endpoint index r query)=Some query"
| "command_query(Read_Historical revision query)=Some query"
| "command_query(Read_Protected_Historical endpoint index r revision query)=Some query"
| "command_query(Read_Raw query)=Some query"
| "command_query _=None"

fun requested_history_revision :: "observed_command \<Rightarrow> nat option" where
  "requested_history_revision(Read_Historical revision query)=Some revision"
| "requested_history_revision(Read_Protected_Historical endpoint index r revision query)=Some revision"
| "requested_history_revision _=None"

lemma historical_reply_has_a_ready_stored_snapshot:
  assumes "historical_query_reply revision query state=Historical_Value received payload"
  shows "received=revision \<and> (\<exists>cache. historical_snapshots state revision=Some cache \<and>
    snapshot_query_ready query cache \<and> payload=stored_query query cache)"
  using assms by (auto simp: historical_query_reply_def split: option.splits if_splits)

lemma current_query_busy_has_a_concrete_failure_reason:
  "current_query_reply endpoint query state=Observation_Busy \<longleftrightarrow>
    (\<exists>cache. endpoint_cache state endpoint=Some cache \<and>
      (\<not>current_cache_valid state endpoint \<or> \<not>snapshot_query_ready query cache))"
  by (auto simp: current_query_reply_def split: option.splits if_splits)

lemma current_query_unavailable_means_no_local_view:
  "current_query_reply endpoint query state=Observation_Unavailable \<longleftrightarrow>
    endpoint_cache state endpoint=None"
  by (auto simp: current_query_reply_def split: option.splits if_splits)

context source_attestation
begin

theorem any_successful_current_command_has_an_independent_abstract_query:
  assumes "snd(execute_observed command state)=Current_Value revision payload"
  shows "\<exists>query. command_query command=Some query \<and>
    payload=abstract_query_value query(observation_alpha(observed_core state)) \<and>
    revision=target_revision(observation_alpha(observed_core state))"
proof (cases command)
  case (Read_Current endpoint query)
  have actual: "snd(execute_observed(Read_Current endpoint query)state)=Current_Value revision payload"
    using assms by (simp only: Read_Current)
  have fields: "payload=abstract_query_value query(observation_alpha(observed_core state)) \<and>
    revision=target_revision(observation_alpha(observed_core state))"
    using public_current_response_preserves_all_its_observation_fields[OF actual] by blast
  show ?thesis using fields by (auto simp: Read_Current)
next
  case (Read_Protected_Current endpoint index r query)
  have actual: "snd(execute_observed(Read_Protected_Current endpoint index r query)state)=Current_Value revision payload"
    using assms by (simp only: Read_Protected_Current)
  have fields: "payload=abstract_query_value query(observation_alpha(observed_core state)) \<and>
    revision=target_revision(observation_alpha(observed_core state))"
    using protected_current_response_preserves_its_independent_value[OF actual] by blast
  show ?thesis using fields by (auto simp: Read_Protected_Current)
qed (use assms in \<open>auto simp: historical_query_reply_def store_core_result_def Let_def
  split: option.splits if_splits\<close>)

theorem any_historical_command_names_its_actual_snapshot:
  assumes "snd(execute_observed command state)=Historical_Value revision payload"
  shows "\<exists>query cache. command_query command=Some query \<and>
    requested_history_revision command=Some revision \<and>
    historical_snapshots state revision=Some cache \<and>
    snapshot_query_ready query cache \<and> payload=stored_query query cache"
  using assms
  by (cases command)
    (auto simp: execute_protected_current_def current_query_reply_def historical_query_reply_def
      store_core_result_def Let_def
      split: option.splits if_splits observed_reply.splits application_query.splits
        finality_reply.splits reservation_reply.splits)

theorem public_current_failure_preserves_its_admission_reason:
  "snd(execute_observed(Read_Current endpoint query)state)=Observation_Rejected \<longleftrightarrow>
    \<not>public_balance_query query"
  "public_balance_query query \<Longrightarrow>
    (snd(execute_observed(Read_Current endpoint query)state)=Observation_Busy \<longleftrightarrow>
      (\<exists>cache. endpoint_cache state endpoint=Some cache \<and>
        (\<not>current_cache_valid state endpoint \<or> \<not>snapshot_query_ready query cache)))"
  "public_balance_query query \<Longrightarrow>
    (snd(execute_observed(Read_Current endpoint query)state)=Observation_Unavailable \<longleftrightarrow>
      endpoint_cache state endpoint=None)"
  by (auto simp: current_query_reply_def split: option.splits if_splits)

theorem protected_read_rejects_a_failed_current_authority_check:
  "\<not>protected_read_access endpoint index r query state \<Longrightarrow>
    execute_observed(Read_Protected_Current endpoint index r query)state=(state,Observation_Rejected)"
  "\<not>protected_read_access endpoint index r query state \<Longrightarrow>
    execute_observed(Read_Protected_Historical endpoint index r revision query)state=(state,Observation_Rejected)"
  by (simp_all add: execute_protected_current_def)

theorem a_historical_response_from_replay_has_an_actual_abstract_source:
  assumes response: "snd(execute_observed command(observed_calls.replay_call_authority entries
    (initial_observed_finality initial_core)))=Historical_Value revision payload"
  shows "\<exists>query index. index\<le>length entries \<and>
    command_query command=Some query \<and> requested_history_revision command=Some revision \<and>
    payload=abstract_query_value query(observation_alpha(observed_core
      (observed_calls.replay_call_authority(take index entries)(initial_observed_finality initial_core)))) \<and>
    target_revision(observation_alpha(observed_core
      (observed_calls.replay_call_authority(take index entries)(initial_observed_finality initial_core))))=revision"
proof -
  obtain query cache where query: "command_query command=Some query"
    and requested: "requested_history_revision command=Some revision"
    and stored: "historical_snapshots(observed_calls.replay_call_authority entries
      (initial_observed_finality initial_core))revision=Some cache"
    and payload: "payload=stored_query query cache"
    using any_historical_command_names_its_actual_snapshot[OF response] by blast
  obtain index where bound: "index\<le>length entries"
    and snapshot: "cache=capture_snapshot(observed_core(observed_calls.replay_call_authority(take index entries)
      (initial_observed_finality initial_core)))" and revision: "snapshot_revision cache=revision"
    using snapshots_from_an_actual_initial_view_have_real_history[OF stored] by blast
  have interpreted_value: "payload=abstract_query_value query(observation_alpha(observed_core
      (observed_calls.replay_call_authority(take index entries)(initial_observed_finality initial_core))))"
    using payload independent_stored_and_abstract_query_readers_agree[
      OF captured_state_supplies_snapshot_correspondence]
    by (simp only: snapshot)
  have at_revision: "target_revision(observation_alpha(observed_core
      (observed_calls.replay_call_authority(take index entries)(initial_observed_finality initial_core))))=revision"
    using revision by (simp add: snapshot observation_alpha_def captured_snapshot_has_the_source_revision)
  show ?thesis using bound query requested interpreted_value at_revision by blast
qed

theorem every_completed_current_reply_retains_its_abstract_execution_value:
  fixes actions :: "(observed_command,observed_environment) client_call_action list"
    and initial :: observed_finality
  assumes parent: "reservation_contract balances(core_parent(observed_core initial))"
    and regulatory: "valid_state(receiver_snapshot(core_regulatory(observed_core initial)))"
  defines "m \<equiv> observed_calls.run_calls actions(initial_call_machine initial)"
  assumes completed: "call_completions m call_id=Some(Current_Value revision payload)"
  shows "\<exists>command index query. call_authority_results m call_id=Some(command,Current_Value revision payload,index) \<and>
    command_query command=Some query \<and>
    payload=abstract_query_value query(observation_alpha(observed_core
      (observed_calls.replay_call_authority(take index(call_authority_log m))initial))) \<and>
    revision=target_revision(observation_alpha(observed_core
      (observed_calls.replay_call_authority(take index(call_authority_log m))initial)))"
proof -
  have completed_run: "call_completions(observed_calls.run_calls actions(initial_call_machine initial))call_id=
    Some(Current_Value revision payload)"
    using completed by (simp only: m_def)
  obtain command index where source: "call_authority_results m call_id=Some(command,Current_Value revision payload,index)"
    and actual: "Current_Value revision payload=snd(execute_observed command
      (observed_calls.replay_call_authority(take index(call_authority_log m))initial))"
    using every_generated_observed_completion_has_an_actual_product_source[OF parent regulatory completed_run]
    unfolding m_def by blast
  obtain query where query: "command_query command=Some query"
    and payload: "payload=abstract_query_value query(observation_alpha(observed_core
      (observed_calls.replay_call_authority(take index(call_authority_log m))initial)))"
    and revision: "revision=target_revision(observation_alpha(observed_core
      (observed_calls.replay_call_authority(take index(call_authority_log m))initial)))"
    using any_successful_current_command_has_an_independent_abstract_query[OF actual[symmetric]] by blast
  show ?thesis using source query payload revision by blast
qed

theorem every_completed_historical_reply_retains_its_actual_abstract_source:
  fixes actions :: "(observed_command,observed_environment) client_call_action list"
    and initial_core :: finality_core
  defines "m \<equiv> observed_calls.run_calls actions
    (initial_call_machine(initial_observed_finality initial_core))"
  assumes completed: "call_completions m call_id=Some(Historical_Value revision payload)"
  shows "\<exists>command execution_index snapshot_index query.
    call_authority_results m call_id=Some(command,Historical_Value revision payload,execution_index) \<and>
    execution_index<length(call_authority_log m) \<and> snapshot_index\<le>execution_index \<and>
    command_query command=Some query \<and> requested_history_revision command=Some revision \<and>
    payload=abstract_query_value query(observation_alpha(observed_core
      (observed_calls.replay_call_authority(take snapshot_index(call_authority_log m))
        (initial_observed_finality initial_core)))) \<and>
    target_revision(observation_alpha(observed_core
      (observed_calls.replay_call_authority(take snapshot_index(call_authority_log m))
        (initial_observed_finality initial_core))))=revision"
proof -
  have life: "call_lifecycle_contract m"
    unfolding m_def by (rule observed_calls.generated_call_lifecycle_contract)
  obtain command execution_index where found:
    "call_authority_results m call_id=Some(command,Historical_Value revision payload,execution_index)"
    using completed_result_has_source[OF life completed] by blast
  have cache: "authority_cache_contract m"
    and replay: "observed_calls.authority_replay_contract m"
    using observed_calls.generated_call_contracts[of actions "initial_observed_finality initial_core"]
    by (simp_all add: m_def)
  have genesis: "call_genesis m=initial_observed_finality initial_core"
    by (simp add: m_def initial_call_machine_def)
  have execution_bound: "execution_index<length(call_authority_log m)"
    by (rule authority_cache_lookup(1)[OF cache found])
  have actual_recorded: "Historical_Value revision payload=snd(execute_observed command
    (observed_calls.replay_call_authority(take execution_index(call_authority_log m))
      (initial_observed_finality initial_core)))"
    using observed_calls.cached_result_is_the_actual_indexed_reply[OF cache replay found]
    by (simp only: genesis)
  obtain query snapshot_index where history_bound:
    "snapshot_index\<le>length(take execution_index(call_authority_log m))"
    and query: "command_query command=Some query"
    and requested: "requested_history_revision command=Some revision"
    and historical_value: "payload=abstract_query_value query(observation_alpha(observed_core
      (observed_calls.replay_call_authority(take snapshot_index(take execution_index(call_authority_log m)))
        (initial_observed_finality initial_core))))"
    and historical_revision: "target_revision(observation_alpha(observed_core
      (observed_calls.replay_call_authority(take snapshot_index(take execution_index(call_authority_log m)))
        (initial_observed_finality initial_core))))=revision"
    using a_historical_response_from_replay_has_an_actual_abstract_source[OF actual_recorded[symmetric]] by blast
  have execution_le: "execution_index\<le>length(call_authority_log m)"
    by (rule less_imp_le[OF execution_bound])
  have prefix_length: "length(take execution_index(call_authority_log m))=execution_index"
    using execution_le by (auto simp: length_take min_def; linarith)
  have snapshot_bound: "snapshot_index\<le>execution_index"
    using history_bound by (simp only: prefix_length)
  have nested_prefix: "take snapshot_index(take execution_index(call_authority_log m))=
    take snapshot_index(call_authority_log m)"
    using snapshot_bound by (simp add: take_take min_def)
  have interpreted_value: "payload=abstract_query_value query(observation_alpha(observed_core
      (observed_calls.replay_call_authority(take snapshot_index(call_authority_log m))
        (initial_observed_finality initial_core))))"
    using historical_value by (simp only: nested_prefix)
  have interpreted_revision: "target_revision(observation_alpha(observed_core
      (observed_calls.replay_call_authority(take snapshot_index(call_authority_log m))
        (initial_observed_finality initial_core))))=revision"
    using historical_revision by (simp only: nested_prefix)
  show ?thesis using found execution_bound snapshot_bound query requested interpreted_value interpreted_revision by blast
qed

text \<open>Successful, historical, raw, operational, rejected and unavailable
  observations are distinct. Failure conditions are derived from the actual
  admission checks; a Busy response is not silently turned into a later
  successful response. The durable call source supplies the exact execution
  position for a completed value. A completed historical response additionally
  names a snapshot cut no later than that execution position. Historical
  values refer to real earlier source cuts rather than being reclassified as current values. The physical
  authentication and freshness of the authority log remain explicit source
  obligations, separate from this interpretation of its generated history.\<close>

end

end
