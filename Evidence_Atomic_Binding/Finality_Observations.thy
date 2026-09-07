(* SPDX-License-Identifier: BSD-3-Clause *)
theory Finality_Observations
  imports Finality_Calls Finality_Records
begin

section \<open>Stored Views and Explicit Query Kinds\<close>

datatype application_query =
    Source_Balance source_account
  | Destination_Balance destination_account
  | Root_Balance source_key destination_account
  | Application_Value nat
  | Regulatory_State nat nat
  | Terminal_Receipt source_key

datatype application_value =
    Units_Value nat
  | Regulatory_Value "reg_state option"
  | Receipt_Value "terminal_record option"

record endpoint_snapshot =
  snapshot_revision :: nat
  snapshot_financial :: reservation_state
  snapshot_regulatory :: global_state
  snapshot_records :: "source_key \<Rightarrow> terminal_record option"
  snapshot_published :: "source_key set"

definition capture_snapshot :: "finality_core \<Rightarrow> endpoint_snapshot" where
  "capture_snapshot s=\<lparr>snapshot_revision=core_epoch s,
    snapshot_financial=machine_state(core_parent s),
    snapshot_regulatory=receiver_snapshot(core_regulatory s),
    snapshot_records=core_records s,snapshot_published=core_published s\<rparr>"

fun stored_query :: "application_query \<Rightarrow> endpoint_snapshot \<Rightarrow> application_value" where
  "stored_query(Source_Balance account)cache=Units_Value(source_units(snapshot_financial cache)account)"
| "stored_query(Destination_Balance account)cache=Units_Value(destination_units(snapshot_financial cache)account)"
| "stored_query(Root_Balance key account)cache=Units_Value(funded_units(snapshot_financial cache)(key,account))"
| "stored_query(Application_Value asset)cache=Units_Value(asset_value(snapshot_financial cache)asset)"
| "stored_query(Regulatory_State domain asset)cache=Regulatory_Value(get_reg_state(snapshot_regulatory cache)domain asset)"
| "stored_query(Terminal_Receipt key)cache=Receipt_Value(snapshot_records cache key)"

fun query_touches_binding :: "application_query \<Rightarrow> transfer_binding \<Rightarrow> bool" where
  "query_touches_binding(Source_Balance account)b=(source_account_of b=account)"
| "query_touches_binding(Destination_Balance account)b=
    (\<exists>holder. holder_account b holder=account)"
| "query_touches_binding(Root_Balance key account)b=(binding_key b=key)"
| "query_touches_binding(Application_Value asset)b=(binding_asset b=asset)"
| "query_touches_binding(Regulatory_State domain asset)b=(binding_asset b=asset)"
| "query_touches_binding(Terminal_Receipt key)b=(binding_key b=key)"

definition snapshot_query_ready :: "application_query \<Rightarrow> endpoint_snapshot \<Rightarrow> bool" where
  "snapshot_query_ready query cache \<longleftrightarrow>
    (\<forall>b\<in>set(source_effects(snapshot_financial cache)).
      query_touches_binding query b \<longrightarrow> binding_key b\<in>snapshot_published cache) \<and>
    (\<forall>key entry. snapshot_records cache key=Some entry \<longrightarrow>
      query_touches_binding query(terminal_binding entry) \<longrightarrow>
      key\<in>snapshot_published cache) \<and>
    (case query of Application_Value asset \<Rightarrow> asset_owner(snapshot_financial cache)asset=None
     | _ \<Rightarrow> True)"

record observed_finality =
  observed_core :: finality_core
  endpoint_cache :: "nat \<Rightarrow> endpoint_snapshot option"
  historical_snapshots :: "nat \<Rightarrow> endpoint_snapshot option"
  secondary_progress :: "nat \<Rightarrow> nat"

definition initial_observed_finality :: "finality_core \<Rightarrow> observed_finality" where
  "initial_observed_finality s=\<lparr>observed_core=s,endpoint_cache=(\<lambda>_.None),
    historical_snapshots=(\<lambda>_.None)(core_epoch s:=Some(capture_snapshot s)),
    secondary_progress=(\<lambda>_.0)\<rparr>"

datatype observed_reply =
    Current_Value nat application_value
  | Historical_Value nat application_value
  | Raw_Value application_value
  | Operation_Status "reservation_phase option" nat
  | Journal_Events "reservation_event list"
  | Observation_Busy
  | Observation_Unavailable
  | Observation_Rejected
  | Cache_Refreshed
  | Effect_Reply finality_reply

datatype observed_command =
    Read_Current nat application_query
  | Read_Protected_Current nat nat execution_request application_query
  | Read_Historical nat application_query
  | Read_Protected_Historical nat nat execution_request nat application_query
  | Read_Raw application_query
  | Read_Operation nat source_key
  | Read_Raw_Journal
  | Refresh_Endpoint nat
  | Execute_Current nat client_command

datatype observed_environment =
    Replace_Current_Context nat lock_context
  | Report_Secondary_Progress nat nat
  | Corrupt_Endpoint_Cache nat "endpoint_snapshot option"

definition current_cache_valid :: "observed_finality \<Rightarrow> nat \<Rightarrow> bool" where
  "current_cache_valid s endpoint \<longleftrightarrow>
    endpoint_cache s endpoint=Some(capture_snapshot(observed_core s))"

fun public_balance_query :: "application_query \<Rightarrow> bool" where
  "public_balance_query(Source_Balance account)=True"
| "public_balance_query(Destination_Balance account)=True"
| "public_balance_query _=False"

fun query_request_matches :: "application_query \<Rightarrow> execution_request \<Rightarrow> bool" where
  "query_request_matches(Source_Balance account)r=(account=source_account_of(request_binding r))"
| "query_request_matches(Destination_Balance(domain,asset,holder))r=
    (domain=binding_destination(request_binding r) \<and> asset=binding_asset(request_binding r))"
| "query_request_matches(Root_Balance key(domain,asset,holder))r=
    (key=binding_key(request_binding r) \<and> domain=binding_destination(request_binding r) \<and>
      asset=binding_asset(request_binding r))"
| "query_request_matches(Application_Value asset)r=(asset=binding_asset(request_binding r))"
| "query_request_matches(Regulatory_State domain asset)r=
    (domain=binding_destination(request_binding r) \<and> asset=binding_asset(request_binding r))"
| "query_request_matches(Terminal_Receipt key)r=(key=binding_key(request_binding r))"

definition protected_read_access :: "nat \<Rightarrow> nat \<Rightarrow> execution_request \<Rightarrow>
  application_query \<Rightarrow> observed_finality \<Rightarrow> bool" where
  "protected_read_access endpoint index r query s=(let c=current_lock_view(observed_core s)endpoint in
    query_request_matches query r \<and>
    current_read_allowed(lock_authority c)(request_caller r)(request_version r) \<and>
    request_authority_epoch r=context_authority_epoch(lock_authority c) \<and>
    terminal_intent_guard(observed_core s)index(Data_Read_Intent r))"

definition current_query_reply :: "nat \<Rightarrow> application_query \<Rightarrow> observed_finality \<Rightarrow> observed_reply" where
  "current_query_reply endpoint query s=(case endpoint_cache s endpoint of None \<Rightarrow> Observation_Unavailable
    | Some cache \<Rightarrow> if current_cache_valid s endpoint \<and> snapshot_query_ready query cache
      then Current_Value(snapshot_revision cache)(stored_query query cache) else Observation_Busy)"

definition historical_query_reply :: "nat \<Rightarrow> application_query \<Rightarrow> observed_finality \<Rightarrow> observed_reply" where
  "historical_query_reply revision query s=(case historical_snapshots s revision of None \<Rightarrow> Observation_Unavailable
    | Some cache \<Rightarrow> if snapshot_query_ready query cache
      then Historical_Value revision(stored_query query cache) else Observation_Busy)"

definition store_core_result :: "finality_core \<times> finality_reply \<Rightarrow> observed_finality
  \<Rightarrow> observed_finality \<times> observed_reply" where
  "store_core_result result s=(let fresh=fst result in
    (s\<lparr>observed_core:=fresh,historical_snapshots:=(historical_snapshots s)
      (core_epoch fresh:=Some(capture_snapshot fresh))\<rparr>,Effect_Reply(snd result)))"

context source_attestation
begin

definition execute_protected_current :: "nat \<Rightarrow> nat \<Rightarrow> execution_request \<Rightarrow>
  application_query \<Rightarrow> observed_finality \<Rightarrow> observed_finality \<times> observed_reply" where
  "execute_protected_current endpoint index r query s=
    (if \<not>protected_read_access endpoint index r query s then (s,Observation_Rejected)
     else case current_query_reply endpoint query s of
       Current_Value revision value \<Rightarrow>
         (case query of Application_Value asset \<Rightarrow>
           (let result=execute_finality_client(Client_Protocol endpoint index(Data_Read_Intent r))(observed_core s)
            in case snd result of Protocol_Response(Value_Response amount) \<Rightarrow>
              (fst(store_core_result result s),Current_Value revision value)
            | _ \<Rightarrow> (s,Observation_Rejected))
          | _ \<Rightarrow> (s,Current_Value revision value))
     | reply \<Rightarrow> (s,reply))"

fun execute_observed :: "observed_command \<Rightarrow> observed_finality \<Rightarrow> observed_finality \<times> observed_reply" where
  "execute_observed(Read_Current endpoint query)s=
    (s,if public_balance_query query then current_query_reply endpoint query s else Observation_Rejected)"
| "execute_observed(Read_Protected_Current endpoint index r query)s=execute_protected_current endpoint index r query s"
| "execute_observed(Read_Historical revision query)s=
    (s,if public_balance_query query then historical_query_reply revision query s else Observation_Rejected)"
| "execute_observed(Read_Protected_Historical endpoint index r revision query)s=
    (s,if protected_read_access endpoint index r query s
      then historical_query_reply revision query s else Observation_Rejected)"
| "execute_observed(Read_Raw query)s=(s,Raw_Value(stored_query query(capture_snapshot(observed_core s))))"
| "execute_observed(Read_Operation endpoint key)s=
    (s,Operation_Status(phase_at(machine_state(core_parent(observed_core s)))key)(secondary_progress s endpoint))"
| "execute_observed Read_Raw_Journal s=(s,Journal_Events(machine_journal(core_parent(observed_core s))))"
| "execute_observed(Refresh_Endpoint endpoint)s=
    (s\<lparr>endpoint_cache:=(endpoint_cache s)(endpoint:=Some(capture_snapshot(observed_core s)))\<rparr>,Cache_Refreshed)"
| "execute_observed(Execute_Current endpoint command)s=
    (if current_cache_valid s endpoint then store_core_result(execute_finality_client command(observed_core s))s
     else (s,Observation_Busy))"

fun execute_observed_environment :: "observed_environment \<Rightarrow> observed_finality
  \<Rightarrow> observed_finality \<times> observed_reply" where
  "execute_observed_environment(Replace_Current_Context endpoint c)s=
    store_core_result(execute_finality_environment(endpoint,c)(observed_core s))s"
| "execute_observed_environment(Report_Secondary_Progress endpoint revision)s=
    (s\<lparr>secondary_progress:=(secondary_progress s)(endpoint:=revision)\<rparr>,Cache_Refreshed)"
| "execute_observed_environment(Corrupt_Endpoint_Cache endpoint cache)s=
    (s\<lparr>endpoint_cache:=(endpoint_cache s)(endpoint:=cache)\<rparr>,Cache_Refreshed)"

sublocale observed_calls: durable_call_protocol execute_observed execute_observed_environment .

theorem successful_current_reply_has_actual_authority_state:
  assumes "snd(execute_observed(Read_Current endpoint query)s)=Current_Value revision value"
  shows "revision=core_epoch(observed_core s) \<and>
    value=stored_query query(capture_snapshot(observed_core s)) \<and>
    snapshot_query_ready query(capture_snapshot(observed_core s))"
  using assms
  by (auto simp: current_query_reply_def current_cache_valid_def capture_snapshot_def
    split: option.splits if_splits)

lemma refresh_allows_a_ready_current_query:
  assumes "snapshot_query_ready query(capture_snapshot(observed_core s))" "public_balance_query query"
  shows "snd(execute_observed(Read_Current endpoint query)
    (fst(execute_observed(Refresh_Endpoint endpoint)s)))=
    Current_Value(core_epoch(observed_core s))(stored_query query(capture_snapshot(observed_core s)))"
  using assms by (simp add: current_query_reply_def current_cache_valid_def capture_snapshot_def)

lemma stale_cache_cannot_complete_as_current:
  assumes "endpoint_cache s endpoint=Some cache" "snapshot_revision cache<core_epoch(observed_core s)"
    "public_balance_query query"
  shows "snd(execute_observed(Read_Current endpoint query)s)=Observation_Busy"
  using assms by (auto simp: current_query_reply_def current_cache_valid_def capture_snapshot_def)

theorem protected_current_response_has_revision:
  assumes "snd(execute_protected_current endpoint index r query s)=Current_Value revision value"
  shows "revision=core_epoch(observed_core s) \<and>
    value=stored_query query(capture_snapshot(observed_core s)) \<and>
    protected_read_access endpoint index r query s"
  using assms
  by (auto simp: execute_protected_current_def current_query_reply_def current_cache_valid_def
      capture_snapshot_def Let_def split: if_splits option.splits application_query.splits
      observed_reply.splits finality_reply.splits reservation_reply.splits)

theorem protected_application_read_consumes_the_actual_parent_read:
  assumes "snd(execute_observed(Read_Protected_Current endpoint index r(Application_Value asset))s)=
    Current_Value revision value"
  shows "\<exists>amount. snd(read_source_data(current_lock_view(observed_core s)endpoint)r
      (core_parent(observed_core s)))=Value_Response amount \<and>
    value=Units_Value amount"
  using assms
  by (auto simp: execute_protected_current_def current_query_reply_def current_cache_valid_def
      protected_read_access_def capture_snapshot_def execute_finality_client_def invoke_protocol_def
      lift_protocol_result_def read_source_data_def record_observation_def snapshot_query_ready_def Let_def
      split: if_splits option.splits finality_reply.splits reservation_reply.splits)

lemma protected_read_does_not_decrease_authority_revision:
  "core_epoch(observed_core s)\<le>core_epoch(observed_core(fst(execute_protected_current endpoint index r query s)))"
  by (auto simp: execute_protected_current_def store_core_result_def execute_finality_client_def Let_def
      split: if_splits observed_reply.splits application_query.splits finality_reply.splits reservation_reply.splits)

lemma current_execution_consumes_actual_current_context:
  assumes "snd(execute_observed(Execute_Current endpoint(Client_Protocol consumer index intent))s)=Effect_Reply reply"
  shows "current_cache_valid s endpoint \<and>
    reply=snd(invoke_protocol consumer(core_epoch(observed_core s))index intent(observed_core s))"
  using assms by (auto simp: store_core_result_def execute_finality_client_def Let_def split: if_splits)

lemma observation_steps_do_not_decrease_authority_revision:
  "core_epoch(observed_core s)\<le>core_epoch(observed_core(fst(execute_observed command s)))"
  by (cases command)
    (auto simp: store_core_result_def execute_finality_client_def Let_def
      intro: protected_read_does_not_decrease_authority_revision)

lemma environment_steps_do_not_decrease_authority_revision:
  "core_epoch(observed_core s)\<le>core_epoch(observed_core(fst(execute_observed_environment input s)))"
  by (cases input)
    (auto simp: store_core_result_def execute_finality_environment_def Let_def)

lemma secondary_lag_does_not_block_current_authority_read:
  "snd(execute_observed(Read_Current endpoint query)
    (s\<lparr>secondary_progress:=(secondary_progress s)(endpoint:=old_revision)\<rparr>))=
   snd(execute_observed(Read_Current endpoint query)s)"
proof -
  have same: "current_cache_valid
      (s\<lparr>secondary_progress:=(secondary_progress s)(endpoint:=old_revision)\<rparr>)endpoint=
    current_cache_valid s endpoint"
    by (simp add: current_cache_valid_def)
  show ?thesis by (cases "endpoint_cache s endpoint") (simp_all add: current_query_reply_def same)
qed

lemma completed_busy_remains_completed:
  "call_completions m call_id=Some Observation_Busy \<Longrightarrow>
    observed_calls.complete_client_call call_id m=m"
  by (rule observed_calls.completed_calls_are_not_completed_twice)

text \<open>The current-read barrier compares the entire cached view with
  the authority's current state at consumption. A version number alone is
  insufficient. This is an explicit, potentially expensive authority read;
  a physical implementation must authenticate that source and preserve the
  atomic read-and-use boundary. Secondary progress is reported separately.
  Raw state and raw journal observers remain available during partial effects.
  Public current balance reads and protected application queries have different
  commands. Protected queries consume the current read role, authority epoch,
  request scope and terminal reference. Application-value queries also execute
  the actual parent data-read operation. That operation is not a replacement
  for public balance getters or raw storage observations.
  Protected historical queries also check the current read authority before
  returning the requested older snapshot. Raw observers have a separate reply
  type and do not establish authorized current-query success or confidentiality
  of already exposed storage.
  Historical queries name an authority snapshot and never masquerade as a
  current response. A Busy reply is completed through the same durable call
  protocol as an accepted effect or a successful query.\<close>

end

end
