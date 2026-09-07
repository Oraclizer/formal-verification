(* SPDX-License-Identifier: BSD-3-Clause *)
theory Finality_Calls
  imports Finality_Protocol
begin

section \<open>Durable Requests and Local Response Loss\<close>

type_synonym client_call_id = "nat \<times> nat"

datatype client_command =
    Client_Terminal source_certificate
  | Client_Protocol nat nat protocol_intent
  | Client_Regulatory nat nat execution_request
  | Client_Publication source_key

fun client_operation :: "finality_core \<Rightarrow> client_command \<Rightarrow> finality_operation" where
  "client_operation s(Client_Terminal cert)=Record_Terminal cert"
| "client_operation s(Client_Protocol endpoint index intent)=
    Invoke_Protocol endpoint(core_epoch s)index intent"
| "client_operation s(Client_Regulatory endpoint index r)=
    Invoke_Regulatory endpoint(core_epoch s)index r"
| "client_operation s(Client_Publication key)=Publish_Primary key"

lemma client_cannot_install_context:
  "client_operation s command \<noteq> Install_Context endpoint context"
  by (cases command) auto

datatype endpoint_availability = Endpoint_Up | Endpoint_Down
datatype authority_connection = Authority_Connected | Authority_Disconnected

datatype ('command,'reply,'environment) authority_call_entry =
    Authority_Executed client_call_id 'command 'reply
  | Authority_Input 'environment 'reply

datatype ('command,'reply) client_call_event =
    Call_Began client_call_id 'command
  | Call_Dispatched client_call_id nat
  | Call_Redispatched client_call_id nat
  | Call_Response_Received client_call_id nat
  | Call_Response_Lost client_call_id
  | Call_Completed client_call_id 'command 'reply nat
  | Call_Payload_Rejected client_call_id 'command
  | Call_Waiting client_call_id
  | Local_Endpoint_Crashed
  | Local_Endpoint_Recovered
  | Authority_Link_Changed authority_connection
  | Authority_Input_Recorded nat

datatype ('command,'environment) client_call_action =
    Begin_Call client_call_id 'command
  | Dispatch_Call client_call_id 'command
  | Collect_Response client_call_id 'command
  | Lose_Response client_call_id
  | Complete_Call client_call_id
  | Crash_Local_Endpoint
  | Recover_Local_Endpoint
  | Set_Authority_Connection authority_connection
  | Apply_Authority_Input 'environment

record ('state,'command,'reply,'environment) durable_call_machine =
  call_genesis :: 'state
  call_authority_state :: 'state
  call_authority_log :: "('command,'reply,'environment) authority_call_entry list"
  call_authority_results :: "client_call_id \<Rightarrow> ('command \<times> 'reply \<times> nat) option"
  call_invocations :: "client_call_id \<Rightarrow> ('command \<times> nat) option"
  call_completions :: "client_call_id \<Rightarrow> 'reply option"
  call_local_results :: "client_call_id \<Rightarrow> ('command \<times> 'reply \<times> nat) option"
  call_local_status :: endpoint_availability
  call_connection :: authority_connection
  call_history :: "('command,'reply) client_call_event list"

definition initial_call_machine ::
  "'state \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine" where
  "initial_call_machine initial =
    \<lparr>call_genesis=initial,call_authority_state=initial,call_authority_log=[],
      call_authority_results=(\<lambda>_.None),call_invocations=(\<lambda>_.None),
      call_completions=(\<lambda>_.None),call_local_results=(\<lambda>_.None),
      call_local_status=Endpoint_Up,call_connection=Authority_Connected,call_history=[]\<rparr>"

fun authority_execution_ids ::
  "('command,'reply,'environment) authority_call_entry list \<Rightarrow> client_call_id list" where
  "authority_execution_ids []=[]"
| "authority_execution_ids(Authority_Executed call_id command reply#rest)=call_id#authority_execution_ids rest"
| "authority_execution_ids(Authority_Input environment reply#rest)=authority_execution_ids rest"

fun completion_ids :: "('command,'reply) client_call_event list \<Rightarrow> client_call_id list" where
  "completion_ids []=[]"
| "completion_ids(Call_Completed call_id command reply began#rest)=call_id#completion_ids rest"
| "completion_ids(_#rest)=completion_ids rest"

lemma authority_execution_ids_append [simp]:
  "authority_execution_ids(first@second)=authority_execution_ids first@authority_execution_ids second"
proof (induction first)
  case Nil
  then show ?case by simp
next
  case (Cons entry entries)
  then show ?case by (cases entry) auto
qed

lemma completion_ids_append [simp]:
  "completion_ids(first@second)=completion_ids first@completion_ids second"
proof (induction first)
  case Nil
  then show ?case by simp
next
  case (Cons entry entries)
  then show ?case by (cases entry) auto
qed

definition authority_cache_contract ::
  "('state,'command,'reply,'environment) durable_call_machine \<Rightarrow> bool" where
  "authority_cache_contract m \<longleftrightarrow>
    distinct(authority_execution_ids(call_authority_log m)) \<and>
    set(authority_execution_ids(call_authority_log m))={call_id. call_authority_results m call_id\<noteq>None} \<and>
    (\<forall>call_id command reply index. call_authority_results m call_id=Some(command,reply,index) \<longrightarrow>
      index<length(call_authority_log m) \<and>
      call_authority_log m!index=Authority_Executed call_id command reply)"

lemma authority_cache_lookup:
  assumes valid: "authority_cache_contract m"
    and found: "call_authority_results m call_id=Some(command,reply,index)"
  shows "index<length(call_authority_log m)"
    "call_authority_log m!index=Authority_Executed call_id command reply"
proof -
  have lookup: "\<forall>key command reply index.
    call_authority_results m key=Some(command,reply,index) \<longrightarrow>
    index<length(call_authority_log m) \<and>
    call_authority_log m!index=Authority_Executed key command reply"
    using valid unfolding authority_cache_contract_def by blast
  have exact: "index<length(call_authority_log m) \<and>
    call_authority_log m!index=Authority_Executed call_id command reply"
    by (rule lookup[rule_format, OF found])
  then show "index<length(call_authority_log m)"
    "call_authority_log m!index=Authority_Executed call_id command reply" by blast+
qed

definition completion_contract ::
  "('state,'command,'reply,'environment) durable_call_machine \<Rightarrow> bool" where
  "completion_contract m \<longleftrightarrow>
    distinct(completion_ids(call_history m)) \<and>
    set(completion_ids(call_history m))={call_id. call_completions m call_id\<noteq>None}"

definition local_pending ::
  "client_call_id \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine \<Rightarrow> bool" where
  "local_pending call_id m \<longleftrightarrow>
    call_invocations m call_id\<noteq>None \<and> call_completions m call_id=None \<and> call_local_results m call_id=None"

locale durable_call_protocol =
  fixes execute :: "'command \<Rightarrow> 'state \<Rightarrow> 'state \<times> 'reply"
    and environment_execute :: "'environment \<Rightarrow> 'state \<Rightarrow> 'state \<times> 'reply"
begin

fun replay_call_authority ::
  "('command,'reply,'environment) authority_call_entry list \<Rightarrow> 'state \<Rightarrow> 'state" where
  "replay_call_authority [] state=state"
| "replay_call_authority(Authority_Executed call_id command reply#rest)state=
    replay_call_authority rest(fst(execute command state))"
| "replay_call_authority(Authority_Input environment reply#rest)state=
    replay_call_authority rest(fst(environment_execute environment state))"

fun authentic_call_history ::
  "('command,'reply,'environment) authority_call_entry list \<Rightarrow> 'state \<Rightarrow> bool" where
  "authentic_call_history [] state=True"
| "authentic_call_history(Authority_Executed call_id command reply#rest)state=
    (reply=snd(execute command state) \<and>
      authentic_call_history rest(fst(execute command state)))"
| "authentic_call_history(Authority_Input environment reply#rest)state=
    (reply=snd(environment_execute environment state) \<and>
      authentic_call_history rest(fst(environment_execute environment state)))"

lemma replay_call_authority_append [simp]:
  "replay_call_authority(first@second)state=
    replay_call_authority second(replay_call_authority first state)"
proof (induction first arbitrary:state)
  case Nil
  then show ?case by simp
next
  case (Cons entry entries)
  then show ?case by (cases entry) auto
qed

lemma authentic_call_history_append [simp]:
  "authentic_call_history(first@second)state \<longleftrightarrow>
    authentic_call_history first state \<and>
    authentic_call_history second(replay_call_authority first state)"
proof (induction first arbitrary:state)
  case Nil
  then show ?case by simp
next
  case (Cons entry entries)
  then show ?case by (cases entry) auto
qed

definition authority_replay_contract ::
  "('state,'command,'reply,'environment) durable_call_machine \<Rightarrow> bool" where
  "authority_replay_contract m \<longleftrightarrow>
    call_authority_state m=replay_call_authority(call_authority_log m)(call_genesis m) \<and>
    authentic_call_history(call_authority_log m)(call_genesis m)"

definition begin_client_call ::
  "client_call_id \<Rightarrow> 'command \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine
    \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine" where
  "begin_client_call call_id command m=
    (case call_invocations m call_id of
       None \<Rightarrow> m\<lparr>call_invocations:=(call_invocations m)(call_id:=Some(command,length(call_history m))),
         call_history:=call_history m@[Call_Began call_id command]\<rparr>
     | Some old \<Rightarrow> if fst old=command then m
       else m\<lparr>call_history:=call_history m@[Call_Payload_Rejected call_id command]\<rparr>)"

definition execute_authority_once ::
  "client_call_id \<Rightarrow> 'command \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine
    \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine" where
  "execute_authority_once call_id command m=
    (case call_authority_results m call_id of
       Some(old,reply,index) \<Rightarrow>
         if old=command then m\<lparr>call_history:=call_history m@[Call_Redispatched call_id index]\<rparr>
         else m\<lparr>call_history:=call_history m@[Call_Payload_Rejected call_id command]\<rparr>
     | None \<Rightarrow> let result=execute command(call_authority_state m);
         index=length(call_authority_log m)
       in m\<lparr>call_authority_state:=fst result,
         call_authority_log:=call_authority_log m@[Authority_Executed call_id command(snd result)],
         call_authority_results:=(call_authority_results m)(call_id:=Some(command,snd result,index)),
         call_history:=call_history m@[Call_Dispatched call_id index]\<rparr>)"

definition dispatch_client_call ::
  "client_call_id \<Rightarrow> 'command \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine
    \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine" where
  "dispatch_client_call call_id command m=
    (if call_local_status m=Endpoint_Up \<and> call_connection m=Authority_Connected
        \<and> map_option fst(call_invocations m call_id)=Some command
     then execute_authority_once call_id command m
     else m\<lparr>call_history:=call_history m@[Call_Waiting call_id]\<rparr>)"

definition collect_client_response ::
  "client_call_id \<Rightarrow> 'command \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine
    \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine" where
  "collect_client_response call_id command m=
    (if call_local_status m=Endpoint_Up \<and> call_connection m=Authority_Connected
        \<and> map_option fst(call_invocations m call_id)=Some command
     then case call_authority_results m call_id of
       None \<Rightarrow> m\<lparr>call_history:=call_history m@[Call_Waiting call_id]\<rparr>
     | Some(old,reply,index) \<Rightarrow>
         if old=command
         then m\<lparr>call_local_results:=(call_local_results m)(call_id:=Some(old,reply,index)),
           call_history:=call_history m@[Call_Response_Received call_id index]\<rparr>
         else m\<lparr>call_history:=call_history m@[Call_Payload_Rejected call_id command]\<rparr>
     else m\<lparr>call_history:=call_history m@[Call_Waiting call_id]\<rparr>)"

definition complete_client_call ::
  "client_call_id \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine
    \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine" where
  "complete_client_call call_id m=
    (if call_local_status m=Endpoint_Down \<or> call_completions m call_id\<noteq>None then m
     else case call_invocations m call_id of None \<Rightarrow> m
     | Some(command,began) \<Rightarrow>
       (case call_local_results m call_id of None \<Rightarrow> m
        | Some(old,reply,index) \<Rightarrow>
          if old=command \<and> call_authority_results m call_id=Some(command,reply,index) \<and>
              began<length(call_history m) \<and> call_history m!began=Call_Began call_id command
          then m\<lparr>call_completions:=(call_completions m)(call_id:=Some reply),
            call_history:=call_history m@[Call_Completed call_id command reply began]\<rparr>
          else m))"

definition apply_authority_input ::
  "'environment \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine
    \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine" where
  "apply_authority_input input m=
    (let result=environment_execute input(call_authority_state m)
     in m\<lparr>call_authority_state:=fst result,
       call_authority_log:=call_authority_log m@[Authority_Input input(snd result)],
       call_history:=call_history m@[Authority_Input_Recorded(length(call_authority_log m))]\<rparr>)"

fun call_step ::
  "('command,'environment) client_call_action \<Rightarrow>
    ('state,'command,'reply,'environment) durable_call_machine \<Rightarrow>
    ('state,'command,'reply,'environment) durable_call_machine" where
  "call_step(Begin_Call call_id command)m=begin_client_call call_id command m"
| "call_step(Dispatch_Call call_id command)m=dispatch_client_call call_id command m"
| "call_step(Collect_Response call_id command)m=collect_client_response call_id command m"
| "call_step(Lose_Response call_id)m=m\<lparr>call_local_results:=(call_local_results m)(call_id:=None),
    call_history:=call_history m@[Call_Response_Lost call_id]\<rparr>"
| "call_step(Complete_Call call_id)m=complete_client_call call_id m"
| "call_step Crash_Local_Endpoint m=m\<lparr>call_local_results:=(\<lambda>_.None),call_local_status:=Endpoint_Down,
    call_history:=call_history m@[Local_Endpoint_Crashed]\<rparr>"
| "call_step Recover_Local_Endpoint m=m\<lparr>call_local_status:=Endpoint_Up,
    call_history:=call_history m@[Local_Endpoint_Recovered]\<rparr>"
| "call_step(Set_Authority_Connection connection)m=m\<lparr>call_connection:=connection,
    call_history:=call_history m@[Authority_Link_Changed connection]\<rparr>"
| "call_step(Apply_Authority_Input input)m=apply_authority_input input m"

fun run_calls ::
  "('command,'environment) client_call_action list \<Rightarrow>
    ('state,'command,'reply,'environment) durable_call_machine \<Rightarrow>
    ('state,'command,'reply,'environment) durable_call_machine" where
  "run_calls [] m=m"
| "run_calls(action#rest)m=run_calls rest(call_step action m)"

lemmas call_definitions = begin_client_call_def execute_authority_once_def dispatch_client_call_def
  collect_client_response_def complete_client_call_def apply_authority_input_def

lemma call_step_keeps_genesis [simp]:
  "call_genesis(call_step action m)=call_genesis m"
  by (cases action)
    (auto simp: call_definitions Let_def split: option.splits prod.splits if_splits)

lemma run_calls_keeps_genesis [simp]:
  "call_genesis(run_calls actions m)=call_genesis m"
  by (induction actions arbitrary:m) auto

lemma recorded_call_is_not_reexecuted:
  assumes "call_authority_results m call_id=Some(old,reply,index)"
  shows "call_authority_state(execute_authority_once call_id command m)=call_authority_state m"
    "call_authority_log(execute_authority_once call_id command m)=call_authority_log m"
    "call_authority_results(execute_authority_once call_id command m)=call_authority_results m"
  using assms by (simp_all add: execute_authority_once_def)

lemma conflicting_payload_cannot_change_the_source:
  assumes "call_authority_results m call_id=Some(old,reply,index)" "old\<noteq>command"
  shows "execute_authority_once call_id command m=
    m\<lparr>call_history:=call_history m@[Call_Payload_Rejected call_id command]\<rparr>"
  using assms by (simp add: execute_authority_once_def)

lemma first_dispatch_records_the_actual_execution:
  assumes "call_authority_results m call_id=None"
  shows "call_authority_state(execute_authority_once call_id command m)=fst(execute command(call_authority_state m))"
    "call_authority_results(execute_authority_once call_id command m)call_id=
      Some(command,snd(execute command(call_authority_state m)),length(call_authority_log m))"
  using assms by (simp_all add: execute_authority_once_def Let_def)

lemma initial_dispatch_projection:
  "call_authority_state(run_calls[Begin_Call call_id command,Dispatch_Call call_id command]
    (initial_call_machine initial))=fst(execute command initial)"
  "call_authority_results(run_calls[Begin_Call call_id command,Dispatch_Call call_id command]
    (initial_call_machine initial))=(\<lambda>_.None)(call_id:=Some(command,snd(execute command initial),0))"
  "call_invocations(run_calls[Begin_Call call_id command,Dispatch_Call call_id command]
    (initial_call_machine initial))=(\<lambda>_.None)(call_id:=Some(command,0))"
  "call_completions(run_calls[Begin_Call call_id command,Dispatch_Call call_id command]
    (initial_call_machine initial))=(\<lambda>_.None)"
  "call_local_results(run_calls[Begin_Call call_id command,Dispatch_Call call_id command]
    (initial_call_machine initial))=(\<lambda>_.None)"
  "call_local_status(run_calls[Begin_Call call_id command,Dispatch_Call call_id command]
    (initial_call_machine initial))=Endpoint_Up"
  "call_connection(run_calls[Begin_Call call_id command,Dispatch_Call call_id command]
    (initial_call_machine initial))=Authority_Connected"
  "call_history(run_calls[Begin_Call call_id command,Dispatch_Call call_id command]
    (initial_call_machine initial))=[Call_Began call_id command,Call_Dispatched call_id 0]"
  by (simp_all add: initial_call_machine_def begin_client_call_def dispatch_client_call_def
      execute_authority_once_def Let_def)

lemma recorded_response_survives_every_action:
  assumes "call_authority_results m call_id=Some recorded"
  shows "call_authority_results(call_step action m)call_id=Some recorded"
  using assms
  by (cases action) (auto simp: call_definitions Let_def split: option.splits prod.splits if_splits)

theorem recorded_response_survives_every_finite_run:
  "call_authority_results m call_id=Some recorded \<Longrightarrow>
    call_authority_results(run_calls actions m)call_id=Some recorded"
  by (induction actions arbitrary:m) (auto intro: recorded_response_survives_every_action)

lemma authority_cache_contract_step:
  assumes valid: "authority_cache_contract m"
  shows "authority_cache_contract(call_step action m)"
proof -
  have extended_bound: "\<And>caller nonce command reply index.
    call_authority_results m(caller,nonce)=Some(command,reply,index) \<Longrightarrow>
    index<Suc(length(call_authority_log m))"
  proof -
    fix caller nonce command reply index
    assume found: "call_authority_results m(caller,nonce)=Some(command,reply,index)"
    have "index<length(call_authority_log m)"
      by (rule authority_cache_lookup(1)[OF valid found])
    then show "index<Suc(length(call_authority_log m))" by simp
  qed
  show ?thesis
    using valid
    by (cases action)
      (auto simp: authority_cache_contract_def call_definitions Let_def nth_append
        dest: extended_bound split: option.splits prod.splits if_splits)
qed

lemma authority_replay_contract_step:
  "authority_replay_contract m \<Longrightarrow> authority_replay_contract(call_step action m)"
  by (cases action)
    (auto simp: authority_replay_contract_def call_definitions Let_def
      split: option.splits prod.splits if_splits)

lemma completion_contract_step:
  "completion_contract m \<Longrightarrow> completion_contract(call_step action m)"
  by (cases action)
    (auto simp: completion_contract_def call_definitions Let_def
      split: option.splits prod.splits if_splits)

theorem generated_call_contracts:
  "authority_cache_contract(run_calls actions(initial_call_machine initial)) \<and>
    authority_replay_contract(run_calls actions(initial_call_machine initial)) \<and>
    completion_contract(run_calls actions(initial_call_machine initial))"
proof -
  have preserve: "\<And>m. authority_cache_contract m \<and> authority_replay_contract m \<and>
      completion_contract m \<Longrightarrow>
      authority_cache_contract(run_calls actions m) \<and> authority_replay_contract(run_calls actions m) \<and>
      completion_contract(run_calls actions m)"
    by (induction actions) (auto intro: authority_cache_contract_step authority_replay_contract_step
      completion_contract_step)
  show ?thesis
    by (rule preserve)
      (simp add: initial_call_machine_def authority_cache_contract_def authority_replay_contract_def
        completion_contract_def)
qed

theorem at_most_one_authority_execution_and_completion:
  "distinct(authority_execution_ids(call_authority_log(run_calls actions(initial_call_machine initial)))) \<and>
    distinct(completion_ids(call_history(run_calls actions(initial_call_machine initial))))"
  using generated_call_contracts
  by (simp add: authority_cache_contract_def completion_contract_def)

theorem completion_has_an_earlier_invocation_and_exact_source_result:
  assumes "call_completions m call_id=None"
    "call_completions(complete_client_call call_id m)call_id=Some reply"
  shows "\<exists>command began index.
    began<length(call_history m) \<and> call_history m!began=Call_Began call_id command \<and>
    call_authority_results m call_id=Some(command,reply,index) \<and>
    call_history(complete_client_call call_id m)=call_history m@[Call_Completed call_id command reply began]"
  using assms
  by (auto simp: complete_client_call_def split: option.splits prod.splits if_splits)

lemma completed_calls_are_not_completed_twice:
  "call_completions m call_id=Some reply \<Longrightarrow> complete_client_call call_id m=m"
  by (simp add: complete_client_call_def)

lemma crash_retains_authority_effect_and_result:
  "call_authority_state(call_step Crash_Local_Endpoint m)=call_authority_state m"
  "call_authority_log(call_step Crash_Local_Endpoint m)=call_authority_log m"
  "call_authority_results(call_step Crash_Local_Endpoint m)=call_authority_results m"
  "call_local_results(call_step Crash_Local_Endpoint m)call_id=None"
  by simp_all

lemma disconnected_recovery_does_not_invent_a_response:
  assumes "call_connection m=Authority_Disconnected" "call_local_results m call_id=None"
  shows "call_local_results(collect_client_response call_id command m)call_id=None"
    "call_authority_state(collect_client_response call_id command m)=call_authority_state m"
  using assms by (simp_all add: collect_client_response_def)

definition execute_without_once_guard ::
  "client_call_id \<Rightarrow> 'command \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine
    \<Rightarrow> ('state,'command,'reply,'environment) durable_call_machine" where
  "execute_without_once_guard call_id command m=
    (let result=execute command(call_authority_state m); index=length(call_authority_log m)
     in m\<lparr>call_authority_state:=fst result,
       call_authority_log:=call_authority_log m@[Authority_Executed call_id command(snd result)],
       call_authority_results:=(call_authority_results m)(call_id:=Some(command,snd result,index))\<rparr>)"

end

section \<open>Concrete Finality Dispatch\<close>

context source_attestation
begin

definition execute_finality_client ::
  "client_command \<Rightarrow> finality_core \<Rightarrow> finality_core \<times> finality_reply" where
  "execute_finality_client command s=
    (finality_step(client_operation s command)s,snd(core_result(client_operation s command)s))"

definition execute_finality_environment ::
  "nat \<times> lock_context \<Rightarrow> finality_core \<Rightarrow> finality_core \<times> finality_reply" where
  "execute_finality_environment input s=
    (finality_step(Install_Context(fst input)(snd input))s,
      snd(core_result(Install_Context(fst input)(snd input))s))"

sublocale finality_calls: durable_call_protocol execute_finality_client execute_finality_environment .

fun call_operations ::
  "(client_command,finality_reply,nat \<times> lock_context) authority_call_entry list \<Rightarrow>
    finality_core \<Rightarrow> finality_operation list" where
  "call_operations [] s=[]"
| "call_operations(Authority_Executed call_id command reply#rest)s=
    client_operation s command#call_operations rest(fst(execute_finality_client command s))"
| "call_operations(Authority_Input input reply#rest)s=
    Install_Context(fst input)(snd input)#call_operations rest(fst(execute_finality_environment input s))"

theorem call_replay_is_actual_finality_run:
  "finality_calls.replay_call_authority entries s=run_finality(call_operations entries s)s"
proof (induction entries arbitrary:s)
  case Nil
  then show ?case
    by (simp only: finality_calls.replay_call_authority.simps call_operations.simps run_finality.simps)
next
  case (Cons entry entries)
  show ?case
  proof (cases entry)
    case (Authority_Executed call_id command reply)
    have next_state: "fst(execute_finality_client command s)=finality_step(client_operation s command)s"
      by (simp only: execute_finality_client_def fst_conv)
    have "finality_calls.replay_call_authority(entry#entries)s=
      finality_calls.replay_call_authority entries(fst(execute_finality_client command s))"
      by (simp only: Authority_Executed finality_calls.replay_call_authority.simps)
    also have "\<dots>=run_finality
      (call_operations entries(fst(execute_finality_client command s)))
      (fst(execute_finality_client command s))"
      by (rule Cons.IH)
    also have "\<dots>=run_finality(call_operations(entry#entries)s)s"
      by (simp only: Authority_Executed call_operations.simps run_finality.simps next_state)
    finally show ?thesis .
  next
    case (Authority_Input input reply)
    have next_state: "fst(execute_finality_environment input s)=
      finality_step(Install_Context(fst input)(snd input))s"
      by (simp only: execute_finality_environment_def fst_conv)
    have "finality_calls.replay_call_authority(entry#entries)s=
      finality_calls.replay_call_authority entries(fst(execute_finality_environment input s))"
      by (simp only: Authority_Input finality_calls.replay_call_authority.simps)
    also have "\<dots>=run_finality
      (call_operations entries(fst(execute_finality_environment input s)))
      (fst(execute_finality_environment input s))"
      by (rule Cons.IH)
    also have "\<dots>=run_finality(call_operations(entry#entries)s)s"
      by (simp only: Authority_Input call_operations.simps run_finality.simps next_state)
    finally show ?thesis .
  qed
qed

theorem generated_calls_have_actual_finality_source:
  fixes actions :: "(client_command,nat \<times> lock_context) client_call_action list"
    and initial :: finality_core
  defines "m \<equiv> finality_calls.run_calls actions(initial_call_machine initial)"
  shows "call_authority_state m=
    run_finality(call_operations(call_authority_log m)initial)initial"
proof -
  have "finality_calls.authority_replay_contract m"
    using finality_calls.generated_call_contracts[of actions initial] by (simp add: m_def)
  moreover have "call_genesis m=initial"
    by (simp add: m_def initial_call_machine_def)
  ultimately show ?thesis
    by (simp add: finality_calls.authority_replay_contract_def call_replay_is_actual_finality_run)
qed

lemma first_protocol_call_uses_the_current_core:
  "execute_finality_client(Client_Protocol endpoint index intent)s=
    (finality_step(Invoke_Protocol endpoint(core_epoch s)index intent)s,
      snd(invoke_protocol endpoint(core_epoch s)index intent s))"
  by (simp add: execute_finality_client_def)

text \<open>The internal core epoch is sampled at the authority execution.
  The request's authority epoch, version, certificate, expected asset versions
  and complete client command remain unchanged. An exact retry reads the old
  durable result, even after authority replacement. A fresh call identifier
  executes again against the new current context. Denied and Busy replies are
  recorded by exactly the same path as successful replies.

  Authority execution and its durable result record form one explicit source
  boundary. Local dispatch, response collection, response loss, completion,
  crash and recovery are separate actions. Destroying the authoritative source
  log, authenticating the caller namespace, real clocks and a distributed
  implementation of that boundary are external obligations. Loss of local
  evidence does not establish that the source effect was absent.\<close>

end

section \<open>Actual Descendant Retry Witness\<close>

definition call_example_seed where
  "call_example_seed=(initial_finality_core sample_balances(sample_metadata ACTIVE)
    (\<lambda>_.sample_context ACTIVE))\<lparr>core_parent:=sample_credited\<rparr>"

definition call_example_ready where
  "call_example_ready=sample.run_finality
    [Record_Terminal(sample_certificate 17),Publish_Primary(0,17)] call_example_seed"

definition call_example_command where
  "call_example_command=Client_Protocol 2 0
    (Descendant_Intent(spend_request 17 4 1)(sample_binding 17)3 4 1)"

definition call_example_once where
  "call_example_once=sample.finality_calls.run_calls
    [Begin_Call(7,1)call_example_command,Dispatch_Call(7,1)call_example_command]
    (initial_call_machine call_example_ready)"

definition call_example_terminal where
  "call_example_terminal=\<lparr>terminal_binding=sample_binding 17,terminal_kind=Confirmed_Decision,
    terminal_evidence=[sample_certificate 17]\<rparr>"

definition call_example_intent where
  "call_example_intent=Descendant_Intent(spend_request 17 4 1)(sample_binding 17)3 4 1"

lemma call_example_command_shape:
  "call_example_command=Client_Protocol 2 0 call_example_intent"
  by (simp only: call_example_command_def call_example_intent_def)

lemma call_example_source_origin:
  "source_origin_present(sample_certificate 17)call_example_seed"
  by (simp add: source_origin_present_def call_example_seed_def initial_finality_core_def
      sample_certificate_def sample_statement_def sample_binding_def example_binding_def sample_credited_state Let_def)

lemma call_example_seed_fields:
  "core_parent call_example_seed=sample_credited"
  "core_records call_example_seed=(\<lambda>_.None)"
  "core_published call_example_seed={}"
  "core_epoch call_example_seed=0"
  by (simp_all add: call_example_seed_def initial_finality_core_def)

lemma call_example_certificate_fields:
  "statement_binding(certificate_statement(sample_certificate 17))=sample_binding 17"
  "statement_status(certificate_statement(sample_certificate 17))=Finalized"
  "binding_key(sample_binding 17)=(0,17)"
  "binding_operation(sample_binding 17)=Destination_Credit"
  by (simp_all add: sample_certificate_def sample_statement_def sample_binding_def example_binding_def)

lemma call_example_ready_shape:
  "call_example_ready=call_example_seed\<lparr>
    core_records:=(\<lambda>_.None)((0,17):=Some call_example_terminal),
    core_published:={(0,17)},core_epoch:=2\<rparr>"
  by (simp add: call_example_ready_def sample.finality_step_def sample.record_terminal_def
      sample.publish_primary_def terminal_effect_completed_def call_example_source_origin
      sample_fact_accepted call_example_terminal_def call_example_seed_fields call_example_certificate_fields
      sample_credited_state
      record_credit_def empty_message_state_def Let_def)

lemma call_example_ready_guard:
  "terminal_intent_guard call_example_ready 0 call_example_intent"
  by (simp add: call_example_intent_def record_reference_def call_example_ready_shape
      call_example_terminal_def sample_binding_def example_binding_def)

lemma call_example_ready_context:
  "current_lock_view call_example_ready 2=sample_context ACTIVE"
  by (simp add: current_lock_view_def call_example_ready_shape call_example_seed_def
      initial_finality_core_def sample_context_def)

lemma call_example_ready_parent:
  "core_parent call_example_ready=sample_credited"
  by (simp add: call_example_ready_shape call_example_seed_def)

lemma call_example_client_projection:
  assumes guard: "terminal_intent_guard state 0 call_example_intent"
    and current: "current_lock_view state 2=sample_context ACTIVE"
  shows
    "snd(sample.execute_finality_client call_example_command state)=Protocol_Response
      (snd(execute_descendant(sample_context ACTIVE)(spend_request 17 4 1)(sample_binding 17)3 4 1(core_parent state)))"
    "core_parent(fst(sample.execute_finality_client call_example_command state))=
      fst(execute_descendant(sample_context ACTIVE)(spend_request 17 4 1)(sample_binding 17)3 4 1(core_parent state))"
    "core_records(fst(sample.execute_finality_client call_example_command state))=core_records state"
    "core_published(fst(sample.execute_finality_client call_example_command state))=core_published state"
    "core_contexts(fst(sample.execute_finality_client call_example_command state))=core_contexts state"
    "core_regulatory(fst(sample.execute_finality_client call_example_command state))=core_regulatory state"
  using guard current
  by (simp_all add: sample.execute_finality_client_def call_example_command_shape
      sample.finality_step_def sample.invoke_protocol_def call_example_intent_def
      lift_protocol_result_def Let_def)

definition call_example_parent_once where
  "call_example_parent_once=fst(execute_descendant(sample_context ACTIVE)
    (spend_request 17 4 1)(sample_binding 17)3 4 1 sample_credited)"

lemmas call_example_parent_definitions = execute_descendant_def spend_request_def descendant_binding_def
  sample_credited_state sample_binding_def example_binding_def sample_request_def
  sample_context_def sample_metadata_def example_context_def initial_reservation_state_def holder_account_def
  metadata_permission_def current_use_allowed_def get_reg_state_def get_asset_state_def
  ordinary_transfer_allowed_def record_observation_def commit_reservation_event_def
  record_credit_def credit_marker_def empty_message_state_def Let_def

lemma call_example_parent_first_reply:
  "snd(execute_descendant(sample_context ACTIVE)(spend_request 17 4 1)(sample_binding 17)3 4 1
    sample_credited)=Descendant_Executed"
  by (simp add: call_example_parent_definitions)

lemma call_example_parent_first_amount:
  "destination_units(machine_state call_example_parent_once)(2,17,4)=1"
  by (simp add: call_example_parent_once_def call_example_parent_definitions)

lemma call_example_parent_repeated_amount:
  "destination_units(machine_state(fst(execute_descendant(sample_context ACTIVE)
    (spend_request 17 4 1)(sample_binding 17)3 4 1 call_example_parent_once)))(2,17,4)=2"
  by (simp add: call_example_parent_once_def call_example_parent_definitions)

definition call_example_first_core where
  "call_example_first_core=fst(sample.execute_finality_client call_example_command call_example_ready)"

lemma call_example_first_reply:
  "snd(sample.execute_finality_client call_example_command call_example_ready)=
    Protocol_Response Descendant_Executed"
  using call_example_client_projection(1)[OF call_example_ready_guard call_example_ready_context]
  by (simp only: call_example_ready_parent call_example_parent_first_reply)

lemma call_example_first_core_parent:
  "core_parent call_example_first_core=call_example_parent_once"
  using call_example_client_projection(2)[OF call_example_ready_guard call_example_ready_context]
  by (simp only: call_example_first_core_def call_example_ready_parent call_example_parent_once_def)

lemma call_example_first_core_frame:
  "core_records call_example_first_core=core_records call_example_ready"
  "core_published call_example_first_core=core_published call_example_ready"
  "core_contexts call_example_first_core=core_contexts call_example_ready"
  "core_regulatory call_example_first_core=core_regulatory call_example_ready"
  using call_example_client_projection(3-6)[OF call_example_ready_guard call_example_ready_context]
  by (simp_all only: call_example_first_core_def)

lemma call_example_second_guard:
  "terminal_intent_guard call_example_first_core 0 call_example_intent"
  using call_example_ready_guard
  by (simp add: call_example_intent_def record_reference_def call_example_first_core_frame)

lemma call_example_second_context:
  "current_lock_view call_example_first_core 2=sample_context ACTIVE"
  using call_example_ready_context
  by (simp add: current_lock_view_def call_example_first_core_frame)

lemma call_example_once_fields:
  "call_authority_state call_example_once=call_example_first_core"
  "call_authority_results call_example_once=
    (\<lambda>_.None)((7,1):=Some(call_example_command,Protocol_Response Descendant_Executed,0))"
  "call_invocations call_example_once=(\<lambda>_.None)((7,1):=Some(call_example_command,0))"
  "call_completions call_example_once=(\<lambda>_.None)"
  "call_local_results call_example_once=(\<lambda>_.None)"
  "call_local_status call_example_once=Endpoint_Up"
  "call_connection call_example_once=Authority_Connected"
  "call_history call_example_once=[Call_Began(7,1)call_example_command,Call_Dispatched(7,1)0]"
  by (simp_all only: call_example_once_def sample.finality_calls.initial_dispatch_projection
      call_example_first_core_def call_example_first_reply)

lemma actual_descendant_call_succeeds:
  "call_authority_results call_example_once(7,1)=
    Some(call_example_command,Protocol_Response Descendant_Executed,0) \<and>
   destination_units(machine_state(core_parent(call_authority_state call_example_once)))(2,17,4)=1"
  by (simp add: call_example_once_fields call_example_first_core_parent call_example_parent_first_amount)

lemma exact_retry_keeps_the_actual_descendant_effect:
  "call_authority_state(sample.finality_calls.execute_authority_once(7,1)call_example_command
      call_example_once)=call_authority_state call_example_once"
  by (rule sample.finality_calls.recorded_call_is_not_reexecuted(1))
    (use actual_descendant_call_succeeds in auto)

lemma removing_once_guard_repeats_the_actual_descendant:
  "destination_units(machine_state(core_parent(call_authority_state
    (sample.finality_calls.execute_without_once_guard(7,1)call_example_command call_example_once))))(2,17,4)=2"
proof -
  have parent: "core_parent(fst(sample.execute_finality_client call_example_command call_example_first_core))=
    fst(execute_descendant(sample_context ACTIVE)(spend_request 17 4 1)(sample_binding 17)3 4 1
      call_example_parent_once)"
    using call_example_client_projection(2)[OF call_example_second_guard call_example_second_context]
    by (simp only: call_example_first_core_parent)
  have source: "call_authority_state
    (sample.finality_calls.execute_without_once_guard(7,1)call_example_command call_example_once)=
    fst(sample.execute_finality_client call_example_command call_example_first_core)"
    by (simp add: sample.finality_calls.execute_without_once_guard_def Let_def call_example_once_fields)
  have "destination_units(machine_state(core_parent(call_authority_state
    (sample.finality_calls.execute_without_once_guard(7,1)call_example_command call_example_once))))(2,17,4)=
    destination_units(machine_state(fst(execute_descendant(sample_context ACTIVE)
      (spend_request 17 4 1)(sample_binding 17)3 4 1 call_example_parent_once)))(2,17,4)"
    by (simp only: source parent)
  also have "\<dots>=2" by (rule call_example_parent_repeated_amount)
  finally show ?thesis .
qed

definition call_example_after_crash where
  "call_example_after_crash=sample.finality_calls.run_calls
    [Crash_Local_Endpoint,Recover_Local_Endpoint,
      Collect_Response(7,1)call_example_command,Complete_Call(7,1),Complete_Call(7,1)]
    call_example_once"

lemma source_effect_precedes_local_response_and_completion:
  "call_local_results call_example_once(7,1)=None \<and>
    call_completions call_example_once(7,1)=None \<and>
    destination_units(machine_state(core_parent(call_authority_state call_example_once)))(2,17,4)=1"
  by (simp add: call_example_once_fields call_example_first_core_parent call_example_parent_first_amount)

lemma crash_recovery_completes_the_old_result_once:
  "call_completions call_example_after_crash(7,1)=Some(Protocol_Response Descendant_Executed) \<and>
    completion_ids(call_history call_example_after_crash)=[(7,1)] \<and>
    destination_units(machine_state(core_parent(call_authority_state call_example_after_crash)))(2,17,4)=1"
  by (simp add: call_example_after_crash_def sample.finality_calls.collect_client_response_def
      sample.finality_calls.complete_client_call_def call_example_once_fields
      call_example_first_core_parent call_example_parent_first_amount)

definition call_example_permission_changed where
  "call_example_permission_changed=sample.finality_calls.call_step
    (Apply_Authority_Input(2,(sample_context ACTIVE)\<lparr>lock_spend_permissions:={}\<rparr>))call_example_once"

lemma past_reply_and_fresh_permission_check_are_distinct:
  "call_authority_results call_example_permission_changed(7,1)=
      Some(call_example_command,Protocol_Response Descendant_Executed,0) \<and>
    snd(sample.execute_finality_client call_example_command
      (call_authority_state call_example_permission_changed))=Protocol_Response Request_Rejected"
proof -
  have recorded: "call_authority_results call_example_permission_changed(7,1)=
    Some(call_example_command,Protocol_Response Descendant_Executed,0)"
    by (simp add: call_example_permission_changed_def sample.finality_calls.apply_authority_input_def
        Let_def call_example_once_fields)
  have changed_source: "call_authority_state call_example_permission_changed=
    sample.finality_step
      (Install_Context 2((sample_context ACTIVE)\<lparr>lock_spend_permissions:={}\<rparr>))call_example_first_core"
  proof -
    have projected: "call_authority_state call_example_permission_changed=
      fst(sample.execute_finality_environment
        (2,(sample_context ACTIVE)\<lparr>lock_spend_permissions:={}\<rparr>)call_example_first_core)"
      by (simp add: call_example_permission_changed_def sample.finality_calls.apply_authority_input_def
          Let_def call_example_once_fields)
    show ?thesis using projected
      by (simp only: sample.execute_finality_environment_def fst_conv snd_conv)
  qed
  have denied: "snd(sample.execute_finality_client call_example_command
    (call_authority_state call_example_permission_changed))=Protocol_Response Request_Rejected"
    by (simp add: changed_source sample.execute_finality_client_def call_example_command_shape
        sample.finality_step_def sample.invoke_protocol_def current_lock_view_def call_example_intent_def
        record_reference_def lift_protocol_result_def execute_descendant_def call_example_first_core_frame
        call_example_ready_shape call_example_seed_def initial_finality_core_def call_example_terminal_def
        sample_context_def example_context_def sample_binding_def example_binding_def record_observation_def Let_def)
  show ?thesis using recorded denied by blast
qed

text \<open>The witness starts with the parent's actual source, credit and
  reconciliation trace. Terminal recording and primary publication use the
  child dispatcher. Removing only call-identity reuse then performs the same
  funded descendant transfer twice. The source result table is therefore
  distinct from the parent's transfer-root credit replay protection.\<close>

end
