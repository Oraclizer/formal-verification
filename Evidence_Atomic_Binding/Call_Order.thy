(* SPDX-License-Identifier: BSD-3-Clause *)
theory Call_Order
  imports Finality_Observations
begin

section \<open>Source Positions of Invoked and Completed Calls\<close>

definition call_lifecycle_contract ::
  "('state,'command,'reply,'environment) durable_call_machine \<Rightarrow> bool" where
  "call_lifecycle_contract m \<longleftrightarrow>
    (\<forall>call_id command reply index.
      call_authority_results m call_id=Some(command,reply,index) \<longrightarrow>
      (\<exists>began. call_invocations m call_id=Some(command,began))) \<and>
    (\<forall>call_id reply. call_completions m call_id=Some reply \<longrightarrow>
      (\<exists>command index. call_authority_results m call_id=Some(command,reply,index)))"

lemma source_result_has_invocation:
  assumes "call_lifecycle_contract m"
    "call_authority_results m call_id=Some(command,reply,index)"
  shows "\<exists>began. call_invocations m call_id=Some(command,began)"
  using assms unfolding call_lifecycle_contract_def by blast

lemma completed_result_has_source:
  assumes "call_lifecycle_contract m" "call_completions m call_id=Some reply"
  shows "\<exists>command index. call_authority_results m call_id=Some(command,reply,index)"
  using assms unfolding call_lifecycle_contract_def by blast

lemma not_invoked_has_no_source_result:
  assumes "call_lifecycle_contract m" "call_invocations m call_id=None"
  shows "call_authority_results m call_id=None"
proof (cases "call_authority_results m call_id")
  case None
  then show ?thesis .
next
  case (Some stored)
  obtain command reply index where shape: "stored=(command,reply,index)"
    by (cases stored) auto
  have "\<exists>began. call_invocations m call_id=Some(command,began)"
    by (rule source_result_has_invocation[OF assms(1)]) (simp add: Some shape)
  then show ?thesis using assms(2) by simp
qed

lemma no_source_result_has_no_completion:
  assumes valid: "call_lifecycle_contract m" and missing: "call_authority_results m call_id=None"
  shows "call_completions m call_id=None"
proof (cases "call_completions m call_id")
  case None
  then show ?thesis .
next
  case (Some reply)
  have "\<exists>command index. call_authority_results m call_id=Some(command,reply,index)"
    by (rule completed_result_has_source[OF valid Some])
  then show ?thesis using missing by simp
qed

context durable_call_protocol
begin

lemma run_calls_append:
  "run_calls(first@second)m=run_calls second(run_calls first m)"
  by (induction first arbitrary:m) auto

lemma call_lifecycle_contract_step:
  assumes valid: "call_lifecycle_contract m"
  shows "call_lifecycle_contract(call_step action m)"
proof (cases action)
  case (Begin_Call call_id command)
  show ?thesis
  proof (cases "call_invocations m call_id")
    case None
    have source_none: "call_authority_results m call_id=None"
      by (rule not_invoked_has_no_source_result[OF valid None])
    show ?thesis using valid source_none
      by (auto simp: Begin_Call begin_client_call_def None call_lifecycle_contract_def)
  next
    case (Some invocation)
    then show ?thesis using valid
      by (auto simp: Begin_Call begin_client_call_def call_lifecycle_contract_def
          split: prod.splits if_splits)
  qed
next
  case (Dispatch_Call call_id command)
  show ?thesis
  proof (cases "call_local_status m=Endpoint_Up \<and> call_connection m=Authority_Connected \<and>
      map_option fst(call_invocations m call_id)=Some command")
    case False
    have stopped: "dispatch_client_call call_id command m=
      m\<lparr>call_history:=call_history m@[Call_Waiting call_id]\<rparr>"
      by (simp only: dispatch_client_call_def False if_False)
    show ?thesis using valid
      by (simp add: Dispatch_Call stopped call_lifecycle_contract_def)
  next
    case True
    obtain began where invocation: "call_invocations m call_id=Some(command,began)"
      using True by (cases "call_invocations m call_id") auto
    have once: "call_lifecycle_contract(execute_authority_once call_id command m)"
    proof (cases "call_authority_results m call_id")
      case None
      have completion_none: "call_completions m call_id=None"
        by (rule no_source_result_has_no_completion[OF valid None])
      show ?thesis using valid invocation completion_none
        by (auto simp: execute_authority_once_def None Let_def call_lifecycle_contract_def)
    next
      case (Some stored)
      then show ?thesis using valid
        by (auto simp: execute_authority_once_def call_lifecycle_contract_def
            split: prod.splits if_splits)
    qed
    show ?thesis using once True
      by (simp add: Dispatch_Call dispatch_client_call_def)
  qed
next
  case (Collect_Response call_id command)
  then show ?thesis using valid
    by (auto simp: collect_client_response_def call_lifecycle_contract_def
        split: option.splits prod.splits if_splits)
next
  case (Lose_Response call_id)
  then show ?thesis using valid by (simp add: call_lifecycle_contract_def)
next
  case (Complete_Call call_id)
  then show ?thesis using valid
    by (auto simp: complete_client_call_def call_lifecycle_contract_def
        split: option.splits prod.splits if_splits)
next
  case Crash_Local_Endpoint
  then show ?thesis using valid by (simp add: call_lifecycle_contract_def)
next
  case Recover_Local_Endpoint
  then show ?thesis using valid by (simp add: call_lifecycle_contract_def)
next
  case (Set_Authority_Connection connection)
  then show ?thesis using valid by (simp add: call_lifecycle_contract_def)
next
  case (Apply_Authority_Input input)
  then show ?thesis using valid by (simp add: apply_authority_input_def Let_def call_lifecycle_contract_def)
qed

theorem generated_call_lifecycle_contract:
  "call_lifecycle_contract(run_calls actions(initial_call_machine initial))"
proof -
  have preserve: "\<And>m. call_lifecycle_contract m \<Longrightarrow>
    call_lifecycle_contract(run_calls actions m)"
    by (induction actions) (auto intro: call_lifecycle_contract_step)
  show ?thesis by (rule preserve)
    (simp add: initial_call_machine_def call_lifecycle_contract_def)
qed

lemma authority_log_step_shape:
  "call_authority_log(call_step action m)=call_authority_log m \<or>
    (\<exists>entry. call_authority_log(call_step action m)=call_authority_log m@[entry])"
  by (cases action)
    (auto simp: call_definitions Let_def split: option.splits prod.splits if_splits)

lemma authority_log_step_extends:
  "\<exists>suffix. call_authority_log(call_step action m)=call_authority_log m@suffix"
  using authority_log_step_shape[of action m]
  by (metis append_Nil2)

lemma authority_log_run_extends:
  "\<exists>suffix. call_authority_log(run_calls actions m)=call_authority_log m@suffix"
proof (induction actions arbitrary:m)
  case Nil
  then show ?case by simp
next
  case (Cons action actions)
  obtain first where first:
    "call_authority_log(call_step action m)=call_authority_log m@first"
    using authority_log_step_extends by blast
  obtain second where second:
    "call_authority_log(run_calls actions(call_step action m))=
      call_authority_log(call_step action m)@second"
    using Cons.IH by blast
  show ?case using first second
    by (intro exI[where x="first@second"]) (simp add: append_assoc)
qed

lemma authority_log_length_step:
  "length(call_authority_log m)\<le>length(call_authority_log(call_step action m))"
  using authority_log_step_extends[of action m] by auto

lemma fresh_step_result_has_next_source_index:
  assumes missing: "call_authority_results m call_id=None"
    and added: "call_authority_results(call_step action m)call_id=Some(command,reply,index)"
  shows "index=length(call_authority_log m)"
  using missing added
  by (cases action)
    (auto simp: call_definitions Let_def split: option.splits prod.splits if_splits)

theorem new_result_is_not_before_its_source_cut:
  assumes missing: "call_authority_results m call_id=None"
    and found: "call_authority_results(run_calls actions m)call_id=Some(command,reply,index)"
  shows "length(call_authority_log m)\<le>index"
  using missing found
proof (induction actions arbitrary:m)
  case Nil
  then show ?case by simp
next
  case (Cons action actions)
  show ?case
  proof (cases "call_authority_results(call_step action m)call_id")
    case None
    have later: "length(call_authority_log(call_step action m))\<le>index"
      by (rule Cons.IH[OF None]) (use Cons.prems(2) in simp)
    show ?thesis by (rule order_trans[OF authority_log_length_step later])
  next
    case (Some stored)
    have retained: "call_authority_results(run_calls actions(call_step action m))call_id=Some stored"
      by (rule recorded_response_survives_every_finite_run[OF Some])
    have same: "stored=(command,reply,index)" using retained Cons.prems(2) by simp
    have at_step: "call_authority_results(call_step action m)call_id=Some(command,reply,index)"
      using Some same by simp
    have "index=length(call_authority_log m)"
      by (rule fresh_step_result_has_next_source_index[OF Cons.prems(1) at_step])
    then show ?thesis by simp
  qed
qed

lemma authentic_history_reply_at_index:
  assumes authentic: "authentic_call_history entries initial"
    and bound: "index<length entries"
    and at: "entries!index=Authority_Executed call_id command reply"
  shows "reply=snd(execute command(replay_call_authority(take index entries)initial))"
  using authentic bound at
proof (induction entries arbitrary:initial index)
  case Nil
  then show ?case by simp
next
  case (Cons entry entries)
  then show ?case by (cases index; cases entry) auto
qed

lemma cached_result_is_the_actual_indexed_reply:
  assumes cache: "authority_cache_contract m"
    and replay: "authority_replay_contract m"
    and found: "call_authority_results m call_id=Some(command,reply,index)"
  shows "reply=snd(execute command
    (replay_call_authority(take index(call_authority_log m))(call_genesis m)))"
proof -
  have bound: "index<length(call_authority_log m)"
    by (rule authority_cache_lookup(1)[OF cache found])
  have at: "call_authority_log m!index=Authority_Executed call_id command reply"
    by (rule authority_cache_lookup(2)[OF cache found])
  have authentic: "authentic_call_history(call_authority_log m)(call_genesis m)"
    using replay unfolding authority_replay_contract_def by blast
  show ?thesis by (rule authentic_history_reply_at_index[OF authentic bound at])
qed

lemma begin_keeps_source [simp]:
  "call_authority_state(begin_client_call call_id command m)=call_authority_state m"
  "call_authority_results(begin_client_call call_id command m)=call_authority_results m"
  "call_authority_log(begin_client_call call_id command m)=call_authority_log m"
  by (auto simp: begin_client_call_def split: option.splits prod.splits if_splits)

lemma completion_keeps_source [simp]:
  "call_authority_state(complete_client_call call_id m)=call_authority_state m"
  "call_authority_results(complete_client_call call_id m)=call_authority_results m"
  "call_authority_log(complete_client_call call_id m)=call_authority_log m"
  by (auto simp: complete_client_call_def split: option.splits prod.splits if_splits)

lemma fresh_begin_is_a_new_invocation_event:
  "call_invocations m call_id=None \<Longrightarrow>
    call_history(begin_client_call call_id command m)=call_history m@[Call_Began call_id command]"
  by (simp add: begin_client_call_def)

end

locale revision_ordered_calls = durable_call_protocol execute environment_execute
  for execute :: "'command \<Rightarrow> 'state \<Rightarrow> 'state \<times> 'reply"
    and environment_execute :: "'environment \<Rightarrow> 'state \<Rightarrow> 'state \<times> 'reply" +
  fixes revision :: "'state \<Rightarrow> nat"
  assumes execution_nondecreasing: "revision state\<le>revision(fst(execute command state))"
    and environment_nondecreasing: "revision state\<le>revision(fst(environment_execute input state))"
begin

lemma authority_replay_revision_nondecreasing:
  "revision initial\<le>revision(replay_call_authority entries initial)"
proof (induction entries arbitrary:initial)
  case Nil
  then show ?case by simp
next
  case (Cons entry entries)
  show ?case
  proof (cases entry)
    case (Authority_Executed call_id command reply)
    have "revision initial\<le>revision(fst(execute command initial))"
      by (rule execution_nondecreasing)
    also have "\<dots>\<le>revision(replay_call_authority entries(fst(execute command initial)))"
      by (rule Cons.IH)
    finally show ?thesis by (simp add: Authority_Executed)
  next
    case (Authority_Input input reply)
    have "revision initial\<le>revision(fst(environment_execute input initial))"
      by (rule environment_nondecreasing)
    also have "\<dots>\<le>revision(replay_call_authority entries(fst(environment_execute input initial)))"
      by (rule Cons.IH)
    finally show ?thesis by (simp add: Authority_Input)
  qed
qed

lemma authority_prefix_revision_le:
  "revision(replay_call_authority(take index entries)initial)\<le>
    revision(replay_call_authority entries initial)"
proof -
  have le: "revision(replay_call_authority(take index entries)initial)\<le>
    revision(replay_call_authority(drop index entries)
      (replay_call_authority(take index entries)initial))"
    by (rule authority_replay_revision_nondecreasing)
  show ?thesis using le
    by (simp only: replay_call_authority_append[symmetric] append_take_drop_id)
qed

lemma authority_prefix_revision_order:
  assumes "first\<le>second"
  shows "revision(replay_call_authority(take first entries)initial)\<le>
    revision(replay_call_authority(take second entries)initial)"
  using authority_prefix_revision_le[of first "take second entries" initial] assms
  by (simp add: take_take min.absorb1)

lemma call_step_revision_nondecreasing:
  "revision(call_authority_state m)\<le>revision(call_authority_state(call_step action m))"
  by (cases action)
    (auto simp: call_definitions Let_def
      intro: execution_nondecreasing environment_nondecreasing
      split: option.splits prod.splits if_splits)

lemma call_run_revision_nondecreasing:
  "revision(call_authority_state m)\<le>revision(call_authority_state(run_calls actions m))"
proof (induction actions arbitrary:m)
  case Nil
  then show ?case by simp
next
  case (Cons action actions)
  have first: "revision(call_authority_state m)\<le>revision(call_authority_state(call_step action m))"
    by (rule call_step_revision_nondecreasing)
  have later: "revision(call_authority_state(call_step action m))\<le>
    revision(call_authority_state(run_calls actions(call_step action m)))"
    by (rule Cons.IH)
  show ?case using order_trans[OF first later] by simp
qed

theorem fresh_result_execution_is_after_the_initial_cut:
  assumes replay: "authority_replay_contract m"
    and missing: "call_authority_results m call_id=None"
    and found: "call_authority_results(run_calls actions m)call_id=Some(command,reply,index)"
  shows "revision(call_authority_state m)\<le>
    revision(replay_call_authority(take index(call_authority_log(run_calls actions m)))
      (call_genesis(run_calls actions m)))"
proof -
  obtain suffix where extension:
    "call_authority_log(run_calls actions m)=call_authority_log m@suffix"
    using authority_log_run_extends by blast
  have bound: "length(call_authority_log m)\<le>index"
    by (rule new_result_is_not_before_its_source_cut[OF missing found])
  have ordered: "revision(replay_call_authority
      (take(length(call_authority_log m))(call_authority_log(run_calls actions m)))(call_genesis m))\<le>
    revision(replay_call_authority(take index(call_authority_log(run_calls actions m)))(call_genesis m))"
    by (rule authority_prefix_revision_order[OF bound])
  have at_cut: "replay_call_authority
    (take(length(call_authority_log m))(call_authority_log(run_calls actions m)))(call_genesis m)=
    call_authority_state m"
    using replay by (simp add: extension authority_replay_contract_def)
  show ?thesis using ordered by (simp only: at_cut run_calls_keeps_genesis)
qed

end

section \<open>Nonoverlapping Current Queries\<close>

context source_attestation
begin

sublocale observed_order: revision_ordered_calls execute_observed execute_observed_environment
  "\<lambda>state. core_epoch(observed_core state)"
  by unfold_locales
    (rule observation_steps_do_not_decrease_authority_revision,
     rule environment_steps_do_not_decrease_authority_revision)

lemma any_current_reply_has_actual_revision:
  assumes "snd(execute_observed command state)=Current_Value revision value"
  shows "revision=core_epoch(observed_core state)"
  using assms
  by (cases command)
    (auto simp: current_query_reply_def current_cache_valid_def capture_snapshot_def
      historical_query_reply_def store_core_result_def Let_def
      dest: protected_current_response_has_revision
      split: option.splits if_splits)

lemma cached_current_reply_is_no_later_than_current_source:
  assumes cache: "authority_cache_contract m"
    and replay: "observed_calls.authority_replay_contract m"
    and found: "call_authority_results m call_id=Some(command,Current_Value revision value,index)"
  shows "revision\<le>core_epoch(observed_core(call_authority_state m))"
proof -
  have actual: "Current_Value revision value=snd(execute_observed command
    (observed_calls.replay_call_authority(take index(call_authority_log m))(call_genesis m)))"
    by (rule observed_calls.cached_result_is_the_actual_indexed_reply[OF cache replay found])
  have issued: "revision=core_epoch(observed_core
    (observed_calls.replay_call_authority(take index(call_authority_log m))(call_genesis m)))"
    by (rule any_current_reply_has_actual_revision[OF actual[symmetric]])
  have order: "core_epoch(observed_core
      (observed_calls.replay_call_authority(take index(call_authority_log m))(call_genesis m)))\<le>
    core_epoch(observed_core(observed_calls.replay_call_authority(call_authority_log m)(call_genesis m)))"
    by (rule observed_order.authority_prefix_revision_le)
  show ?thesis using order replay
    by (simp add: issued observed_calls.authority_replay_contract_def)
qed

lemma fresh_current_reply_is_not_older_than_its_source_cut:
  assumes initial_replay: "observed_calls.authority_replay_contract m"
    and final_cache: "authority_cache_contract(observed_calls.run_calls actions m)"
    and final_replay: "observed_calls.authority_replay_contract(observed_calls.run_calls actions m)"
    and missing: "call_authority_results m call_id=None"
    and found: "call_authority_results(observed_calls.run_calls actions m)call_id=
      Some(command,Current_Value revision value,index)"
  shows "core_epoch(observed_core(call_authority_state m))\<le>revision"
proof -
  have actual: "Current_Value revision value=snd(execute_observed command
    (observed_calls.replay_call_authority
      (take index(call_authority_log(observed_calls.run_calls actions m)))
      (call_genesis(observed_calls.run_calls actions m))))"
    by (rule observed_calls.cached_result_is_the_actual_indexed_reply[OF final_cache final_replay found])
  have issued: "revision=core_epoch(observed_core
    (observed_calls.replay_call_authority
      (take index(call_authority_log(observed_calls.run_calls actions m)))
      (call_genesis(observed_calls.run_calls actions m))))"
    by (rule any_current_reply_has_actual_revision[OF actual[symmetric]])
  have ordered: "core_epoch(observed_core(call_authority_state m))\<le>
    core_epoch(observed_core(observed_calls.replay_call_authority
      (take index(call_authority_log(observed_calls.run_calls actions m)))
      (call_genesis(observed_calls.run_calls actions m))))"
    by (rule observed_order.fresh_result_execution_is_after_the_initial_cut[OF initial_replay missing found])
  show ?thesis using ordered by (simp only: issued)
qed

theorem later_invoked_current_call_cannot_complete_an_older_revision:
  fixes before gap after :: "(observed_command,observed_environment) client_call_action list"
    and initial :: observed_finality
  assumes before_state: "before_completion=observed_calls.run_calls before(initial_call_machine initial)"
    and completion_state: "after_completion=observed_calls.call_step(Complete_Call first_call)before_completion"
    and first_not_done: "call_completions before_completion first_call=None"
    and first_done: "call_completions after_completion first_call=Some(Current_Value first_revision first_value)"
    and gap_state: "before_begin=observed_calls.run_calls gap after_completion"
    and fresh_invocation: "call_invocations before_begin later_call=None"
    and begin_state:
      "after_begin=observed_calls.call_step(Begin_Call later_call later_request)before_begin"
    and final_state: "finished=observed_calls.run_calls after after_begin"
    and later_done: "call_completions finished later_call=Some(Current_Value later_revision later_value)"
  shows "first_revision\<le>later_revision"
proof -
  have generated_before: "authority_cache_contract before_completion \<and>
    observed_calls.authority_replay_contract before_completion"
    using observed_calls.generated_call_contracts[of before initial] before_state by simp
  have before_begin_trace: "before_begin=observed_calls.run_calls
    (before@[Complete_Call first_call]@gap)(initial_call_machine initial)"
    by (simp add: before_state completion_state gap_state observed_calls.run_calls_append)
  have after_begin_trace: "after_begin=observed_calls.run_calls
    (before@[Complete_Call first_call]@gap@[Begin_Call later_call later_request])
    (initial_call_machine initial)"
    by (simp add: before_begin_trace begin_state observed_calls.run_calls_append)
  have finished_trace: "finished=observed_calls.run_calls
    (before@[Complete_Call first_call]@gap@[Begin_Call later_call later_request]@after)
    (initial_call_machine initial)"
    by (simp add: final_state after_begin_trace observed_calls.run_calls_append)
  have generated_after_begin: "observed_calls.authority_replay_contract after_begin"
    using observed_calls.generated_call_contracts
      [of "before@[Complete_Call first_call]@gap@[Begin_Call later_call later_request]" initial]
    by (simp only: after_begin_trace[symmetric])
  have generated_finished: "authority_cache_contract finished \<and>
    observed_calls.authority_replay_contract finished"
    using observed_calls.generated_call_contracts
      [of "before@[Complete_Call first_call]@gap@[Begin_Call later_call later_request]@after" initial]
    by (simp only: finished_trace[symmetric])
  have life_before_begin: "call_lifecycle_contract before_begin"
    using observed_calls.generated_call_lifecycle_contract
      [of "before@[Complete_Call first_call]@gap" initial]
    by (simp only: before_begin_trace[symmetric])
  have life_finished: "call_lifecycle_contract finished"
    using observed_calls.generated_call_lifecycle_contract
      [of "before@[Complete_Call first_call]@gap@[Begin_Call later_call later_request]@after" initial]
    by (simp only: finished_trace[symmetric])
  obtain first_command first_index where first_source:
    "call_authority_results before_completion first_call=
      Some(first_command,Current_Value first_revision first_value,first_index)"
    using observed_calls.completion_has_an_earlier_invocation_and_exact_source_result
      [OF first_not_done] first_done completion_state by auto
  have first_upper: "first_revision\<le>core_epoch(observed_core(call_authority_state before_completion))"
    by (rule cached_current_reply_is_no_later_than_current_source[OF _ _ first_source])
      (use generated_before in auto)
  have complete_same: "call_authority_state after_completion=call_authority_state before_completion"
    by (simp add: completion_state)
  have gap_order: "core_epoch(observed_core(call_authority_state after_completion))\<le>
    core_epoch(observed_core(call_authority_state before_begin))"
    unfolding gap_state by (rule observed_order.call_run_revision_nondecreasing)
  have begin_same: "call_authority_state after_begin=call_authority_state before_begin"
    by (simp add: begin_state)
  have no_earlier_source: "call_authority_results before_begin later_call=None"
    by (rule not_invoked_has_no_source_result[OF life_before_begin fresh_invocation])
  have no_source_at_begin: "call_authority_results after_begin later_call=None"
    by (simp add: begin_state no_earlier_source)
  obtain later_command later_index where later_source:
    "call_authority_results finished later_call=
      Some(later_command,Current_Value later_revision later_value,later_index)"
    using completed_result_has_source[OF life_finished later_done] by blast
  have later_lower: "core_epoch(observed_core(call_authority_state after_begin))\<le>later_revision"
    by (rule fresh_current_reply_is_not_older_than_its_source_cut[OF generated_after_begin _ _
          no_source_at_begin])
      (use generated_finished later_source in \<open>auto simp: final_state\<close>)
  have between: "core_epoch(observed_core(call_authority_state before_completion))\<le>
    core_epoch(observed_core(call_authority_state after_begin))"
    using gap_order by (simp only: complete_same begin_same)
  have first_before_begin: "first_revision\<le>core_epoch(observed_core(call_authority_state after_begin))"
    by (rule order_trans[OF first_upper between])
  show ?thesis by (rule order_trans[OF first_before_begin later_lower])
qed

text \<open>The interval order uses a new invocation after the first completed
  call, with arbitrary intervening and subsequent actions. The durable log
  positions and actual replay determine the ordering of successful revisions.
  An old invocation whose response was delayed may overlap a newer completed
  call and is intentionally outside this nonoverlapping conclusion.
  Historical and raw responses remain separate reply constructors. No
  monotonicity of account balances or other application payloads is claimed.\<close>

end

end
