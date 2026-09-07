(* SPDX-License-Identifier: BSD-3-Clause *)
theory Observed_Protocol_Link
  imports Finality_Refinement Call_Order
begin

section \<open>Operations Selected by the Actual Observation Callbacks\<close>

fun optional_finality_word :: "finality_operation option \<Rightarrow> finality_operation list" where
  "optional_finality_word None=[]"
| "optional_finality_word(Some operation)=[operation]"

context source_attestation
begin

definition protected_read_operation :: "nat \<Rightarrow> nat \<Rightarrow> execution_request \<Rightarrow>
  application_query \<Rightarrow> observed_finality \<Rightarrow> finality_operation option" where
  "protected_read_operation endpoint index r query s =
    (if \<not>protected_read_access endpoint index r query s then None
     else case current_query_reply endpoint query s of
       Current_Value revision value \<Rightarrow>
         (case query of Application_Value asset \<Rightarrow>
           (case snd(execute_finality_client(Client_Protocol endpoint index(Data_Read_Intent r))(observed_core s)) of
             Protocol_Response(Value_Response amount) \<Rightarrow>
               Some(client_operation(observed_core s)(Client_Protocol endpoint index(Data_Read_Intent r)))
           | _ \<Rightarrow> None)
          | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)"

fun observed_operation :: "observed_command \<Rightarrow> observed_finality \<Rightarrow> finality_operation option" where
  "observed_operation(Read_Protected_Current endpoint index r query)s =
    protected_read_operation endpoint index r query s"
| "observed_operation(Execute_Current endpoint command)s =
    (if current_cache_valid s endpoint then Some(client_operation(observed_core s)command) else None)"
| "observed_operation _ s=None"

fun observed_environment_operation :: "observed_environment \<Rightarrow> finality_operation option" where
  "observed_environment_operation(Replace_Current_Context endpoint c)=Some(Install_Context endpoint c)"
| "observed_environment_operation _=None"

lemma stored_result_projects_its_actual_core [simp]:
  "observed_core(fst(store_core_result result s))=fst result"
  by (simp add: store_core_result_def Let_def)

theorem protected_read_projects_its_actual_operation:
  "observed_core(fst(execute_protected_current endpoint index r query s)) =
    run_finality(optional_finality_word(protected_read_operation endpoint index r query s))(observed_core s)"
  by (auto simp: execute_protected_current_def protected_read_operation_def Let_def
      execute_finality_client_def store_core_result_def
      split: if_splits observed_reply.splits application_query.splits
        finality_reply.splits reservation_reply.splits)

theorem observed_callback_projects_its_actual_operation:
  "observed_core(fst(execute_observed command s)) =
    run_finality(optional_finality_word(observed_operation command s))(observed_core s)"
proof (cases command)
  case (Read_Protected_Current endpoint index r query)
  show ?thesis by (simp only: Read_Protected_Current execute_observed.simps observed_operation.simps
      protected_read_projects_its_actual_operation)
qed (auto simp: execute_finality_client_def store_core_result_def Let_def split: if_splits)

theorem observed_environment_projects_its_actual_operation:
  "observed_core(fst(execute_observed_environment input s)) =
    run_finality(optional_finality_word(observed_environment_operation input))(observed_core s)"
  by (cases input) (simp_all add: execute_finality_environment_def store_core_result_def Let_def)

text \<open>The operation selectors describe existing callback branches.
  They neither restrict the input alphabet nor add a guard to execution.
  An Execute Current callback that reaches the authority emits its operation
  even when that authority operation rejects: its actual core step still
  advances the authority revision. A rejected protected application read
  emits no operation when its callback returns the original observed state.\<close>

section \<open>Each Durable Source Entry Has an Actual Core Word\<close>

fun observed_source_operations ::
  "(observed_command,observed_reply,observed_environment) authority_call_entry list \<Rightarrow>
    observed_finality \<Rightarrow> finality_operation list" where
  "observed_source_operations [] s=[]"
| "observed_source_operations(Authority_Executed call_id command reply#rest)s =
    optional_finality_word(observed_operation command s)@
      observed_source_operations rest(fst(execute_observed command s))"
| "observed_source_operations(Authority_Input input reply#rest)s =
    optional_finality_word(observed_environment_operation input)@
      observed_source_operations rest(fst(execute_observed_environment input s))"

theorem observed_replay_projects_to_actual_finality_run:
  "observed_core(observed_calls.replay_call_authority entries s) =
    run_finality(observed_source_operations entries s)(observed_core s)"
proof (induction entries arbitrary:s)
  case Nil
  then show ?case
    by (simp only: observed_calls.replay_call_authority.simps observed_source_operations.simps run_finality.simps)
next
  case (Cons entry entries)
  show ?case
  proof (cases entry)
    case (Authority_Executed call_id command reply)
    have "observed_core(observed_calls.replay_call_authority(entry#entries)s) =
      observed_core(observed_calls.replay_call_authority entries(fst(execute_observed command s)))"
      by (simp only: Authority_Executed observed_calls.replay_call_authority.simps)
    also have "\<dots> = run_finality
      (observed_source_operations entries(fst(execute_observed command s)))
      (observed_core(fst(execute_observed command s)))"
      by (rule Cons.IH)
    also have "\<dots> = run_finality(observed_source_operations(entry#entries)s)(observed_core s)"
      by (simp only: Authority_Executed observed_source_operations.simps finality_run_append
          observed_callback_projects_its_actual_operation)
    finally show ?thesis .
  next
    case (Authority_Input input reply)
    have "observed_core(observed_calls.replay_call_authority(entry#entries)s) =
      observed_core(observed_calls.replay_call_authority entries(fst(execute_observed_environment input s)))"
      by (simp only: Authority_Input observed_calls.replay_call_authority.simps)
    also have "\<dots> = run_finality
      (observed_source_operations entries(fst(execute_observed_environment input s)))
      (observed_core(fst(execute_observed_environment input s)))"
      by (rule Cons.IH)
    also have "\<dots> = run_finality(observed_source_operations(entry#entries)s)(observed_core s)"
      by (simp only: Authority_Input observed_source_operations.simps finality_run_append
          observed_environment_projects_its_actual_operation)
    finally show ?thesis .
  qed
qed

theorem generated_observed_calls_have_actual_finality_core:
  fixes actions :: "(observed_command,observed_environment) client_call_action list"
    and initial :: observed_finality
  defines "m \<equiv> observed_calls.run_calls actions(initial_call_machine initial)"
  shows "observed_core(call_authority_state m) =
    run_finality(observed_source_operations(call_authority_log m)initial)(observed_core initial)"
proof -
  have contract: "observed_calls.authority_replay_contract m"
    using observed_calls.generated_call_contracts[of actions initial] by (simp add: m_def)
  have genesis: "call_genesis m=initial"
    by (simp add: m_def initial_call_machine_def)
  have actual: "call_authority_state m=
    observed_calls.replay_call_authority(call_authority_log m)initial"
    using contract unfolding observed_calls.authority_replay_contract_def by (simp add: genesis)
  show ?thesis by (simp only: actual observed_replay_projects_to_actual_finality_run)
qed

section \<open>Supplying Parent and Regulatory Contracts at Every Source Cut\<close>

lemma finality_word_preserves_cdsp:
  assumes "valid_state(receiver_snapshot(core_regulatory s))"
  shows "valid_state(receiver_snapshot(core_regulatory(run_finality operations s)))"
  using assms by (induction operations arbitrary:s)
    (auto intro: actual_finality_step_preserves_cdsp)

theorem observed_replay_supplies_parent_contract:
  assumes "reservation_contract balances(core_parent(observed_core initial))"
  shows "reservation_contract balances(core_parent(observed_core
    (observed_calls.replay_call_authority entries initial)))"
  by (simp only: observed_replay_projects_to_actual_finality_run)
     (rule finite_finality_preserves_parent_contract[OF assms])

theorem observed_replay_preserves_cdsp:
  assumes "valid_state(receiver_snapshot(core_regulatory(observed_core initial)))"
  shows "valid_state(receiver_snapshot(core_regulatory(observed_core
    (observed_calls.replay_call_authority entries initial))))"
  by (simp only: observed_replay_projects_to_actual_finality_run)
     (rule finality_word_preserves_cdsp[OF assms])

theorem every_observed_source_prefix_supplies_product_premises:
  assumes parent: "reservation_contract balances(core_parent(observed_core initial))"
    and regulatory: "valid_state(receiver_snapshot(core_regulatory(observed_core initial)))"
  shows "reservation_contract balances(core_parent(observed_core
      (observed_calls.replay_call_authority(take index entries)initial))) \<and>
    valid_state(receiver_snapshot(core_regulatory(observed_core
      (observed_calls.replay_call_authority(take index entries)initial))))"
  by (intro conjI)
     (rule observed_replay_supplies_parent_contract[OF parent],
      rule observed_replay_preserves_cdsp[OF regulatory])

theorem generated_observed_calls_supply_parent_and_cdsp:
  fixes actions :: "(observed_command,observed_environment) client_call_action list"
    and initial :: observed_finality
  assumes parent: "reservation_contract balances(core_parent(observed_core initial))"
    and regulatory: "valid_state(receiver_snapshot(core_regulatory(observed_core initial)))"
  defines "m \<equiv> observed_calls.run_calls actions(initial_call_machine initial)"
  shows "reservation_contract balances(core_parent(observed_core(call_authority_state m))) \<and>
    valid_state(receiver_snapshot(core_regulatory(observed_core(call_authority_state m))))"
proof -
  have actual: "observed_core(call_authority_state m) =
    run_finality(observed_source_operations(call_authority_log m)initial)(observed_core initial)"
    unfolding m_def by (rule generated_observed_calls_have_actual_finality_core)
  show ?thesis unfolding actual
    by (intro conjI)
       (rule finite_finality_preserves_parent_contract[OF parent],
        rule finality_word_preserves_cdsp[OF regulatory])
qed

theorem actual_initial_observed_calls_supply_product_premises:
  fixes actions :: "(observed_command,observed_environment) client_call_action list"
    and balances :: "source_account \<Rightarrow> nat" and regulatory :: global_state
    and contexts :: "nat \<Rightarrow> lock_context"
    and initial :: observed_finality
  assumes regulatory: "valid_state regulatory"
  defines "initial \<equiv> initial_observed_finality(initial_finality_core balances regulatory contexts)"
    and "m \<equiv> observed_calls.run_calls actions(initial_call_machine initial)"
  shows "reservation_contract balances(core_parent(observed_core(call_authority_state m))) \<and>
    valid_state(receiver_snapshot(core_regulatory(observed_core(call_authority_state m))))"
  unfolding m_def
  by (rule generated_observed_calls_supply_parent_and_cdsp)
     (simp_all add: initial_def initial_observed_finality_def initial_finality_core_def
        initial_reservation_contract regulatory)

section \<open>Independent Product Words for Observed Executions\<close>

lemma regulatory_word_append:
  "run_regulatory_word(first@second)state =
    (case run_regulatory_word first state of None \<Rightarrow> None
      | Some intermediate \<Rightarrow> run_regulatory_word second intermediate)"
proof (induction first arbitrary:state)
  case Nil
  then show ?case by simp
next
  case (Cons entry entries)
  obtain domain action asset where shape: "entry=(domain,action,asset)"
    by (cases entry) auto
  show ?case by (simp add: shape Cons.IH split: option.splits)
qed

fun finality_regulatory_word :: "finality_operation list \<Rightarrow> finality_core \<Rightarrow> regulatory_word" where
  "finality_regulatory_word [] s=[]"
| "finality_regulatory_word(operation#rest)s=
    emitted_regulatory_word operation s@finality_regulatory_word rest(finality_step operation s)"

theorem finality_run_refines_regulatory_word:
  "run_regulatory_word(finality_regulatory_word operations s)(receiver_snapshot(core_regulatory s)) =
    Some(receiver_snapshot(core_regulatory(run_finality operations s)))"
proof (induction operations arbitrary:s)
  case Nil
  then show ?case by simp
next
  case (Cons operation operations)
  have step: "run_regulatory_word(emitted_regulatory_word operation s)(receiver_snapshot(core_regulatory s)) =
    Some(receiver_snapshot(core_regulatory(finality_step operation s)))"
    by (rule actual_finality_step_refines_regulatory_word)
  have tail: "run_regulatory_word(finality_regulatory_word operations(finality_step operation s))
      (receiver_snapshot(core_regulatory(finality_step operation s))) =
    Some(receiver_snapshot(core_regulatory(run_finality operations(finality_step operation s))))"
    by (rule Cons.IH)
  show ?case by (simp add: regulatory_word_append step tail)
qed

theorem observed_replay_refines_both_product_words:
  fixes entries :: "(observed_command,observed_reply,observed_environment) authority_call_entry list"
  assumes parent: "reservation_contract balances(core_parent(observed_core initial))"
  defines "operations \<equiv> observed_source_operations entries initial"
  shows "fst(finality_alpha(observed_core(observed_calls.replay_call_authority entries initial))) =
      run_transfer_ledger(finality_transfer_word operations(observed_core initial))
        (fst(finality_alpha(observed_core initial))) \<and>
    run_regulatory_word(finality_regulatory_word operations(observed_core initial))
        (snd(finality_alpha(observed_core initial))) =
      Some(snd(finality_alpha(observed_core(observed_calls.replay_call_authority entries initial))))"
proof -
  have actual: "observed_core(observed_calls.replay_call_authority entries initial)=
    run_finality operations(observed_core initial)"
    unfolding operations_def by (rule observed_replay_projects_to_actual_finality_run)
  have transfer: "transfer_projection(core_parent(run_finality operations(observed_core initial))) =
    run_transfer_ledger(finality_transfer_word operations(observed_core initial))
      (transfer_projection(core_parent(observed_core initial)))"
    by (rule finite_actual_child_execution_refines_transfer_word[OF parent])
  have regulation: "run_regulatory_word(finality_regulatory_word operations(observed_core initial))
      (receiver_snapshot(core_regulatory(observed_core initial))) =
    Some(receiver_snapshot(core_regulatory(run_finality operations(observed_core initial))))"
    by (rule finality_run_refines_regulatory_word)
  show ?thesis using transfer regulation by (simp only: actual finality_alpha_def fst_conv snd_conv)
qed

theorem generated_observed_calls_refine_both_product_words:
  fixes actions :: "(observed_command,observed_environment) client_call_action list"
    and initial :: observed_finality
    and m :: "(observed_finality,observed_command,observed_reply,observed_environment) durable_call_machine"
  assumes parent: "reservation_contract balances(core_parent(observed_core initial))"
  defines "m \<equiv> observed_calls.run_calls actions(initial_call_machine initial)"
    and "operations \<equiv> observed_source_operations(call_authority_log m)initial"
  shows "fst(finality_alpha(observed_core(call_authority_state m))) =
      run_transfer_ledger(finality_transfer_word operations(observed_core initial))
        (fst(finality_alpha(observed_core initial))) \<and>
    run_regulatory_word(finality_regulatory_word operations(observed_core initial))
        (snd(finality_alpha(observed_core initial))) =
      Some(snd(finality_alpha(observed_core(call_authority_state m))))"
proof -
  have replay: "observed_calls.authority_replay_contract m"
    using observed_calls.generated_call_contracts[of actions initial] by (simp add: m_def)
  have genesis: "call_genesis m=initial" by (simp add: m_def initial_call_machine_def)
  have source: "call_authority_state m=observed_calls.replay_call_authority(call_authority_log m)initial"
    using replay by (simp add: observed_calls.authority_replay_contract_def genesis)
  show ?thesis unfolding source operations_def
    by (rule observed_replay_refines_both_product_words[OF parent])
qed

section \<open>Product Premises at the Actual Source of Every Completed Reply\<close>

theorem every_generated_observed_completion_has_an_actual_product_source:
  fixes actions :: "(observed_command,observed_environment) client_call_action list"
    and initial :: observed_finality
  assumes parent: "reservation_contract balances(core_parent(observed_core initial))"
    and regulatory: "valid_state(receiver_snapshot(core_regulatory(observed_core initial)))"
  defines "m \<equiv> observed_calls.run_calls actions(initial_call_machine initial)"
  assumes completed: "call_completions m call_id=Some reply"
  shows "\<exists>command index.
    call_authority_results m call_id=Some(command,reply,index) \<and>
    reply=snd(execute_observed command
      (observed_calls.replay_call_authority(take index(call_authority_log m))initial)) \<and>
    reservation_contract balances(core_parent(observed_core
      (observed_calls.replay_call_authority(take index(call_authority_log m))initial))) \<and>
    valid_state(receiver_snapshot(core_regulatory(observed_core
      (observed_calls.replay_call_authority(take index(call_authority_log m))initial))))"
proof -
  have life: "call_lifecycle_contract m"
    unfolding m_def by (rule observed_calls.generated_call_lifecycle_contract)
  obtain command index where found: "call_authority_results m call_id=Some(command,reply,index)"
    using completed_result_has_source[OF life completed] by blast
  have cache: "authority_cache_contract m"
    and replay: "observed_calls.authority_replay_contract m"
    using observed_calls.generated_call_contracts[of actions initial] by (simp_all add: m_def)
  have genesis: "call_genesis m=initial" by (simp add: m_def initial_call_machine_def)
  have actual: "reply=snd(execute_observed command
    (observed_calls.replay_call_authority(take index(call_authority_log m))initial))"
    using observed_calls.cached_result_is_the_actual_indexed_reply[OF cache replay found]
    by (simp only: genesis)
  have source_premises: "reservation_contract balances(core_parent(observed_core
      (observed_calls.replay_call_authority(take index(call_authority_log m))initial))) \<and>
    valid_state(receiver_snapshot(core_regulatory(observed_core
      (observed_calls.replay_call_authority(take index(call_authority_log m))initial))))"
    by (rule every_observed_source_prefix_supplies_product_premises[OF parent regulatory])
  show ?thesis using found actual source_premises by blast
qed

text \<open>All observed commands and environmental inputs remain available,
  including malformed requests, stale caches, raw and historical queries,
  completed Busy replies, disconnections, retries and local response loss.
  The durable source log is interpreted by its actual callbacks. Recorded
  reply values are not used to invent the operation word; the generated
  replay and cache contracts separately establish their authenticity.
  Each completed reply has an actual indexed execution whose source supplies
  the financial and regulatory premises. Its application or protocol payload
  still needs the corresponding independent observation interpretation;
  this file does not identify those additional payloads with token quantities.\<close>

end

end
