(* SPDX-License-Identifier: BSD-3-Clause *)
theory Regulatory_Composition_Example
  imports Source_Call_Realization "Evidence_Atomic_Binding.Regulatory_Finality_Scenarios"
begin

abbreviation regulatory_checked_current_replay where
  "regulatory_checked_current_replay \<equiv> durable_call_protocol.checked_current_replay
    regulation_case.execute_observed regulation_case.execute_observed_environment"

abbreviation regulatory_restore_current_replica where
  "regulatory_restore_current_replica \<equiv> durable_call_protocol.restore_current_replica
    regulation_case.execute_observed regulation_case.execute_observed_environment"

abbreviation regulatory_dispatch_from_recovered_replica where
  "regulatory_dispatch_from_recovered_replica \<equiv> durable_call_protocol.dispatch_from_recovered_replica
    regulation_case.execute_observed"

context source_attestation
begin

lemma observed_completion_survives_every_step:
  assumes "call_completions machine call_id=Some reply"
  shows "call_completions(observed_calls.call_step action machine)call_id=Some reply"
  using assms by (cases action)
    (auto simp: observed_calls.call_definitions Let_def split: option.splits prod.splits if_splits)

theorem observed_completed_replies_survive_finite_continuations:
  assumes "call_completions machine call_id=Some reply"
  shows "call_completions(observed_calls.run_calls actions machine)call_id=Some reply"
  using assms by (induction actions arbitrary:machine)
    (auto intro: observed_completion_survives_every_step)

end

section \<open>Existing Generated Regulatory States Supply the Concrete Inputs\<close>

lemma enforcement_state_is_an_actual_child_prefix:
  "regulation_enforced=regulation_case.run_finality
    (regulation_credit_trace@[
      Record_Terminal (example_certificate 20),Invoke_Regulatory 2 8 0 (example_request 20),
      Publish_Primary (0,20),Invoke_Protocol 2 10 0 regulation_ordinary_intent,
      Invoke_Protocol 2 11 0 regulation_enforcement_intent]) regulation_genesis"
  by (simp add: regulation_enforced_def regulation_denied_def regulation_published_def
      regulation_frozen_def regulation_recorded_def regulation_root_ready_def
      regulation_case.finality_run_append)

theorem ordinary_use_succeeds_before_the_existing_freeze:
  "snd (regulation_case.invoke_protocol 2 7 0 regulation_ordinary_intent regulation_root_ready)=
    Protocol_Response Descendant_Executed"
  by (simp add: regulation_case.invoke_protocol_def regulation_root_ready_core_fields
      regulation_root_ready_financial_state regulation_root_record_def record_reference_def
      lift_protocol_result_def regulation_spend_definitions regulation_payload_definitions
      example_snapshot_def Let_def)

theorem equal_funding_does_not_supply_the_current_active_policy:
  "funded_units (machine_state (core_parent regulation_published))=
      funded_units (machine_state (core_parent regulation_root_ready)) \<and>
    destination_units (machine_state (core_parent regulation_published))=
      destination_units (machine_state (core_parent regulation_root_ready)) \<and>
    snd (regulation_case.invoke_protocol 2 7 0 regulation_ordinary_intent regulation_root_ready)=
      Protocol_Response Descendant_Executed \<and>
    snd (regulation_case.invoke_protocol 2 10 0 regulation_ordinary_intent regulation_published)=
      Protocol_Response Request_Rejected"
proof -
  have funding: "funded_units (machine_state (core_parent regulation_published))=
      funded_units (machine_state (core_parent regulation_root_ready))"
    and pooled: "destination_units (machine_state (core_parent regulation_published))=
      destination_units (machine_state (core_parent regulation_root_ready))"
    by (simp_all add: regulation_published_shape regulation_frozen_shape regulation_recorded_shape)
  show ?thesis by (intro conjI, rule funding, rule pooled,
    rule ordinary_use_succeeds_before_the_existing_freeze,
    rule ordinary_descendant_is_rejected_after_actual_freeze)
qed

section \<open>Actual Refresh and Current Dispatch Consume Those States\<close>

definition regulatory_refreshed :: "observed_finality \<Rightarrow> observed_finality" where
  "regulatory_refreshed state=fst (regulation_case.execute_observed (Refresh_Endpoint 2) state)"

lemma regulatory_refresh_uses_the_existing_client:
  "snd (regulation_case.execute_observed (Execute_Current 2 command) (regulatory_refreshed state))=
    Effect_Reply (snd (regulation_case.execute_finality_client command (observed_core state)))"
  by (simp add: regulatory_refreshed_def current_cache_valid_def store_core_result_def Let_def)

theorem current_freeze_observation_is_the_actual_receiver_success:
  assumes core: "observed_core state=regulation_recorded"
  shows "snd (regulation_case.execute_observed
    (Execute_Current 2 (Client_Regulatory 2 0 (example_request 20))) (regulatory_refreshed state))=
      Effect_Reply Regulatory_Applied"
proof -
  have epoch: "core_epoch regulation_recorded=8" by (simp add: regulation_recorded_shape)
  show ?thesis by (simp only: regulatory_refresh_uses_the_existing_client core
      regulation_case.execute_finality_client_def client_operation.simps snd_conv
      regulation_case.core_result.simps epoch actual_child_freeze_succeeds)
qed

theorem current_ordinary_observation_really_rejects_the_frozen_policy:
  assumes core: "observed_core state=regulation_published"
  shows "snd (regulation_case.execute_observed
    (Execute_Current 2 (Client_Protocol 2 0 regulation_ordinary_intent)) (regulatory_refreshed state))=
      Effect_Reply (Protocol_Response Request_Rejected)"
proof -
  have epoch: "core_epoch regulation_published=10" by (simp add: regulation_published_shape)
  show ?thesis
    by (simp only: regulatory_refresh_uses_the_existing_client core
      regulation_case.execute_finality_client_def client_operation.simps snd_conv
      regulation_case.core_result.simps epoch ordinary_descendant_is_rejected_after_actual_freeze)
qed

theorem current_enforcement_observation_really_uses_the_legal_recovery_path:
  assumes core: "observed_core state=regulation_denied"
  shows "snd (regulation_case.execute_observed
    (Execute_Current 2 (Client_Protocol 2 0 regulation_enforcement_intent)) (regulatory_refreshed state))=
      Effect_Reply (Protocol_Response Descendant_Executed)"
proof -
  have epoch: "core_epoch regulation_denied=11" using regulation_denied_state by blast
  show ?thesis
    by (simp only: regulatory_refresh_uses_the_existing_client core
      regulation_case.execute_finality_client_def client_operation.simps snd_conv
      regulation_case.core_result.simps epoch authorized_enforcement_descendant_succeeds_after_actual_freeze)
qed

section \<open>A Nontrivial Historical Projection of Actual Enforcement\<close>

theorem generated_enforcement_snapshot_has_a_nontrivial_projection:
  "normalize_historical_snapshot (capture_snapshot regulation_enforced)\<noteq>capture_snapshot regulation_enforced"
proof (rule notI)
  assume same: "normalize_historical_snapshot (capture_snapshot regulation_enforced)=capture_snapshot regulation_enforced"
  have original: "length (lawful_descendants (snapshot_financial (capture_snapshot regulation_enforced)))=1"
    using enforcement_changes_only_lawful_funding_and_keeps_freeze by (simp add: capture_snapshot_def)
  have normalized: "length (lawful_descendants (snapshot_financial
      (normalize_historical_snapshot (capture_snapshot regulation_enforced))))=0"
    by (simp add: normalize_historical_snapshot_def)
  have zero: "length (lawful_descendants (snapshot_financial (capture_snapshot regulation_enforced)))=0"
    using normalized by (simp only: same)
  show False using zero original by simp
qed

theorem generated_regulatory_history_keeps_every_query_and_readiness_decision:
  "stored_query query (normalize_historical_snapshot (capture_snapshot regulation_enforced))=
      stored_query query (capture_snapshot regulation_enforced) \<and>
    snapshot_query_ready query (normalize_historical_snapshot (capture_snapshot regulation_enforced))=
      snapshot_query_ready query (capture_snapshot regulation_enforced) \<and>
    snapshot_regulatory (normalize_historical_snapshot (capture_snapshot regulation_enforced))=
      receiver_snapshot (core_regulatory regulation_published)"
proof -
  have queries: "stored_query query (normalize_historical_snapshot (capture_snapshot regulation_enforced))=
      stored_query query (capture_snapshot regulation_enforced)"
    by (rule normalized_snapshot_stored_query)
  have ready: "snapshot_query_ready query (normalize_historical_snapshot (capture_snapshot regulation_enforced))=
      snapshot_query_ready query (capture_snapshot regulation_enforced)"
    by (rule normalized_snapshot_query_ready)
  have current: "core_regulatory regulation_enforced=core_regulatory regulation_published"
    using enforcement_changes_only_lawful_funding_and_keeps_freeze by blast
  have regulatory: "snapshot_regulatory (normalize_historical_snapshot (capture_snapshot regulation_enforced))=
      receiver_snapshot (core_regulatory regulation_published)"
    by (simp add: normalize_historical_snapshot_def capture_snapshot_def current)
  show ?thesis by (rule conjI[OF queries], rule conjI[OF ready regulatory])
qed

theorem historical_projection_preserves_the_actual_frozen_rejection:
  assumes "observed_core state=regulation_published"
  shows "snd (regulation_case.execute_observed
    (Execute_Current 2 (Client_Protocol 2 0 regulation_ordinary_intent))
    (normalize_observed_history (regulatory_refreshed state)))=
      Effect_Reply (Protocol_Response Request_Rejected)"
  by (simp only: regulation_case.observed_callback_reply_preserved
      current_ordinary_observation_really_rejects_the_frozen_policy[OF assms])

theorem historical_projection_preserves_the_actual_enforcement_success:
  assumes "observed_core state=regulation_denied"
  shows "snd (regulation_case.execute_observed
    (Execute_Current 2 (Client_Protocol 2 0 regulation_enforcement_intent))
    (normalize_observed_history (regulatory_refreshed state)))=
      Effect_Reply (Protocol_Response Descendant_Executed)"
  by (simp only: regulation_case.observed_callback_reply_preserved
      current_enforcement_observation_really_uses_the_legal_recovery_path[OF assms])

section \<open>Continuation from the Existing Generated Call Machine\<close>

theorem generated_regulatory_cut_transports_future_calls:
  assumes generated: "recovery_source runtime=regulation_case.observed_calls.run_calls prefix
      (initial_call_machine (initial_observed_finality regulation_genesis))"
    and connected: "recovery_connected runtime"
    and cut: "observed_core (call_authority_state (recovery_source runtime))=regulation_denied"
  shows "regulatory_checked_current_replay (recovery_source runtime)
      (current_source_candidate (recovery_source runtime))=Some (call_authority_state (recovery_source runtime)) \<and>
    snd (regulation_case.execute_observed
      (Execute_Current 2 (Client_Protocol 2 0 regulation_enforcement_intent))
      (regulatory_refreshed (call_authority_state (recovery_source runtime))))=
        Effect_Reply (Protocol_Response Descendant_Executed) \<and>
    call_completions (regulation_case.observed_history_projection.reduced.run_calls actions
      (regulation_case.observed_history_projection.normalize_call_machine
        (recovery_source (regulatory_dispatch_from_recovered_replica call_id (Refresh_Endpoint 2)
          (regulatory_restore_current_replica
            (current_source_candidate (recovery_source runtime)) runtime)))))=
      call_completions (regulation_case.observed_calls.run_calls actions
        (regulation_case.observed_calls.dispatch_client_call call_id (Refresh_Endpoint 2) (recovery_source runtime)))"
proof -
  have contract: "regulation_case.observed_calls.authority_replay_contract (recovery_source runtime)"
    using regulation_case.observed_calls.generated_call_contracts
      [of prefix "initial_observed_finality regulation_genesis"]
    by (simp only: generated; blast)
  have recovered: "regulatory_checked_current_replay (recovery_source runtime)
      (current_source_candidate (recovery_source runtime))=Some (call_authority_state (recovery_source runtime))"
    by (rule durable_call_protocol.actual_source_produces_a_valid_complete_candidate[OF contract])
  have enforcement: "snd (regulation_case.execute_observed
      (Execute_Current 2 (Client_Protocol 2 0 regulation_enforcement_intent))
      (regulatory_refreshed (call_authority_state (recovery_source runtime))))=
        Effect_Reply (Protocol_Response Descendant_Executed)"
    by (rule current_enforcement_observation_really_uses_the_legal_recovery_path[OF cut])
  have decisions: "call_completions (regulation_case.observed_history_projection.reduced.run_calls actions
      (regulation_case.observed_history_projection.normalize_call_machine
        (recovery_source (regulatory_dispatch_from_recovered_replica call_id (Refresh_Endpoint 2)
          (regulatory_restore_current_replica
            (current_source_candidate (recovery_source runtime)) runtime)))))=
      call_completions (regulation_case.observed_calls.run_calls actions
        (regulation_case.observed_calls.dispatch_client_call call_id (Refresh_Endpoint 2) (recovery_source runtime)))"
    by (rule regulation_case.observed_history_projection.restored_runtime_preserves_all_future_completed_replies(1)
      [OF contract connected recovered])
  show ?thesis by (rule conjI[OF recovered], rule conjI[OF enforcement decisions])
qed

section \<open>A Fresh Completed Observed Call for Every Existing Client Command\<close>

type_synonym regulatory_observed_machine =
  "(observed_finality,observed_command,observed_reply,observed_environment) durable_call_machine"

definition observed_client_program :: "nat \<Rightarrow> nat \<Rightarrow> client_command \<Rightarrow>
  (observed_command,observed_environment) client_call_action list" where
  "observed_client_program namespace next command=
    complete_call_program (namespace,next) (Refresh_Endpoint 0) @
    complete_call_program (namespace,Suc next) (Execute_Current 0 command)"

fun observed_client_word :: "nat \<Rightarrow> nat \<Rightarrow> client_command list \<Rightarrow>
  (observed_command,observed_environment) client_call_action list" where
  "observed_client_word namespace next []=[]"
| "observed_client_word namespace next (command#commands)=
    observed_client_program namespace next command @ observed_client_word namespace (next+2) commands"

lemma observed_client_word_append:
  "observed_client_word namespace next (first@second)=observed_client_word namespace next first @
    observed_client_word namespace (next+2*length first) second"
  by (induction first arbitrary:"next") (simp_all add: algebra_simps)

fun client_operation_at_epoch :: "nat \<Rightarrow> client_command \<Rightarrow> finality_operation" where
  "client_operation_at_epoch epoch (Client_Terminal cert)=Record_Terminal cert"
| "client_operation_at_epoch epoch (Client_Protocol endpoint index intent)=Invoke_Protocol endpoint epoch index intent"
| "client_operation_at_epoch epoch (Client_Regulatory endpoint index request)=Invoke_Regulatory endpoint epoch index request"
| "client_operation_at_epoch epoch (Client_Publication key)=Publish_Primary key"

lemma client_operation_at_current_epoch:
  "client_operation_at_epoch (core_epoch state) command=client_operation state command"
  by (cases command) simp_all

fun observed_client_operation_word :: "nat \<Rightarrow> client_command list \<Rightarrow> finality_operation list" where
  "observed_client_operation_word epoch []=[]"
| "observed_client_operation_word epoch (command#commands)=
    client_operation_at_epoch epoch command # observed_client_operation_word (Suc epoch) commands"

context source_attestation
begin

fun observed_client_core_run :: "client_command list \<Rightarrow> finality_core \<Rightarrow> finality_core" where
  "observed_client_core_run [] state=state"
| "observed_client_core_run (command#commands) state=
    observed_client_core_run commands (fst (execute_finality_client command state))"

lemma observed_client_core_run_append:
  "observed_client_core_run (first@second) state=
    observed_client_core_run second (observed_client_core_run first state)"
  by (induction first arbitrary:state) simp_all

lemma observed_client_core_run_is_actual_finality:
  "observed_client_core_run commands state=
    run_finality (observed_client_operation_word (core_epoch state) commands) state"
  by (induction commands arbitrary:state)
    (simp_all add: execute_finality_client_def client_operation_at_current_epoch)

theorem observed_client_program_completes_its_actual_callback:
  fixes machine :: regulatory_observed_machine
  assumes ready: "source_call_ready namespace next machine"
  shows "source_call_ready namespace (next+2)
      (observed_calls.run_calls (observed_client_program namespace next command) machine)"
    "observed_core (call_authority_state
      (observed_calls.run_calls (observed_client_program namespace next command) machine))=
      fst (execute_finality_client command (observed_core (call_authority_state machine)))"
    "call_completions (observed_calls.run_calls (observed_client_program namespace next command) machine)
      (namespace,Suc next)=Some (Effect_Reply
        (snd (execute_finality_client command (observed_core (call_authority_state machine)))))"
    "historical_snapshots (call_authority_state
      (observed_calls.run_calls (observed_client_program namespace next command) machine))
      (core_epoch (fst (execute_finality_client command (observed_core (call_authority_state machine)))))=
      Some (capture_snapshot (fst (execute_finality_client command (observed_core (call_authority_state machine)))))"
proof -
  let ?refreshed = "observed_calls.run_calls (complete_call_program (namespace,next) (Refresh_Endpoint 0)) machine"
  let ?finished = "observed_calls.run_calls (complete_call_program (namespace,Suc next) (Execute_Current 0 command)) ?refreshed"
  have refreshed_ready: "source_call_ready namespace (Suc next) ?refreshed"
    by (rule observed_calls.fresh_program_advances_the_identifier_supply[OF ready])
  have refreshed_state: "call_authority_state ?refreshed=
      fst (execute_observed (Refresh_Endpoint 0) (call_authority_state machine))"
    by (rule observed_calls.fresh_program_uses_the_actual_callback(2)[OF ready])
  have current: "current_cache_valid (call_authority_state ?refreshed) 0"
    by (simp add: refreshed_state current_cache_valid_def)
  have core: "observed_core (call_authority_state ?refreshed)=observed_core (call_authority_state machine)"
    by (simp add: refreshed_state)
  note completed = observed_calls.fresh_program_uses_the_actual_callback[OF refreshed_ready,
    where command="Execute_Current 0 command"]
  have shape: "observed_calls.run_calls (observed_client_program namespace next command) machine=?finished"
    by (simp only: observed_client_program_def observed_calls.run_calls_append)
  have advanced: "source_call_ready namespace (Suc (Suc next)) ?finished"
    by (rule observed_calls.fresh_program_advances_the_identifier_supply[OF refreshed_ready])
  show "source_call_ready namespace (next+2)
      (observed_calls.run_calls (observed_client_program namespace next command) machine)"
    using advanced by (simp add: shape numeral_2_eq_2)
  show "observed_core (call_authority_state
      (observed_calls.run_calls (observed_client_program namespace next command) machine))=
      fst (execute_finality_client command (observed_core (call_authority_state machine)))"
    by (simp only: shape completed(2) execute_observed.simps current if_True;
      simp add: store_core_result_def core Let_def)
  show "call_completions (observed_calls.run_calls (observed_client_program namespace next command) machine)
      (namespace,Suc next)=Some (Effect_Reply
        (snd (execute_finality_client command (observed_core (call_authority_state machine)))))"
    by (simp only: shape completed(1) execute_observed.simps current if_True;
      simp add: store_core_result_def core Let_def)
  show "historical_snapshots (call_authority_state
      (observed_calls.run_calls (observed_client_program namespace next command) machine))
      (core_epoch (fst (execute_finality_client command (observed_core (call_authority_state machine)))))=
      Some (capture_snapshot (fst (execute_finality_client command (observed_core (call_authority_state machine)))))"
    by (simp only: shape completed(2) execute_observed.simps current if_True;
      simp add: store_core_result_def core Let_def)
qed

theorem observed_client_word_has_the_exact_actual_core:
  fixes machine :: regulatory_observed_machine
  assumes ready: "source_call_ready namespace next machine"
  shows "source_call_ready namespace (next+2*length commands)
      (observed_calls.run_calls (observed_client_word namespace next commands) machine) \<and>
    observed_core (call_authority_state (observed_calls.run_calls (observed_client_word namespace next commands) machine))=
      observed_client_core_run commands (observed_core (call_authority_state machine))"
  using ready
proof (induction commands arbitrary:"next" machine)
  case Nil
  then show ?case by simp
next
  case (Cons command commands)
  let ?step = "observed_calls.run_calls (observed_client_program namespace next command) machine"
  note first = observed_client_program_completes_its_actual_callback[OF Cons.prems, where command=command]
  note tail = Cons.IH[OF first(1)]
  show ?case using tail first(2)
    by (simp add: observed_calls.run_calls_append algebra_simps)
qed

end

section \<open>The Original Regulatory Prefix Is Now an Actual Durable Call Word\<close>

definition regulatory_preparation_clients :: "client_command list" where
  "regulatory_preparation_clients=[
    Client_Protocol 0 0 (Reserve_Intent regulation_money_request [] 10),
    Client_Protocol 0 0 (Dispatch_Intent regulation_money_request 0 []),
    Client_Protocol 0 0 (Source_Intent regulation_money_request 0 []),
    Client_Terminal regulation_money_certificate,
    Client_Protocol 0 0 (Certificate_Intent regulation_money_certificate),
    Client_Protocol 2 0 (Deliver_Intent Bypass_Route regulation_money_request),
    Client_Publication (0,17),Client_Terminal (example_certificate 20),
    Client_Regulatory 2 0 (example_request 20),Client_Publication (0,20)]"

definition regulatory_calls_initial :: regulatory_observed_machine where
  "regulatory_calls_initial=initial_call_machine (initial_observed_finality regulation_genesis)"

definition regulatory_prepared_calls :: regulatory_observed_machine where
  "regulatory_prepared_calls=regulation_case.observed_calls.run_calls
    (observed_client_word 92 0 regulatory_preparation_clients) regulatory_calls_initial"

definition regulatory_denied_calls :: regulatory_observed_machine where
  "regulatory_denied_calls=regulation_case.observed_calls.run_calls
    (observed_client_program 92 20 (Client_Protocol 2 0 regulation_ordinary_intent)) regulatory_prepared_calls"

definition regulatory_enforced_calls :: regulatory_observed_machine where
  "regulatory_enforced_calls=regulation_case.observed_calls.run_calls
    (observed_client_program 92 22 (Client_Protocol 2 0 regulation_enforcement_intent)) regulatory_denied_calls"

lemma regulatory_preparation_is_the_original_operation_word:
  "observed_client_operation_word 0 regulatory_preparation_clients=regulation_credit_trace@[
    Record_Terminal (example_certificate 20),Invoke_Regulatory 2 8 0 (example_request 20),Publish_Primary (0,20)]"
  by (simp add: regulatory_preparation_clients_def regulation_credit_trace_def)

lemma regulatory_preparation_core_is_the_existing_published_state:
  "regulation_case.observed_client_core_run regulatory_preparation_clients regulation_genesis=regulation_published"
proof -
  have epoch: "core_epoch regulation_genesis=0" by (simp add: regulation_genesis_def initial_finality_core_def)
  have existing: "regulation_published=regulation_case.run_finality
    (regulation_credit_trace@[Record_Terminal (example_certificate 20),
      Invoke_Regulatory 2 8 0 (example_request 20),Publish_Primary (0,20)]) regulation_genesis"
    by (simp add: regulation_published_def regulation_frozen_def regulation_recorded_def
      regulation_root_ready_def regulation_case.finality_run_append)
  show ?thesis by (simp only: regulation_case.observed_client_core_run_is_actual_finality epoch
    regulatory_preparation_is_the_original_operation_word existing[symmetric])
qed

lemma regulatory_prepared_calls_are_fresh_and_exact:
  "source_call_ready 92 20 regulatory_prepared_calls \<and>
    observed_core (call_authority_state regulatory_prepared_calls)=regulation_published"
proof -
  have ready: "source_call_ready 92 0 regulatory_calls_initial"
    by (simp add: regulatory_calls_initial_def)
  note generated = regulation_case.observed_client_word_has_the_exact_actual_core
    [OF ready, where commands=regulatory_preparation_clients]
  have count: "length regulatory_preparation_clients=10"
    by (simp add: regulatory_preparation_clients_def)
  have initial_core: "observed_core (call_authority_state regulatory_calls_initial)=regulation_genesis"
    by (simp add: regulatory_calls_initial_def initial_call_machine_def initial_observed_finality_def)
  show ?thesis using generated
    by (simp only: regulatory_prepared_calls_def count initial_core
      regulatory_preparation_core_is_the_existing_published_state; simp)
qed

lemma regulatory_actual_client_steps:
  "fst (regulation_case.execute_finality_client (Client_Protocol 2 0 regulation_ordinary_intent)
    regulation_published)=regulation_denied"
  "fst (regulation_case.execute_finality_client (Client_Protocol 2 0 regulation_enforcement_intent)
    regulation_denied)=regulation_enforced"
  "snd (regulation_case.execute_finality_client (Client_Protocol 2 0 regulation_ordinary_intent)
    regulation_published)=Protocol_Response Request_Rejected"
  "snd (regulation_case.execute_finality_client (Client_Protocol 2 0 regulation_enforcement_intent)
    regulation_denied)=Protocol_Response Descendant_Executed"
proof -
  have published_epoch: "core_epoch regulation_published=10" by (simp add: regulation_published_shape)
  have denied_epoch: "core_epoch regulation_denied=11" using regulation_denied_state by blast
  show "fst (regulation_case.execute_finality_client (Client_Protocol 2 0 regulation_ordinary_intent)
    regulation_published)=regulation_denied"
    by (simp only: regulation_case.execute_finality_client_def fst_conv client_operation.simps
      published_epoch regulation_denied_def)
  show "fst (regulation_case.execute_finality_client (Client_Protocol 2 0 regulation_enforcement_intent)
    regulation_denied)=regulation_enforced"
    by (simp only: regulation_case.execute_finality_client_def fst_conv client_operation.simps
      denied_epoch regulation_enforced_def)
  show "snd (regulation_case.execute_finality_client (Client_Protocol 2 0 regulation_ordinary_intent)
    regulation_published)=Protocol_Response Request_Rejected"
    by (simp only: regulation_case.execute_finality_client_def snd_conv client_operation.simps
      published_epoch regulation_case.core_result.simps ordinary_descendant_is_rejected_after_actual_freeze)
  show "snd (regulation_case.execute_finality_client (Client_Protocol 2 0 regulation_enforcement_intent)
    regulation_denied)=Protocol_Response Descendant_Executed"
    by (simp only: regulation_case.execute_finality_client_def snd_conv client_operation.simps
      denied_epoch regulation_case.core_result.simps authorized_enforcement_descendant_succeeds_after_actual_freeze)
qed

theorem actual_observed_calls_generate_the_previously_required_cut:
  "source_call_ready 92 22 regulatory_denied_calls \<and>
    observed_core (call_authority_state regulatory_denied_calls)=regulation_denied \<and>
    call_completions regulatory_denied_calls (92,21)=Some (Effect_Reply (Protocol_Response Request_Rejected))"
proof -
  have ready: "source_call_ready 92 20 regulatory_prepared_calls"
    and core: "observed_core (call_authority_state regulatory_prepared_calls)=regulation_published"
    using regulatory_prepared_calls_are_fresh_and_exact by blast+
  note actual = regulation_case.observed_client_program_completes_its_actual_callback
    [OF ready, where command="Client_Protocol 2 0 regulation_ordinary_intent"]
  show ?thesis using actual(1,2,3)
    by (simp only: regulatory_denied_calls_def core regulatory_actual_client_steps; simp)
qed

theorem the_same_call_machine_completes_actual_enforcement:
  "observed_core (call_authority_state regulatory_enforced_calls)=regulation_enforced \<and>
    call_completions regulatory_enforced_calls (92,23)=Some (Effect_Reply (Protocol_Response Descendant_Executed)) \<and>
    historical_snapshots (call_authority_state regulatory_enforced_calls) 12=Some (capture_snapshot regulation_enforced)"
proof -
  have ready: "source_call_ready 92 22 regulatory_denied_calls"
    and core: "observed_core (call_authority_state regulatory_denied_calls)=regulation_denied"
    using actual_observed_calls_generate_the_previously_required_cut by blast+
  have epoch: "core_epoch regulation_enforced=12"
    using enforcement_changes_only_lawful_funding_and_keeps_freeze by blast
  note actual = regulation_case.observed_client_program_completes_its_actual_callback
    [OF ready, where command="Client_Protocol 2 0 regulation_enforcement_intent"]
  show ?thesis using actual(2,3,4)
    by (simp only: regulatory_enforced_calls_def core regulatory_actual_client_steps epoch; simp)
qed

definition regulatory_completed_word :: "(observed_command,observed_environment) client_call_action list" where
  "regulatory_completed_word=observed_client_word 92 0 regulatory_preparation_clients @
    observed_client_program 92 20 (Client_Protocol 2 0 regulation_ordinary_intent) @
    observed_client_program 92 22 (Client_Protocol 2 0 regulation_enforcement_intent)"

lemma regulatory_completed_word_generates_the_same_machine:
  "regulatory_enforced_calls=regulation_case.observed_calls.run_calls regulatory_completed_word
    (initial_call_machine (initial_observed_finality regulation_genesis))"
  by (simp only: regulatory_enforced_calls_def regulatory_denied_calls_def regulatory_prepared_calls_def
    regulatory_completed_word_def regulatory_calls_initial_def durable_call_protocol.run_calls_append)

theorem actual_generated_regulatory_history_is_changed_by_projection:
  "normalize_observed_history (call_authority_state regulatory_enforced_calls)\<noteq>
    call_authority_state regulatory_enforced_calls"
proof (rule notI)
  assume same: "normalize_observed_history (call_authority_state regulatory_enforced_calls)=
      call_authority_state regulatory_enforced_calls"
  have stored: "historical_snapshots (call_authority_state regulatory_enforced_calls) 12=Some (capture_snapshot regulation_enforced)"
    using the_same_call_machine_completes_actual_enforcement by blast
  have equality: "Some (normalize_historical_snapshot (capture_snapshot regulation_enforced))=
      Some (capture_snapshot regulation_enforced)"
    using arg_cong[OF same, where f="\<lambda>state. historical_snapshots state 12"]
    by (simp add: normalize_observed_history_def normalize_snapshot_history_def stored)
  have snapshots: "normalize_historical_snapshot (capture_snapshot regulation_enforced)=capture_snapshot regulation_enforced"
    using equality by (simp only: option.inject)
  show False by (rule notE[OF generated_enforcement_snapshot_has_a_nontrivial_projection snapshots])
qed

definition regulatory_generated_recovery where
  "regulatory_generated_recovery=\<lparr>recovery_source=regulatory_enforced_calls,recovery_replica=None,recovery_connected=True\<rparr>"

theorem actual_regulatory_machine_recovers_and_transports_every_continuation:
  "call_completions (regulation_case.observed_history_projection.reduced.run_calls actions
    (regulation_case.observed_history_projection.normalize_call_machine
      (recovery_source (regulatory_dispatch_from_recovered_replica (92,23)
        (Execute_Current 0 (Client_Protocol 2 0 regulation_enforcement_intent))
        (regulatory_restore_current_replica
          (current_source_candidate regulatory_enforced_calls) regulatory_generated_recovery)))))=
    call_completions (regulation_case.observed_calls.run_calls actions
      (regulation_case.observed_calls.dispatch_client_call (92,23)
        (Execute_Current 0 (Client_Protocol 2 0 regulation_enforcement_intent)) regulatory_enforced_calls))"
proof -
  have contract: "regulation_case.observed_calls.authority_replay_contract regulatory_enforced_calls"
    using regulation_case.observed_calls.generated_call_contracts
      [of regulatory_completed_word "initial_observed_finality regulation_genesis"]
    by (simp only: regulatory_completed_word_generates_the_same_machine; blast)
  have runtime_contract: "regulation_case.observed_calls.authority_replay_contract (recovery_source regulatory_generated_recovery)"
    and connected: "recovery_connected regulatory_generated_recovery"
    using contract by (simp_all add: regulatory_generated_recovery_def)
  have recovered: "regulatory_checked_current_replay (recovery_source regulatory_generated_recovery)
      (current_source_candidate regulatory_enforced_calls)=Some (call_authority_state regulatory_enforced_calls)"
    by (simp only: regulatory_generated_recovery_def recovered_call_runtime.select_convs,
      rule durable_call_protocol.actual_source_produces_a_valid_complete_candidate[OF contract])
  show ?thesis
    using regulation_case.observed_history_projection.restored_runtime_preserves_all_future_completed_replies(1)
      [OF runtime_contract connected recovered, where actions=actions and call_id="(92,23)"
        and command="Execute_Current 0 (Client_Protocol 2 0 regulation_enforcement_intent)"]
    by (simp only: regulatory_generated_recovery_def recovered_call_runtime.select_convs)
qed

lemma both_regulatory_decisions_are_completed_on_the_same_machine:
  "call_completions regulatory_enforced_calls (92,21)=Some(Effect_Reply(Protocol_Response Request_Rejected))"
  "call_completions regulatory_enforced_calls (92,23)=Some(Effect_Reply(Protocol_Response Descendant_Executed))"
proof -
  have denied: "call_completions regulatory_denied_calls (92,21)=Some(Effect_Reply(Protocol_Response Request_Rejected))"
    using actual_observed_calls_generate_the_previously_required_cut by blast
  show "call_completions regulatory_enforced_calls (92,21)=Some(Effect_Reply(Protocol_Response Request_Rejected))"
    unfolding regulatory_enforced_calls_def
    by (rule regulation_case.observed_completed_replies_survive_finite_continuations[OF denied])
  show "call_completions regulatory_enforced_calls (92,23)=Some(Effect_Reply(Protocol_Response Descendant_Executed))"
    using the_same_call_machine_completes_actual_enforcement by blast
qed

definition regulatory_recovered_future :: "(observed_command,observed_environment) client_call_action list
  \<Rightarrow> regulatory_observed_machine" where
  "regulatory_recovered_future actions=regulation_case.observed_history_projection.reduced.run_calls actions
    (regulation_case.observed_history_projection.normalize_call_machine
      (recovery_source(regulatory_dispatch_from_recovered_replica (92,23)
        (Execute_Current 0(Client_Protocol 2 0 regulation_enforcement_intent))
        (regulatory_restore_current_replica
          (current_source_candidate regulatory_enforced_calls)regulatory_generated_recovery))))"

lemma regulatory_recovery_retains_each_completed_reply:
  assumes completed: "call_completions regulatory_enforced_calls call_id=Some reply"
  shows "call_completions(regulatory_recovered_future actions)call_id=Some reply"
proof -
  have dispatched: "call_completions(regulation_case.observed_calls.dispatch_client_call (92,23)
      (Execute_Current 0(Client_Protocol 2 0 regulation_enforcement_intent))regulatory_enforced_calls)call_id=Some reply"
    using regulation_case.observed_completion_survives_every_step[OF completed,
      where action="Dispatch_Call (92,23)(Execute_Current 0(Client_Protocol 2 0 regulation_enforcement_intent))"]
    by simp
  have continued: "call_completions(regulation_case.observed_calls.run_calls actions
      (regulation_case.observed_calls.dispatch_client_call (92,23)
        (Execute_Current 0(Client_Protocol 2 0 regulation_enforcement_intent))regulatory_enforced_calls))call_id=Some reply"
    by (rule regulation_case.observed_completed_replies_survive_finite_continuations[OF dispatched])
  show ?thesis using continued
    by (simp only: regulatory_recovered_future_def actual_regulatory_machine_recovers_and_transports_every_continuation)
qed

theorem both_regulatory_decisions_survive_recovery_projection_and_future_calls:
  "call_completions(regulatory_recovered_future actions)(92,21)=Some(Effect_Reply(Protocol_Response Request_Rejected))"
  "call_completions(regulatory_recovered_future actions)(92,23)=Some(Effect_Reply(Protocol_Response Descendant_Executed))"
  by (rule regulatory_recovery_retains_each_completed_reply
      [OF both_regulatory_decisions_are_completed_on_the_same_machine(1)],
      rule regulatory_recovery_retains_each_completed_reply
      [OF both_regulatory_decisions_are_completed_on_the_same_machine(2)])

text \<open>The source scenario already produced the monetary credit, terminal
  records, Freeze effect and authorized enforcement. The new application above
  uses its exact states for current observation, nontrivial historical projection
  and the existing restore-and-dispatch law. The restoration keeps the original
  authority machine, log, invocation identifiers and earlier completions.

  The explicit client word now begins at regulation_genesis, completes a
  fresh refresh and unchanged command for every original operation, reaches
  regulation_denied and completes the subsequent enforcement on that same
  call machine. The generated historical snapshot makes normalization
  nontrivial. Recovery uses its complete original log and existing completed
  enforcement identifier before transporting arbitrary future call words.

  The regulatory certificate remains the separately supplied original example
  input. Its physical source production and transport are UNVERIFIED. This
  application introduces no regulatory authority or physical-source claim.
  Equal funding margins cannot replace the current regulatory policy checks.\<close>

end
