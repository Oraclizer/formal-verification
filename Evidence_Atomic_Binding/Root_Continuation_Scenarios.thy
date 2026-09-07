(* SPDX-License-Identifier: BSD-3-Clause *)
theory Root_Continuation_Scenarios
  imports Root_Information
begin

text \<open>The initial machine is the existing two-root, two-holder parent
  execution. The nonempty continuation successfully spends the other root
  through the actual descendant operation. The selected root's frame is
  supplied by the existing general continuation theorem.\<close>

definition root_continuation_initial :: reservation_machine where
  "root_continuation_initial=lineage_history 17"

definition root_continuation_actions :: "reservation_action list" where
  "root_continuation_actions=[Descendant_Action(sample_context ACTIVE)
    (spend_request 23 4 1)(sample_binding 23)3 4 1]"

definition root_continuation_after :: reservation_machine where
  "root_continuation_after=sample.run_reservations sample_balances
    root_continuation_actions root_continuation_initial"

definition root_continuation_effect :: descendant_effect where
  "root_continuation_effect=\<lparr>lineage_root=sample_binding 23,lineage_from=3,lineage_to=4,
    lineage_amount=1,lineage_operation=Ordinary_Transfer_Effect,
    lineage_caller=request_caller(spend_request 23 4 1),
    lineage_authority_epoch=request_authority_epoch(spend_request 23 4 1),
    lineage_version=request_version(spend_request 23 4 1)\<rparr>"

lemma continuation_initial_is_an_actual_parent_execution:
  "root_continuation_initial=sample.run_reservations sample_balances
    ((sample_credit_trace 17@sample_credit_trace 23)@
      [Descendant_Action(sample_context ACTIVE)(spend_request 17 4 5)(sample_binding 17)3 4 5])
    (initial_reservation_machine sample_balances)"
  unfolding root_continuation_initial_def by (rule lineage_history_is_actual_finite_execution)

lemma continuation_initial_supplies_the_parent_contract:
  "sample.reservation_contract sample_balances root_continuation_initial"
  unfolding root_continuation_initial_def by (rule lineage_history_supplies_parent_contract)

lemma continuation_initial_has_both_credited_roots:
  "sample_binding 17\<in>set(credit_history(received_messages(machine_state root_continuation_initial)))"
  "sample_binding 23\<in>set(credit_history(received_messages(machine_state root_continuation_initial)))"
  by (simp_all add: root_continuation_initial_def lineage_trace_defs)

lemma continuation_initial_uses_shared_accounts:
  "binding_asset(sample_binding 17)=17" "binding_asset(sample_binding 23)=17"
  "holder_account(sample_binding 17)3=holder_account(sample_binding 23)3"
  "holder_account(sample_binding 17)4=holder_account(sample_binding 23)4"
  "destination_units(machine_state root_continuation_initial)(2,17,3)=5"
  "destination_units(machine_state root_continuation_initial)(2,17,4)=5"
  "funded_units(machine_state root_continuation_initial)((0,23),(2,17,3))=5"
  "funded_units(machine_state root_continuation_initial)((0,23),(2,17,4))=0"
  "funded_units(machine_state root_continuation_initial)((0,17),(2,17,4))=5"
  "length(filter(\<lambda>effect. binding_key(lineage_root effect)=(0,17))
    (lawful_descendants(machine_state root_continuation_initial)))=1"
  by (simp_all add: root_continuation_initial_def lineage_trace_defs)

lemma continuation_is_nonempty_and_avoids_the_selected_root:
  "root_continuation_actions\<noteq>[]"
  "\<forall>action\<in>set root_continuation_actions. avoids_root(binding_key(sample_binding 17))action"
  by (simp_all add: root_continuation_actions_def sample_binding_def example_binding_def)

lemma other_root_callback_is_the_actual_successful_effect:
  "execute_descendant(sample_context ACTIVE)(spend_request 23 4 1)(sample_binding 23)3 4 1
    root_continuation_initial =
    record_observation(spend_request 23 4 1)Descendant_Executed
      (commit_reservation_event(Descendant_Event root_continuation_effect)root_continuation_initial)"
  by (simp add: root_continuation_initial_def root_continuation_effect_def lineage_trace_defs)

theorem the_nonempty_other_root_action_really_executes:
  "snd(execute_descendant(sample_context ACTIVE)(spend_request 23 4 1)(sample_binding 23)3 4 1
    root_continuation_initial)=Descendant_Executed"
  by (simp only: other_root_callback_is_the_actual_successful_effect;
      simp add: record_observation_def)

lemma continuation_after_is_the_actual_other_root_step:
  "root_continuation_after=fst(execute_descendant(sample_context ACTIVE)
    (spend_request 23 4 1)(sample_binding 23)3 4 1 root_continuation_initial)"
  by (simp only: root_continuation_after_def root_continuation_actions_def
      sample.run_reservations.simps sample.reservation_step.simps)

lemma continuation_after_records_the_other_root_effect:
  "root_continuation_after=fst(record_observation(spend_request 23 4 1)Descendant_Executed
    (commit_reservation_event(Descendant_Event root_continuation_effect)root_continuation_initial))"
  by (simp only: continuation_after_is_the_actual_other_root_step
      other_root_callback_is_the_actual_successful_effect)

theorem the_other_root_moves_one_unit_between_shared_holders:
  "funded_units(machine_state root_continuation_after)((0,23),(2,17,3))=4"
  "funded_units(machine_state root_continuation_after)((0,23),(2,17,4))=1"
  "destination_units(machine_state root_continuation_after)(2,17,3)=4"
  "destination_units(machine_state root_continuation_after)(2,17,4)=6"
  "lawful_descendants(machine_state root_continuation_after)=
    lawful_descendants(machine_state root_continuation_initial)@[root_continuation_effect]"
  by (simp_all add: continuation_after_records_the_other_root_effect record_observation_def
      commit_reservation_event_def root_continuation_effect_def holder_account_def
      sample_binding_def example_binding_def continuation_initial_uses_shared_accounts Let_def)

theorem the_actual_other_root_continuation_activates_the_general_frame:
  "(\<forall>account. funded_units(machine_state root_continuation_after)(binding_key(sample_binding 17),account)=
      funded_units(machine_state root_continuation_initial)(binding_key(sample_binding 17),account)) \<and>
    filter(\<lambda>effect. binding_key(lineage_root effect)=binding_key(sample_binding 17))
      (lawful_descendants(machine_state root_continuation_after)) =
    filter(\<lambda>effect. binding_key(lineage_root effect)=binding_key(sample_binding 17))
      (lawful_descendants(machine_state root_continuation_initial)) \<and>
    snd(execute_descendant(sample_context ACTIVE)(spend_request 17 3 1)(sample_binding 17)4 3 1
      root_continuation_after)=
    snd(execute_descendant(sample_context ACTIVE)(spend_request 17 3 1)(sample_binding 17)4 3 1
      root_continuation_initial)"
  unfolding root_continuation_after_def
proof (rule sample.finite_unrelated_actions_preserve_actual_root_continuation)
  show "sample.reservation_contract sample_balances root_continuation_initial"
    by (rule continuation_initial_supplies_the_parent_contract)
  show "sample_binding 17\<in>set(credit_history(received_messages(machine_state root_continuation_initial)))"
    by (rule continuation_initial_has_both_credited_roots(1))
  show "\<forall>action\<in>set root_continuation_actions. avoids_root(binding_key(sample_binding 17))action"
    by (rule continuation_is_nonempty_and_avoids_the_selected_root(2))
qed

lemma selected_root_initial_continuation_succeeds:
  "snd(execute_descendant(sample_context ACTIVE)(spend_request 17 3 1)(sample_binding 17)4 3 1
    root_continuation_initial)=Descendant_Executed"
  using two_holder_actual_continuation_distinguishes_roots
  by (simp add: two_holder_continuation_def root_continuation_initial_def)

theorem the_selected_root_keeps_funding_history_and_its_actual_success:
  "funded_units(machine_state root_continuation_after)((0,17),(2,17,4))=5 \<and>
    filter(\<lambda>effect. binding_key(lineage_root effect)=(0,17))
      (lawful_descendants(machine_state root_continuation_after)) =
    filter(\<lambda>effect. binding_key(lineage_root effect)=(0,17))
      (lawful_descendants(machine_state root_continuation_initial)) \<and>
    length(filter(\<lambda>effect. binding_key(lineage_root effect)=(0,17))
      (lawful_descendants(machine_state root_continuation_after)))=1 \<and>
    snd(execute_descendant(sample_context ACTIVE)(spend_request 17 3 1)(sample_binding 17)4 3 1
      root_continuation_after)=Descendant_Executed"
proof -
  have funds: "\<forall>account. funded_units(machine_state root_continuation_after)((0,17),account)=
      funded_units(machine_state root_continuation_initial)((0,17),account)"
    and history: "filter(\<lambda>effect. binding_key(lineage_root effect)=(0,17))
        (lawful_descendants(machine_state root_continuation_after)) =
      filter(\<lambda>effect. binding_key(lineage_root effect)=(0,17))
        (lawful_descendants(machine_state root_continuation_initial))"
    and reply: "snd(execute_descendant(sample_context ACTIVE)(spend_request 17 3 1)(sample_binding 17)4 3 1
        root_continuation_after)=
      snd(execute_descendant(sample_context ACTIVE)(spend_request 17 3 1)(sample_binding 17)4 3 1
        root_continuation_initial)"
    using the_actual_other_root_continuation_activates_the_general_frame
    by (auto simp: sample_binding_def example_binding_def)
  show ?thesis using funds history reply selected_root_initial_continuation_succeeds
    continuation_initial_uses_shared_accounts(9,10) by simp
qed

text \<open>The continuation changes pooled balances and the other root's
  account funding, and appends an actual descendant record. The selected
  root already has a nonempty descendant history. Its preservation therefore
  does not rely on an empty program, an empty history or a rejected action.
  Context and request are identical on both sides of the selected consumer
  comparison. This is an activation of the existing finite-continuation
  theorem, not preservation of permission under a policy change.\<close>

end
