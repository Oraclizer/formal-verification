(* SPDX-License-Identifier: BSD-3-Clause *)
theory Source_Coupling_Conservation
  imports Source_Coupling
begin

section \<open>Every Child Credit Consumes a Current Source Finalization\<close>

definition coupling_credits :: "source_coupling_state \<Rightarrow> transfer_binding set" where
  "coupling_credits s=set (credit_history (received_messages (machine_state (core_parent (coupled_core s)))))"

definition coupling_remote_effects :: "source_coupling_state \<Rightarrow> transfer_binding set" where
  "coupling_remote_effects s=set (boundary_effects (controlled_endpoint (coupled_source s)))"

definition coupling_remote_returns :: "source_coupling_state \<Rightarrow> transfer_binding set" where
  "coupling_remote_returns s=set (controlled_returns (coupled_source s))"

definition coupling_credits_finalized :: "source_coupling_state \<Rightarrow> bool" where
  "coupling_credits_finalized s \<longleftrightarrow>
    (\<forall>b\<in>coupling_credits s. controlled_source_fact (coupled_source s) (binding_key b)=
      Some \<lparr>statement_binding=b,statement_status=Finalized\<rparr>)"

definition coupling_unresolved_remote :: "source_coupling_state \<Rightarrow> transfer_binding set" where
  "coupling_unresolved_remote s=
    coupling_remote_effects s-(coupling_remote_returns s\<union>coupling_credits s)"

definition coupling_remote_pending_mass :: "source_coupling_state \<Rightarrow> source_account \<Rightarrow> int"
  where
  "coupling_remote_pending_mass s pool=(\<Sum>b\<in>coupling_unresolved_remote s. binding_mass pool b)"

lemma controlled_reversal_record_is_a_source_fact:
  assumes "controlled_source_invariant balances source" "b\<in>set (controlled_returns source)"
  shows "controlled_source_fact source (binding_key b)=
    Some \<lparr>statement_binding=b,statement_status=Reversed\<rparr>"
proof -
  have recorded: "controlled_outcomes source (binding_key b)=Some (Controlled_Reversed b)"
    using assms unfolding controlled_source_invariant_def controlled_return_history_def by blast
  show ?thesis by (simp add: controlled_source_fact_def recorded)
qed

lemma current_terminal_fact_has_an_exact_source_debit:
  assumes inv: "controlled_source_invariant balances source"
    and fact: "controlled_source_fact source (binding_key b)=
      Some \<lparr>statement_binding=b,statement_status=status\<rparr>"
  shows "b\<in>set (boundary_effects (controlled_endpoint source))"
proof -
  obtain outcome where recorded: "controlled_outcomes source (binding_key b)=Some outcome"
    and statement: "controlled_outcome_statement outcome=
      \<lparr>statement_binding=b,statement_status=status\<rparr>"
    using fact unfolding controlled_source_fact_def by (cases "controlled_outcomes source (binding_key b)") auto
  have bound: "controlled_outcome_binding outcome=b"
    using arg_cong[OF statement, where f=statement_binding]
    by (simp add: controlled_statement_preserves_binding)
  have member: "controlled_outcome_binding outcome\<in>set (boundary_effects (controlled_endpoint source))"
    using controlled_terminal_outcome_has_exact_source_effect[OF inv recorded] by blast
  show ?thesis using member bound by simp
qed

context source_attestation
begin

definition source_coupling_accounting_invariant :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  source_coupling_state \<Rightarrow> bool" where
  "source_coupling_accounting_invariant balances s \<longleftrightarrow>
    source_coupling_invariant balances s \<and> coupling_credits_finalized s"

lemma live_admissible_delivery_has_current_source_finality:
  assumes live: "coupling_live_receipt s (request_certificate r)" and accepted: "credit_admissible c r"
  shows "controlled_source_fact (coupled_source s) (binding_key (request_binding r))=
    Some \<lparr>statement_binding=request_binding r,statement_status=Finalized\<rparr>"
proof -
  have binding: "statement_binding (certificate_statement (request_certificate r))=request_binding r"
    and status: "statement_status (certificate_statement (request_certificate r))=Finalized"
    using accepted unfolding credit_admissible_def authenticated_request_def by blast+
  have whole: "certificate_statement (request_certificate r)=
    \<lparr>statement_binding=request_binding r,statement_status=Finalized\<rparr>"
    using binding status by (cases "certificate_statement (request_certificate r)") auto
  have fact: "controlled_source_fact (coupled_source s)
    (binding_key (statement_binding (certificate_statement (request_certificate r))))=
    Some (certificate_statement (request_certificate r))"
    using live unfolding coupling_live_receipt_def by blast
  show ?thesis using fact by (simp only: whole source_statement.select_convs)
qed

lemma actual_delivery_preserves_a_credit_predicate:
  assumes before: "\<forall>b\<in>set (credit_history (received_messages (machine_state parent))). predicate b"
    and new: "credit_admissible c r \<Longrightarrow> predicate (request_binding r)"
  shows "\<forall>b\<in>set (credit_history (received_messages
    (machine_state (fst (deliver_reserved_credit route c r parent))))). predicate b"
  using before new
  by (auto simp: actual_parent_message_projection published_receive_expansion record_credit_def
    split: if_splits)

lemma non_delivery_intent_preserves_credit_history:
  assumes "\<forall>route r. intent\<noteq>Deliver_Intent route r"
  shows "credit_history (received_messages (machine_state (fst (intent_result c intent parent))))=
    credit_history (received_messages (machine_state parent))"
  using assms
  by (cases intent)
     (auto simp: lift_protocol_result_def protocol_definitions record_observation_def
       commit_reservation_event_def finish_reservation_def set_phase_def Let_def
       split: option.splits message_reply.splits)

lemma actual_guarded_client_preserves_source_finality_for_credit:
  assumes before: "coupling_credits_finalized s" and guard: "coupling_guard available s command"
  shows "\<forall>b\<in>set (credit_history (received_messages
      (machine_state (core_parent (fst (execute_finality_client command (coupled_core s))))))).
    controlled_source_fact (coupled_source s) (binding_key b)=
      Some \<lparr>statement_binding=b,statement_status=Finalized\<rparr>"
proof (cases command)
  case (Client_Protocol endpoint index intent)
  have old: "\<forall>b\<in>set (credit_history (received_messages (machine_state (core_parent (coupled_core s))))).
    controlled_source_fact (coupled_source s) (binding_key b)=
      Some \<lparr>statement_binding=b,statement_status=Finalized\<rparr>"
    using before unfolding coupling_credits_finalized_def coupling_credits_def by blast
  have after_intent: "\<forall>b\<in>set (credit_history (received_messages (machine_state
      (fst (intent_result (current_lock_view (coupled_core s) endpoint) intent (core_parent (coupled_core s))))))).
    controlled_source_fact (coupled_source s) (binding_key b)=
      Some \<lparr>statement_binding=b,statement_status=Finalized\<rparr>"
  proof (cases intent)
    case (Deliver_Intent route r)
    have live: "coupling_live_receipt s (request_certificate r)"
      using guard Client_Protocol Deliver_Intent by simp
    have delivered: "\<forall>b\<in>set (credit_history (received_messages (machine_state
        (fst (deliver_reserved_credit route (lock_authority (current_lock_view (coupled_core s) endpoint))
          r (core_parent (coupled_core s))))))).
      controlled_source_fact (coupled_source s) (binding_key b)=
        Some \<lparr>statement_binding=b,statement_status=Finalized\<rparr>"
      by (rule actual_delivery_preserves_a_credit_predicate[OF old])
         (rule live_admissible_delivery_has_current_source_finality[OF live])
    show ?thesis using delivered Deliver_Intent by (simp add: lift_protocol_result_def)
  qed (use old in \<open>auto simp: lift_protocol_result_def protocol_definitions
      record_observation_def commit_reservation_event_def finish_reservation_def set_phase_def Let_def
      split: option.splits message_reply.splits\<close>)
  show ?thesis using after_intent old Client_Protocol
    by (auto simp: execute_finality_client_def finality_step_def invoke_protocol_def
      reject_protocol_intent_def record_observation_def Let_def split: option.splits)
qed (use before in \<open>auto simp: coupling_credits_finalized_def coupling_credits_def
  execute_finality_client_def finality_step_def record_terminal_def invoke_regulatory_def
  publish_primary_def Let_def split: option.splits\<close>)

lemma source_change_preserves_credit_finality:
  assumes before: "coupling_credits_finalized s"
  shows "coupling_credits_finalized (fst (coupling_source_result arrived replied command s))"
proof (unfold coupling_credits_finalized_def, intro ballI)
  fix b
  assume member: "b\<in>coupling_credits (fst (coupling_source_result arrived replied command s))"
  have old_member: "b\<in>coupling_credits s"
    using member by (simp add: coupling_credits_def coupling_source_result_def Let_def split: if_splits)
  have old: "controlled_source_fact (coupled_source s) (binding_key b)=
    Some \<lparr>statement_binding=b,statement_status=Finalized\<rparr>"
    using before old_member unfolding coupling_credits_finalized_def by blast
  have after_source: "controlled_source_fact (fst (controlled_source_step command (coupled_source s))) (binding_key b)=
    Some \<lparr>statement_binding=b,statement_status=Finalized\<rparr>"
    by (rule controlled_fact_survives_one_step
      [where source="coupled_source s" and key="binding_key b"
        and statement="\<lparr>statement_binding=b,statement_status=Finalized\<rparr>" and command=command])
       (rule old)
  show "controlled_source_fact (coupled_source (fst (coupling_source_result arrived replied command s)))
    (binding_key b)=Some \<lparr>statement_binding=b,statement_status=Finalized\<rparr>"
    using old after_source by (simp add: coupling_source_result_def Let_def split: if_splits)
qed

theorem coupling_step_preserves_source_finality_for_credit:
  assumes "coupling_credits_finalized s"
  shows "coupling_credits_finalized (fst (source_coupling_step action s))"
proof (cases action)
  case (Coupling_Source arrived replied command)
  show ?thesis by (simp only: Coupling_Source source_coupling_step.simps,
    rule source_change_preserves_credit_finality[OF assms])
next
  case (Coupling_Client available command)
  have proved: "coupling_guard available s command \<Longrightarrow>
    \<forall>b\<in>set (credit_history (received_messages
      (machine_state (core_parent (fst (execute_finality_client command (coupled_core s))))))).
    controlled_source_fact (coupled_source s) (binding_key b)=
      Some \<lparr>statement_binding=b,statement_status=Finalized\<rparr>"
    by (rule actual_guarded_client_preserves_source_finality_for_credit[OF assms])
  show ?thesis using assms proved guarded_client_is_the_actual_child
    by (auto simp: Coupling_Client coupling_client_step_def coupling_credits_finalized_def
      coupling_credits_def Let_def split: option.splits if_splits)
qed (use assms in \<open>auto simp: coupling_credits_finalized_def coupling_credits_def
  coupling_issue_result_def execute_finality_environment_def finality_step_def Let_def\<close>)

theorem source_coupling_accounting_step:
  "source_coupling_accounting_invariant balances s \<Longrightarrow>
    source_coupling_accounting_invariant balances (fst (source_coupling_step action s))"
  unfolding source_coupling_accounting_invariant_def
  using source_coupling_step_preserves_invariant coupling_step_preserves_source_finality_for_credit by blast

theorem source_coupling_accounting_run:
  "source_coupling_accounting_invariant balances s \<Longrightarrow>
    source_coupling_accounting_invariant balances (run_source_coupling actions s)"
  by (induction actions arbitrary:s) (auto intro: source_coupling_accounting_step)

theorem generated_joint_accounting_invariant:
  "source_coupling_accounting_invariant balances
    (run_source_coupling actions (initial_source_coupling balances regulatory contexts))"
proof (rule source_coupling_accounting_run)
  have initial_joint: "source_coupling_invariant balances (initial_source_coupling balances regulatory contexts)"
    by (rule initial_source_coupling_invariant)
  have initial_finality: "coupling_credits_finalized (initial_source_coupling balances regulatory contexts)"
    by (simp add: coupling_credits_finalized_def coupling_credits_def initial_source_coupling_def
      initial_finality_core_def initial_reservation_machine_def initial_reservation_state_def
      empty_message_state_def)
  show "source_coupling_accounting_invariant balances (initial_source_coupling balances regulatory contexts)"
    using initial_joint initial_finality
    unfolding source_coupling_accounting_invariant_def by blast
qed

theorem remote_return_and_child_credit_are_disjoint:
  assumes inv: "source_coupling_accounting_invariant balances s"
  shows "coupling_remote_returns s\<inter>coupling_credits s={}"
proof (rule ccontr)
  assume "\<not>coupling_remote_returns s\<inter>coupling_credits s={}"
  then obtain b where returned: "b\<in>coupling_remote_returns s" and credited: "b\<in>coupling_credits s" by blast
  have source: "controlled_source_invariant balances (coupled_source s)"
    and final: "coupling_credits_finalized s"
    using inv unfolding source_coupling_accounting_invariant_def source_coupling_invariant_def by blast+
  have reverse_fact: "controlled_source_fact (coupled_source s) (binding_key b)=
    Some \<lparr>statement_binding=b,statement_status=Reversed\<rparr>"
    by (rule controlled_reversal_record_is_a_source_fact[OF source])
       (use returned in \<open>simp add: coupling_remote_returns_def\<close>)
  have final_fact: "controlled_source_fact (coupled_source s) (binding_key b)=
    Some \<lparr>statement_binding=b,statement_status=Finalized\<rparr>"
    using final credited unfolding coupling_credits_finalized_def by blast
  show False using reverse_fact final_fact by simp
qed

lemma remote_returns_and_credits_are_source_effects:
  assumes inv: "source_coupling_accounting_invariant balances s"
  shows "coupling_remote_returns s\<subseteq>coupling_remote_effects s \<and>
    coupling_credits s\<subseteq>coupling_remote_effects s"
proof -
  have source: "controlled_source_invariant balances (coupled_source s)"
    and final: "coupling_credits_finalized s"
    using inv unfolding source_coupling_accounting_invariant_def source_coupling_invariant_def by blast+
  have returned: "\<And>b. b\<in>coupling_remote_returns s \<Longrightarrow> b\<in>coupling_remote_effects s"
  proof -
    fix b
    assume b: "b\<in>coupling_remote_returns s"
    have fact: "controlled_source_fact (coupled_source s) (binding_key b)=
      Some \<lparr>statement_binding=b,statement_status=Reversed\<rparr>"
      by (rule controlled_reversal_record_is_a_source_fact[OF source])
         (use b in \<open>simp add: coupling_remote_returns_def\<close>)
    show "b\<in>coupling_remote_effects s"
      using current_terminal_fact_has_an_exact_source_debit[OF source fact]
      by (simp add: coupling_remote_effects_def)
  qed
  have credited: "\<And>b. b\<in>coupling_credits s \<Longrightarrow> b\<in>coupling_remote_effects s"
  proof -
    fix b
    assume b: "b\<in>coupling_credits s"
    have fact: "controlled_source_fact (coupled_source s) (binding_key b)=
      Some \<lparr>statement_binding=b,statement_status=Finalized\<rparr>"
      using final b unfolding coupling_credits_finalized_def by blast
    show "b\<in>coupling_remote_effects s"
      using current_terminal_fact_has_an_exact_source_debit[OF source fact]
      by (simp add: coupling_remote_effects_def)
  qed
  show ?thesis using returned credited by blast
qed

end

section \<open>Actual Source Pool Conservation\<close>

lemma filtered_amount_is_binding_mass:
  "int (sum_list (map binding_amount (filter (\<lambda>b. source_account_of b=pool) history)))=
    sum_list (map (binding_mass pool) history)"
  by (induction history) (auto simp: binding_mass_def)

lemma controlled_debit_set_mass:
  assumes "boundary_history_consistent source"
  shows "int (boundary_debited pool source)=(\<Sum>b\<in>set (boundary_effects source). binding_mass pool b)"
proof -
  have unique: "distinct (map binding_key (boundary_effects source))"
    using assms unfolding boundary_history_consistent_def by blast
  have distinct: "distinct (boundary_effects source)"
    using unique by (simp only: distinct_map)
  show ?thesis
    by (simp add: boundary_debited_def filtered_amount_is_binding_mass
      sum_list_distinct_conv_sum_set[OF distinct])
qed

lemma controlled_return_set_mass:
  assumes "controlled_return_history source"
  shows "int (controlled_returned pool source)=(\<Sum>b\<in>set (controlled_returns source). binding_mass pool b)"
proof -
  have unique: "distinct (map binding_key (controlled_returns source))"
    using assms unfolding controlled_return_history_def by blast
  have distinct: "distinct (controlled_returns source)"
    using unique by (simp only: distinct_map)
  show ?thesis
    by (simp add: controlled_returned_def filtered_amount_is_binding_mass
      sum_list_distinct_conv_sum_set[OF distinct])
qed

context source_attestation
begin

theorem actual_source_pool_is_conserved:
  assumes inv: "source_coupling_accounting_invariant balances s"
  shows "int (boundary_units (controlled_endpoint (coupled_source s)) pool)+
    coupling_remote_pending_mass s pool+
    destination_pool_funding (machine_state (core_parent (coupled_core s))) pool=int (balances pool)"
proof -
  let ?E="coupling_remote_effects s"
  let ?R="coupling_remote_returns s"
  let ?C="coupling_credits s"
  let ?U="coupling_unresolved_remote s"
  have source: "controlled_source_invariant balances (coupled_source s)"
    and parent: "reservation_contract balances (core_parent (coupled_core s))"
    using inv unfolding source_coupling_accounting_invariant_def source_coupling_invariant_def by blast+
  have history: "boundary_history_consistent (controlled_endpoint (coupled_source s))"
    and returns: "controlled_return_history (coupled_source s)"
    using source unfolding controlled_source_invariant_def by blast+
  have finiteE: "finite ?E" and finiteR: "finite ?R" and finiteC: "finite ?C" and finiteU: "finite ?U"
    by (simp_all add: coupling_remote_effects_def coupling_remote_returns_def coupling_credits_def
      coupling_unresolved_remote_def)
  have included: "?R\<subseteq>?E \<and> ?C\<subseteq>?E"
    by (rule remote_returns_and_credits_are_source_effects[OF inv])
  have RC: "?R\<inter>?C={}" by (rule remote_return_and_child_credit_are_disjoint[OF inv])
  have partition: "?E=?U\<union>?C\<union>?R"
    using included unfolding coupling_unresolved_remote_def by blast
  have UC: "?U\<inter>?C={}" and UR: "(?U\<union>?C)\<inter>?R={}"
    using RC unfolding coupling_unresolved_remote_def by blast+
  have split: "(\<Sum>b\<in>?E. binding_mass pool b)=
    (\<Sum>b\<in>?U. binding_mass pool b)+(\<Sum>b\<in>?C. binding_mass pool b)+
    (\<Sum>b\<in>?R. binding_mass pool b)"
    by (simp only: partition sum.union_disjoint[OF finite_UnI[OF finiteU finiteC] finiteR UR]
      sum.union_disjoint[OF finiteU finiteC UC])
  have debit_mass: "int (boundary_debited pool (controlled_endpoint (coupled_source s)))=
    (\<Sum>b\<in>?E. binding_mass pool b)"
    using controlled_debit_set_mass[OF history, where pool=pool] by (simp add: coupling_remote_effects_def)
  have return_mass: "int (controlled_returned pool (coupled_source s))=(\<Sum>b\<in>?R. binding_mass pool b)"
    using controlled_return_set_mass[OF returns, where pool=pool] by (simp add: coupling_remote_returns_def)
  have nat_balance: "boundary_units (controlled_endpoint (coupled_source s)) pool+
    boundary_debited pool (controlled_endpoint (coupled_source s))=
    balances pool+controlled_returned pool (coupled_source s)"
    by (rule controlled_net_resource_equation[OF source])
  have balance: "int (boundary_units (controlled_endpoint (coupled_source s)) pool)+
    int (boundary_debited pool (controlled_endpoint (coupled_source s)))=
    int (balances pool)+int (controlled_returned pool (coupled_source s))"
    using arg_cong[OF nat_balance, where f="\<lambda>n. int n"] by simp
  have financial: "financial_history_agreement balances (core_parent (coupled_core s))"
    and messages: "message_invariant (received_messages (machine_state (core_parent (coupled_core s))))"
    using parent unfolding reservation_contract_def message_source_invariant_def by blast+
  have funding: "destination_pool_funding (machine_state (core_parent (coupled_core s))) pool=
    (\<Sum>b\<in>?C. binding_mass pool b)"
    using destination_pool_funding_is_credit_mass[OF financial messages, where account=pool]
    by (simp only: coupling_credits_def)
  show ?thesis using balance debit_mass return_mass split funding
    unfolding coupling_remote_pending_mass_def by linarith
qed

theorem all_finite_joint_executions_preserve_actual_source_allocation:
  "int (boundary_units (controlled_endpoint (coupled_source
      (run_source_coupling actions (initial_source_coupling balances regulatory contexts)))) pool)+
    coupling_remote_pending_mass (run_source_coupling actions
      (initial_source_coupling balances regulatory contexts)) pool+
    destination_pool_funding (machine_state (core_parent (coupled_core
      (run_source_coupling actions (initial_source_coupling balances regulatory contexts))))) pool=
    int (balances pool)"
  by (rule actual_source_pool_is_conserved[OF generated_joint_accounting_invariant])

end

section \<open>A Generated Credit and Two Distinct Negative Controls\<close>

definition conservation_contexts :: "nat \<Rightarrow> lock_context" where
  "conservation_contexts endpoint=
    (if endpoint=0 then sample_source_context ACTIVE else sample_context ACTIVE)"

definition conservation_initial :: source_coupling_state where
  "conservation_initial=initial_source_coupling sample_balances (sample_metadata ACTIVE) conservation_contexts"

definition conservation_credit_request :: execution_request where
  "conservation_credit_request=(sample_request 17)\<lparr>request_certificate:=linked_certificate 17\<rparr>"

definition conservation_credit_word :: "source_coupling_action list" where
  "conservation_credit_word=coupling_prepare 17@[
    Coupling_Source True True (Controlled_Boundary (Boundary_Apply (sample_binding 17))),
    Coupling_Client True (Client_Protocol 0 0 (Source_Intent (sample_request 17) 0 [])),
    Coupling_Source True True (Controlled_Finalize (sample_binding 17)),
    Coupling_Issue True (linked_certificate 17),
    Coupling_Client True (Client_Terminal (linked_certificate 17)),
    Coupling_Client True (Client_Protocol 0 0 (Certificate_Intent (linked_certificate 17))),
    Coupling_Client True (Client_Protocol 2 0 (Deliver_Intent Bypass_Route conservation_credit_request))]"

definition conservation_credited :: source_coupling_state where
  "conservation_credited=linked.run_source_coupling conservation_credit_word conservation_initial"

theorem conservation_credit_word_has_the_generated_strong_invariant:
  "linked.source_coupling_accounting_invariant sample_balances conservation_credited"
  unfolding conservation_credited_def conservation_initial_def
  by (rule linked.generated_joint_accounting_invariant)

lemmas conservation_execution_rules =
  linked.run_source_coupling.simps linked.source_coupling_step.simps
  linked.coupling_client_step_def linked.coupling_client_result.simps
  linked.execute_finality_client_def linked.finality_step_def linked.core_result.simps
  linked.invoke_protocol_def linked.intent_result.simps linked.record_terminal_def
  linked.publish_source_certificate_def linked.deliver_reserved_credit_def linked.published_receive_expansion
  linked.credit_admissible_def linked.authenticated_request_def linked.certificate_ok_def

lemma conservation_credit_projection:
  "boundary_effects (controlled_endpoint (coupled_source conservation_credited))=[sample_binding 17] \<and>
    controlled_returns (coupled_source conservation_credited)=[] \<and>
    controlled_outcomes (coupled_source conservation_credited) (0,17)=Some (Controlled_Finalized (sample_binding 17)) \<and>
    boundary_units (controlled_endpoint (coupled_source conservation_credited)) (0,17)=5 \<and>
    source_effects (machine_state (core_parent (coupled_core conservation_credited)))=[sample_binding 17] \<and>
    credit_history (received_messages (machine_state (core_parent (coupled_core conservation_credited))))=
      [sample_binding 17] \<and>
    returned_bindings (machine_journal (core_parent (coupled_core conservation_credited)))=[] \<and>
    coupled_sent conservation_credited={(0,17)} \<and> coupled_blocked conservation_credited={}"
proof -
  let ?b="sample_binding 17"
  let ?cert="linked_certificate 17"
  let ?r="conservation_credit_request"
  let ?source_command="Client_Protocol 0 0 (Source_Intent (sample_request 17) 0 [])"
  let ?entry="\<lparr>terminal_binding=?b,terminal_kind=Confirmed_Decision,terminal_evidence=[?cert]\<rparr>"
  define prepared where "prepared=linked.run_source_coupling (coupling_prepare 17) conservation_initial"
  define applied where "applied=fst(linked.source_coupling_step
    (Coupling_Source True True (Controlled_Boundary(Boundary_Apply ?b)))prepared)"
  define sourced where "sourced=fst(linked.source_coupling_step (Coupling_Client True ?source_command)applied)"
  define finalized where "finalized=fst(linked.source_coupling_step
    (Coupling_Source True True (Controlled_Finalize ?b))sourced)"
  define issued where "issued=fst(linked.source_coupling_step (Coupling_Issue True ?cert)finalized)"
  define terminal where "terminal=fst(linked.source_coupling_step
    (Coupling_Client True (Client_Terminal ?cert))issued)"
  define published where "published=fst(linked.source_coupling_step
    (Coupling_Client True (Client_Protocol 0 0 (Certificate_Intent ?cert)))terminal)"
  define delivered where "delivered=fst(linked.source_coupling_step
    (Coupling_Client True (Client_Protocol 2 0 (Deliver_Intent Bypass_Route ?r)))published)"
  have word: "conservation_credited=delivered"
    unfolding conservation_credited_def conservation_credit_word_def delivered_def published_def
      terminal_def issued_def finalized_def sourced_def applied_def prepared_def coupling_prepare_def
    by (simp only: append.simps linked.run_source_coupling.simps)

  have binding: "binding_key ?b=(0,17)" "binding_operation ?b=Destination_Credit" "0<binding_amount ?b"
    "binding_destination ?b=2"
    by (simp_all add: sample_binding_def example_binding_def)
  have certificate: "certificate_statement ?cert=\<lparr>statement_binding=?b,statement_status=Finalized\<rparr>"
    and certificate_epoch: "certificate_epoch ?cert=8"
    by (simp_all add: linked_certificate_def sample_statement_def)
  have certificate_ok: "linked.certificate_ok ?cert"
    using linked_certificates_pass_the_parent_checker[of 17] by simp
  have request_binding: "request_binding ?r=?b" and request_certificate: "request_certificate ?r=?cert"
    by (simp_all add: conservation_credit_request_def sample_request_def)
  have prepared_source: "coupled_source prepared=initial_controlled_source sample_balances"
    and prepared_sent: "coupled_sent prepared={}"
    and prepared_blocked: "coupled_blocked prepared={}"
    and prepared_receipts: "coupled_receipts prepared=[]"
    unfolding prepared_def coupling_prepare_def linked.run_source_coupling.simps
    by (simp_all add: conservation_initial_def initial_source_coupling_def
      linked.coupling_client_step_def Let_def)

  define effect_source where "effect_source=fst(controlled_source_step
    (Controlled_Boundary(Boundary_Apply ?b))(initial_controlled_source sample_balances))"
  have applied_source: "coupled_source applied=effect_source"
    and applied_core: "coupled_core applied=coupled_core prepared"
    and applied_sent: "coupled_sent applied={(0,17)}"
    and applied_blocked: "coupled_blocked applied={}"
    and applied_receipts: "coupled_receipts applied=[]"
    by (simp_all add: applied_def coupling_source_result_def effect_source_def
      prepared_source prepared_sent prepared_blocked prepared_receipts binding Let_def)
  have effect: "boundary_has_effect ?b(controlled_endpoint effect_source)"
    and outcome: "controlled_outcomes effect_source(binding_key ?b)=None"
    by (simp_all add: effect_source_def controlled_boundary_def initial_controlled_source_def
      initial_source_boundary_def boundary_apply_def boundary_record_effect_def boundary_has_effect_def
      boundary_valid_binding_def sample_binding_def example_binding_def sample_balances_def source_account_of_def Let_def)
  have source_guard: "coupling_guard True applied ?source_command"
    using effect by (simp add: applied_source coupling_effect_witness_def boundary_evidence_exact sample_request_def)
  define source_core where "source_core=fst(linked.execute_finality_client ?source_command(coupled_core prepared))"
  have sourced_core: "coupled_core sourced=source_core"
    and sourced_source: "coupled_source sourced=effect_source"
    and sourced_sent: "coupled_sent sourced={(0,17)}"
    and sourced_blocked: "coupled_blocked sourced={}"
    and sourced_receipts: "coupled_receipts sourced=[]"
    using source_guard[simplified coupling_guard.simps coupling_intent_guard.simps]
    by (auto simp: sourced_def linked.coupling_client_step_def source_core_def
      applied_core applied_source applied_sent applied_blocked applied_receipts Let_def)
  have source_core_shape: "source_core=(initial_finality_core sample_balances
    (sample_metadata ACTIVE)conservation_contexts)\<lparr>core_parent:=sample_burnt 17,core_epoch:=3\<rparr>"
    unfolding source_core_def prepared_def coupling_prepare_def linked.run_source_coupling.simps
    by (simp add: conservation_initial_def conservation_contexts_def initial_source_coupling_def
      conservation_execution_rules initial_finality_core_def current_lock_view_def lift_protocol_result_def
      vector_lookup_def sample_data_defs sample.run_reservations.simps sample.reservation_step.simps
      acquire_reservation_def dispatch_source_def execute_source_effect_def record_observation_def
      commit_reservation_event_def Let_def)
  have source_parent: "core_parent source_core=sample_burnt 17"
    and source_epoch: "core_epoch source_core=3"
    and source_records: "core_records source_core=(\<lambda>_.None)"
    and source_context: "current_lock_view source_core 0=sample_source_context ACTIVE"
    and destination_context: "current_lock_view source_core 2=sample_context ACTIVE"
    by (simp_all add: source_core_shape initial_finality_core_def current_lock_view_def
      conservation_contexts_def sample_source_context_def sample_context_def)
  have parent_effects: "source_effects(machine_state(sample_burnt 17))=[?b]"
    using source_acquire_dispatch_effect_activates by blast
  have parent_empty: "issued_certificates(machine_state(sample_burnt 17))=[]"
    "received_messages(machine_state(sample_burnt 17))=empty_message_state"
    by (simp_all add: sample_data_defs sample.run_reservations.simps sample.reservation_step.simps
      acquire_reservation_def dispatch_source_def execute_source_effect_def record_observation_def
      commit_reservation_event_def Let_def)

  define final_source where "final_source=controlled_record_finalized ?b effect_source"
  have finalized_source: "coupled_source finalized=final_source"
    and finalized_core: "coupled_core finalized=source_core"
    and finalized_sent: "coupled_sent finalized={(0,17)}"
    and finalized_blocked: "coupled_blocked finalized={}"
    and finalized_receipts: "coupled_receipts finalized=[]"
    by (simp_all add: finalized_def coupling_source_result_def controlled_finalize_def effect outcome
      final_source_def sourced_source sourced_core sourced_sent sourced_blocked sourced_receipts Let_def)
  have final_fact: "controlled_source_fact final_source(binding_key ?b)=
      Some \<lparr>statement_binding=?b,statement_status=Finalized\<rparr>"
    by (simp add: final_source_def controlled_record_finalized_def controlled_source_fact_def)
  have remote_fields: "boundary_effects(controlled_endpoint final_source)=[?b]"
    "controlled_returns final_source=[]"
    "controlled_outcomes final_source(0,17)=Some(Controlled_Finalized ?b)"
    "boundary_units(controlled_endpoint final_source)(0,17)=5"
    by (simp_all add: final_source_def controlled_record_finalized_def effect_source_def
      controlled_boundary_def initial_controlled_source_def initial_source_boundary_def boundary_apply_def
      boundary_record_effect_def boundary_valid_binding_def sample_binding_def example_binding_def
      sample_balances_def source_account_of_def Let_def)
  have issued_shape: "issued=finalized\<lparr>coupled_receipts:=[?cert]\<rparr>"
    by (simp add: issued_def coupling_issue_result_def issue_source_receipt_def source_receipt_slot_available_def
      finalized_source finalized_receipts final_fact certificate Let_def)
  have issued_live: "coupling_live_receipt issued ?cert"
    by (simp add: coupling_live_receipt_def issued_shape finalized_source final_fact certificate)
  have issued_core: "coupled_core issued=source_core"
    by (simp add: issued_shape finalized_core)
  have terminal_guard: "coupling_guard True issued(Client_Terminal ?cert)"
    using issued_live by simp
  let ?terminal_core="source_core\<lparr>core_records:=(core_records source_core)(binding_key ?b:=Some ?entry),core_epoch:=4\<rparr>"
  have terminal_execution: "linked.execute_finality_client(Client_Terminal ?cert)source_core=(?terminal_core,Terminal_Recorded)"
    by (simp add: linked.execute_finality_client_def linked.finality_step_def linked.core_result.simps
      linked.record_terminal_def certificate_ok certificate source_origin_present_def source_parent
      parent_effects source_records source_epoch binding Let_def)
  have terminal_shape: "terminal=issued\<lparr>coupled_core:=?terminal_core\<rparr>"
    using terminal_guard[simplified coupling_guard.simps]
    by (auto simp: terminal_def linked.coupling_client_step_def issued_core terminal_execution Let_def)
  have terminal_live: "coupling_live_receipt terminal ?cert"
    by (simp add: terminal_shape coupling_live_receipt_def issued_shape finalized_source final_fact certificate)
  have terminal_core: "coupled_core terminal=?terminal_core"
    by (simp add: terminal_shape)
  have publication_guard: "coupling_guard True terminal(Client_Protocol 0 0(Certificate_Intent ?cert))"
    using terminal_live by simp
  let ?published_parent="commit_reservation_event(Certificate_Event ?cert)(sample_burnt 17)"
  let ?published_core="?terminal_core\<lparr>core_parent:=?published_parent,core_epoch:=5\<rparr>"
  have publication: "linked.publish_source_certificate ?cert(sample_burnt 17)=?published_parent"
    by (simp add: linked.publish_source_certificate_def certificate_ok certificate parent_effects Let_def)
  have publication_execution: "linked.execute_finality_client
      (Client_Protocol 0 0(Certificate_Intent ?cert))?terminal_core=(?published_core,Internal_Completed)"
    by (simp add: linked.execute_finality_client_def linked.finality_step_def linked.core_result.simps
      linked.invoke_protocol_def linked.intent_result.simps certificate source_parent publication
      exact_record_reference_def record_reference_def Let_def)
  have published_shape: "published=terminal\<lparr>coupled_core:=?published_core\<rparr>"
    using publication_guard[simplified coupling_guard.simps coupling_intent_guard.simps]
    by (auto simp: published_def linked.coupling_client_step_def terminal_core publication_execution Let_def)
  have published_live: "coupling_live_receipt published ?cert"
    by (simp add: published_shape terminal_shape coupling_live_receipt_def issued_shape
      finalized_source final_fact certificate)
  have request_use: "current_use_allowed example_context ?r"
    by (simp add: current_use_allowed_def conservation_credit_request_def sample_request_def
      sample_binding_def example_binding_def example_context_def)
  have context_fields: "context_relay_epoch example_context=8" "context_endpoint example_context=2"
    by (simp_all add: example_context_def)
  have admissible: "linked.credit_admissible example_context ?r"
    by (simp add: linked.credit_admissible_def linked.authenticated_request_def request_binding
      request_certificate certificate_ok certificate certificate_epoch request_use binding context_fields)
  have receive: "linked.published_receive Bypass_Route example_context ?r(machine_state ?published_parent)=
      (record_credit ?b empty_message_state,New_Credit ?b)"
    by (simp add: linked.published_receive_expansion admissible request_certificate request_binding
      commit_reservation_event_def parent_empty empty_message_state_def)
  let ?credited_parent="fst(record_observation ?r(Delivery_Response(New_Credit ?b))
    (commit_reservation_event(Credit_Event ?b)?published_parent))"
  have delivery: "linked.deliver_reserved_credit Bypass_Route example_context ?r ?published_parent=
      (?credited_parent,Delivery_Response(New_Credit ?b))"
    by (simp only: linked.deliver_reserved_credit_def receive snd_conv;
        simp add: record_observation_def)
  have delivery_execution: "fst(linked.execute_finality_client
      (Client_Protocol 2 0(Deliver_Intent Bypass_Route ?r))?published_core)=
      ?published_core\<lparr>core_parent:=?credited_parent,core_epoch:=6\<rparr>"
    by (simp add: linked.execute_finality_client_def linked.finality_step_def linked.core_result.simps
      linked.invoke_protocol_def linked.intent_result.simps lift_protocol_result_def destination_context
      sample_context_def request_binding request_certificate exact_record_reference_def record_reference_def
      delivery Let_def)
  have delivery_guard: "coupling_guard True published(Client_Protocol 2 0(Deliver_Intent Bypass_Route ?r))"
    using published_live by (simp add: request_certificate)
  have published_core: "coupled_core published=?published_core"
    and published_source: "coupled_source published=final_source"
    and published_sent: "coupled_sent published={(0,17)}"
    and published_blocked: "coupled_blocked published={}"
    by (simp_all add: published_shape terminal_shape issued_shape finalized_source finalized_sent finalized_blocked)
  have delivered_core: "coupled_core delivered=?published_core\<lparr>core_parent:=?credited_parent,core_epoch:=6\<rparr>"
    and delivered_source: "coupled_source delivered=final_source"
    and delivered_sent: "coupled_sent delivered={(0,17)}"
    and delivered_blocked: "coupled_blocked delivered={}"
    using delivery_guard[simplified coupling_guard.simps coupling_intent_guard.simps]
      delivery_execution[simplified]
    by (auto simp: delivered_def linked.coupling_client_step_def published_core
      published_source published_sent published_blocked Let_def)
  have parent_projection: "source_effects(machine_state ?credited_parent)=[?b]"
    "credit_history(received_messages(machine_state ?credited_parent))=[?b]"
    "returned_bindings(machine_journal ?credited_parent)=[]"
    by (simp_all add: record_observation_def commit_reservation_event_def record_credit_def
      empty_message_state_def returned_bindings_def sample_data_defs sample.run_reservations.simps
      sample.reservation_step.simps acquire_reservation_def dispatch_source_def execute_source_effect_def Let_def)
  show ?thesis using parent_effects parent_empty
    by (simp add: word delivered_core delivered_source delivered_sent delivered_blocked
      parent_projection remote_fields empty_message_state_def)
qed

lemma conservation_credited_funding_is_five:
  "linked.destination_pool_funding (machine_state (core_parent (coupled_core conservation_credited))) (0,17)=5"
proof -
  have strong: "linked.source_coupling_accounting_invariant sample_balances conservation_credited"
    by (rule conservation_credit_word_has_the_generated_strong_invariant)
  have financial: "financial_history_agreement sample_balances (core_parent (coupled_core conservation_credited))"
    and messages: "linked.message_invariant
      (received_messages (machine_state (core_parent (coupled_core conservation_credited))))"
    using strong unfolding linked.source_coupling_accounting_invariant_def linked.source_coupling_invariant_def
      linked.reservation_contract_def linked.message_source_invariant_def by blast+
  have mass: "linked.destination_pool_funding
      (machine_state (core_parent (coupled_core conservation_credited))) (0,17)=
    (\<Sum>b\<in>set (credit_history (received_messages
      (machine_state (core_parent (coupled_core conservation_credited))))). binding_mass (0,17) b)"
    by (rule linked.destination_pool_funding_is_credit_mass[OF financial messages])
  show ?thesis using mass conservation_credit_projection
    by (simp add: binding_mass_def source_account_of_def sample_binding_def example_binding_def)
qed

lemma conservation_credited_has_actual_effect_evidence:
  "boundary_has_effect (sample_binding 17) (controlled_endpoint (coupled_source conservation_credited))"
proof -
  have inv: "controlled_source_invariant sample_balances (coupled_source conservation_credited)"
    using conservation_credit_word_has_the_generated_strong_invariant
    unfolding linked.source_coupling_accounting_invariant_def linked.source_coupling_invariant_def by blast
  have history: "boundary_history_consistent (controlled_endpoint (coupled_source conservation_credited))"
    using inv unfolding controlled_source_invariant_def by blast
  have member: "sample_binding 17\<in>set (boundary_effects (controlled_endpoint (coupled_source conservation_credited)))"
    using conservation_credit_projection by simp
  show ?thesis using history member
    unfolding boundary_history_consistent_def boundary_has_effect_def by blast
qed

theorem generated_credit_counts_one_actual_allocation:
  "int (boundary_units (controlled_endpoint (coupled_source conservation_credited)) (0,17))+
    coupling_remote_pending_mass conservation_credited (0,17)+
    linked.destination_pool_funding (machine_state (core_parent (coupled_core conservation_credited))) (0,17)=10"
  using linked.actual_source_pool_is_conserved
    [where balances=sample_balances and s=conservation_credited and pool="(0,17)",
      OF conservation_credit_word_has_the_generated_strong_invariant]
  by (simp add: sample_balances_def)

definition independently_reversed_source :: controlled_source_state where
  "independently_reversed_source=run_controlled_source
    [Controlled_Boundary (Boundary_Apply (sample_binding 17)),Controlled_Reverse (sample_binding 17)]
    (initial_controlled_source sample_balances)"

definition weakly_mixed_source_views :: source_coupling_state where
  "weakly_mixed_source_views=conservation_credited
    \<lparr>coupled_source:=independently_reversed_source,coupled_receipts:=[]\<rparr>"

lemma independently_reversed_source_projection:
  "boundary_effects (controlled_endpoint independently_reversed_source)=[sample_binding 17] \<and>
    controlled_returns independently_reversed_source=[sample_binding 17] \<and>
    boundary_units (controlled_endpoint independently_reversed_source) (0,17)=10"
  by (simp add: independently_reversed_source_def initial_controlled_source_def initial_source_boundary_def
    controlled_boundary_def controlled_reverse_def controlled_record_reversed_def boundary_apply_def
    boundary_record_effect_def boundary_has_effect_def boundary_valid_binding_def sample_balances_def
    sample_binding_def example_binding_def source_account_of_def Let_def)

theorem weak_source_mirror_conditions_allow_incompatible_fragments:
  "linked.source_coupling_invariant sample_balances weakly_mixed_source_views"
proof -
  have remote: "controlled_source_invariant sample_balances independently_reversed_source"
    unfolding independently_reversed_source_def by (rule controlled_all_finite_executions)
  have before: "linked.source_coupling_invariant sample_balances conservation_credited"
    using conservation_credit_word_has_the_generated_strong_invariant
    unfolding linked.source_coupling_accounting_invariant_def by blast
  show ?thesis using remote before conservation_credit_projection independently_reversed_source_projection
    by (auto simp: weakly_mixed_source_views_def linked.source_coupling_invariant_def
      source_mirror_provenance_def coupling_receipts_sound_def coupling_sent_covers_effects_def
      coupling_blocked_protected_def sample_binding_def example_binding_def)
qed

theorem weak_fragments_have_fifteen_units_against_ten:
  "int (boundary_units (controlled_endpoint (coupled_source weakly_mixed_source_views)) (0,17))+
    coupling_remote_pending_mass weakly_mixed_source_views (0,17)+
    linked.destination_pool_funding (machine_state (core_parent (coupled_core weakly_mixed_source_views))) (0,17)=15 \<and>
    sample_balances (0,17)=10"
  using conservation_credit_projection independently_reversed_source_projection conservation_credited_funding_is_five
  by (simp add: weakly_mixed_source_views_def coupling_remote_pending_mass_def coupling_unresolved_remote_def
    coupling_remote_effects_def coupling_remote_returns_def coupling_credits_def sample_balances_def)

text \<open>The mixed state combines a source reversal fragment with a child
  credit fragment from a different source outcome. The earlier mirror
  conditions admit this combination, but the strengthened generated invariant
  does not. It is not presented as an execution of the original joint
  dispatcher. The following mutation is a separate, actual transition test.\<close>

definition reverse_without_finalization_guard :: "transfer_binding \<Rightarrow> controlled_source_state
  \<Rightarrow> controlled_source_state \<times> controlled_source_reply" where
  "reverse_without_finalization_guard b source=
    (if controlled_outcomes source (binding_key b)=Some (Controlled_Finalized b) \<and>
        boundary_has_effect b (controlled_endpoint source)
     then (controlled_record_reversed b source,
       Controlled_Outcome_Reply \<lparr>statement_binding=b,statement_status=Reversed\<rparr>)
     else controlled_reverse b source)"

definition source_reverse_guard_removed :: "transfer_binding \<Rightarrow> source_coupling_state
  \<Rightarrow> source_coupling_state \<times> source_coupling_reply" where
  "source_reverse_guard_removed b s=
    (let result=reverse_without_finalization_guard b (coupled_source s)
     in (s\<lparr>coupled_source:=fst result\<rparr>,Coupling_Source_Reply (snd result)))"

lemma reverse_mutation_is_identical_outside_the_finalized_branch:
  assumes "controlled_outcomes (coupled_source s) (binding_key b)\<noteq>Some (Controlled_Finalized b)"
  shows "source_reverse_guard_removed b s=
    linked.source_coupling_step (Coupling_Source True True (Controlled_Reverse b)) s"
  using assms by (simp add: source_reverse_guard_removed_def reverse_without_finalization_guard_def
    linked.source_coupling_step.simps coupling_source_result_def Let_def)

definition mutated_after_credit :: source_coupling_state where
  "mutated_after_credit=fst (source_reverse_guard_removed (sample_binding 17) conservation_credited)"

theorem ordinary_source_reverse_rejects_after_the_generated_credit:
  "linked.source_coupling_step (Coupling_Source True True (Controlled_Reverse (sample_binding 17)))
    conservation_credited=(conservation_credited,Coupling_Source_Reply Controlled_Outcome_Rejected)"
  using conservation_credit_projection
  by (simp add: linked.source_coupling_step.simps coupling_source_result_def controlled_reverse_def
    sample_binding_def example_binding_def Let_def)

theorem removing_only_the_finalization_guard_refunds_a_credited_root:
  "sample_binding 17\<in>coupling_remote_returns mutated_after_credit \<and>
    sample_binding 17\<in>coupling_credits mutated_after_credit \<and>
    boundary_units (controlled_endpoint (coupled_source mutated_after_credit)) (0,17)=10 \<and>
    linked.destination_pool_funding (machine_state (core_parent (coupled_core mutated_after_credit))) (0,17)=5 \<and>
    coupled_core mutated_after_credit=coupled_core conservation_credited"
  using conservation_credit_projection conservation_credited_funding_is_five
    conservation_credited_has_actual_effect_evidence
  by (simp add: mutated_after_credit_def source_reverse_guard_removed_def reverse_without_finalization_guard_def
    controlled_record_reversed_def coupling_remote_returns_def coupling_credits_def sample_binding_def
    example_binding_def source_account_of_def Let_def)

theorem mutated_credit_and_refund_break_the_actual_pool_equation:
  "int (boundary_units (controlled_endpoint (coupled_source mutated_after_credit)) (0,17))+
    coupling_remote_pending_mass mutated_after_credit (0,17)+
    linked.destination_pool_funding (machine_state (core_parent (coupled_core mutated_after_credit))) (0,17)=15"
  using conservation_credit_projection conservation_credited_funding_is_five
    conservation_credited_has_actual_effect_evidence
  by (simp add: mutated_after_credit_def source_reverse_guard_removed_def reverse_without_finalization_guard_def
    controlled_record_reversed_def coupling_remote_pending_mass_def coupling_unresolved_remote_def
    coupling_remote_effects_def coupling_remote_returns_def coupling_credits_def sample_binding_def
    example_binding_def source_account_of_def Let_def)

text \<open>The source term is the authoritative endpoint's available allocation.
  A remote debit contributes to pending mass only while it is neither returned
  at that source nor credited by the child. The destination term uses the
  parent's actual root-indexed funding, including lawful descendants. The
  parent accounting mirror is not added as an independent holding.

  This result needs the generated credit-to-current-Finalized invariant in
  addition to the two-view debit/return gap equation. Matching a local debit
  and return journal to source history alone does not establish exclusivity
  between a remote refund and a child credit.\<close>

end
