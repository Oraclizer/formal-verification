theory Rollback_Legacy
  imports
    REOS_Rollback.Rollback_Contracts
    Regulatory_Action_Composition.Regulatory_Action_Composition
    Cross_Domain_State_Preservation.DQuencer_Instance
begin

section \<open>Previously verified terminal and selection guarantees\<close>

definition legacy_terminal_view :: "rollback_state \<Rightarrow> nat \<Rightarrow> reg_state"
where
  "legacy_terminal_view s i =
    (if terminal_records s i = None then ACTIVE else CONFISCATED)"

text \<open>The diagram compares the terminal observation of the two models.
  A preterminal state requires a richer action and state correspondence.\<close>

theorem terminal_observation_agrees_with_rac:
  assumes trace: "finite_trace rollback_step carrier s events t"
    and settled: "terminal_records s i = Some p"
  shows "legacy_terminal_view t i = run_word actions (legacy_terminal_view s i)"
  using finalized_effect_survives_trace[OF trace settled] settled confiscated_word_absorbing[of actions]
  by (simp add: legacy_terminal_view_def)

context dquencer_priority_concrete
begin

text \<open>The priority theorem identifies the selected message under its own
  well-formedness conditions. The later authority check still uses the
  rollback intent and ratification, independent of the priority key.\<close>

theorem selected_request_still_requires_rollback_authority:
  fixes intent_of :: "dq_message \<Rightarrow> rollback_intent"
  assumes finite: "finite msg_set"
    and selected: "dq_priority.select_highest msg_priority_keys = Some k"
    and wide: "request_scope (intent_of (recover_msg k)) = Wide"
    and no_ratification: "\<not> matches_certificate s (intent_of (recover_msg k)) Governance_Ratification Governance approval"
  shows "recover_msg k \<in> msg_set"
    and "\<not> rollback_step s (Execute_Rollback (intent_of (recover_msg k)) approval role_proof)
      (Operational_Trace_Contracts.Accepted i) t"
  using dq_select_highest_message[OF finite selected] broad_rollback_requires_ratification[OF wide no_ratification]
  by blast+

end

end
