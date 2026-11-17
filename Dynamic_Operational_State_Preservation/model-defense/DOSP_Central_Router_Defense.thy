theory DOSP_Central_Router_Defense
  imports DOSP_Classified_Entry
begin

definition degrees_for_initiator where
  "degrees_for_initiator policy origin receiver = {degree. legal_at policy degree (Commit_From origin receiver 0)}"

lemma an_initiators_degree_family_has_the_exact_route_scope:
  "degrees_for_initiator policy origin receiver =
    (if origin \<in> allowed_sources policy \<and> origin \<noteq> receiver \<and> {origin,receiver} \<subseteq> domain_set policy
     then {Coupled,Atomic} else {})"
proof (rule set_eqI)
  fix degree
  show "degree \<in> degrees_for_initiator policy origin receiver \<longleftrightarrow>
    degree \<in> (if origin \<in> allowed_sources policy \<and> origin \<noteq> receiver \<and> {origin,receiver} \<subseteq> domain_set policy
      then {Coupled,Atomic} else {})"
    by (cases degree) (auto simp: degrees_for_initiator_def)
qed

lemma the_two_origins_have_their_own_legal_committing_degrees:
  "degrees_for_initiator two_origin_policy 1 2 = {Coupled,Atomic}"
  "degrees_for_initiator two_origin_policy 2 1 = {Coupled,Atomic}"
  "degrees_for_initiator two_origin_policy 0 2 = {}"
  by (simp_all add: an_initiators_degree_family_has_the_exact_route_scope two_origin_policy_def)

context integrated_dosp_authority
begin

theorem a_joint_native_credit_gives_the_same_routed_update_when_participants_are_kept:
  assumes accepted: "joint_credit_step mode versions confirmed evidence p request index route r
      (Cycle_Result (transition_result.Accepted Binding_Committed)) q"
    and participants: "participants (request_flow request) \<subseteq> domains"
  shows "route_and_execute (authority_registry (source_consensus p)) (restrict_policy domains flow_policy)
      (fst (cycle_session_id request)) (cycle_ticket request) True
      (forget_outside domains (binding_state (lifecycle_cutover (source_lifecycle p)))) (request_flow request) =
    (forget_outside domains (binding_state (lifecycle_cutover (source_lifecycle q))),
      transition_result.Accepted (Committed_Value (cycle_value request)))"
proof -
  let ?s = "(source_lifecycle p)\<lparr>lifecycle_clock := consensus_now (source_consensus p)\<rparr>"
  let ?registry = "authority_registry (source_consensus p)"
  let ?t = "lifecycle_cutover (source_lifecycle q)"
  let ?path = "chosen_path (ticket_metadata (cycle_ticket request))"
  have candidate: "joint_credit_candidate mode versions confirmed evidence p request index route r
      (source_lifecycle q) (source_consensus q)"
    using a_confirmed_joint_credit_requires_both_linked_effects[OF accepted] by blast
  have life: "lifecycle_step flow_policy promotion_authorizations versions confirmed evidence
      (promotion_locks_clear flow_policy (current_operational (source_consensus p))) ?s
      (Commit_Cycle True) (Cycle_Result (transition_result.Accepted Binding_Committed)) (source_lifecycle q)"
    and registry: "lifecycle_registry ?s = ?registry"
    using candidate by (auto simp: joint_credit_candidate_def Let_def)
  obtain row where permit: "binding_is_current flow_policy ?s request"
    and metered: "metered_attempt flow_policy promotion_authorizations versions evidence ?s request True
      (transition_result.Accepted Binding_Committed) ?t = Some row"
  proof -
    have verified: "lifecycle_phase ?s = Verified_Cycle request"
      using candidate by (simp add: joint_credit_candidate_def Let_def)
    from life verified obtain row where "binding_is_current flow_policy ?s request"
       "metered_attempt flow_policy promotion_authorizations versions evidence ?s request True
         (transition_result.Accepted Binding_Committed) ?t = Some row"
      by (cases rule: lifecycle_step.cases) auto
    then show thesis by (rule that)
  qed
  have action: "cutover_step flow_policy promotion_authorizations (lifecycle_cutover ?s) (request_commit request True)
      (transition_result.Accepted Binding_Committed) ?t"
    using metered by (auto simp: metered_attempt_def observed_commit_charge_def request_commit_def Let_def
      split: option.splits if_splits)
  have raw: "flow_step flow_policy ?path True (binding_state (lifecycle_cutover (source_lifecycle p)))
      (request_flow request) (transition_result.Accepted (Committed_Value (cycle_value request))) (binding_state ?t)"
    using action unfolding request_commit_def request_flow_def
    by (cases rule: cutover_step.cases) auto
  have admitted_ticket: "ticket_authorizes (lifecycle_registry ?s) flow_policy (fst (cycle_session_id request))
      (cycle_ticket request) (request_flow request)"
    using permit unfolding binding_is_current_def by blast
  have current: "ticket_authorizes ?registry flow_policy (fst (cycle_session_id request)) (cycle_ticket request) (request_flow request)"
    using admitted_ticket by (simp only: registry)
  have normal: "route_and_execute ?registry flow_policy (fst (cycle_session_id request)) (cycle_ticket request) True
      (binding_state (lifecycle_cutover (source_lifecycle p))) (request_flow request) =
    (binding_state ?t, transition_result.Accepted (Committed_Value (cycle_value request)))"
    using current raw by (simp add: route_and_execute_def flow_step_def)
  show ?thesis
    by (simp only: routed_flow_naturality_uses_the_same_ticket_and_result[OF participants] normal map_prod_simp id_apply)
qed

lemma a_joint_credit_consumes_the_degree_at_its_actual_initiator:
  assumes accepted: "joint_credit_step mode versions confirmed evidence p request index route r
    (Cycle_Result (transition_result.Accepted Binding_Committed)) q"
  shows "required_level (ticket_metadata (cycle_ticket request)) \<in>
    degrees_for_initiator flow_policy (fst (binding_key (request_binding r))) (binding_destination (request_binding r))"
proof -
  obtain row where recorded: "run_registered_meter (cycle_ticket request) (cycle_session_id request) index route r (source_consensus p) =
    Some (source_consensus q, Credit_Result (Some (Credit_Metered row)))"
    using a_confirmed_joint_credit_requires_both_linked_effects[OF accepted]
    by (auto simp: joint_credit_candidate_def Let_def)
  have allowed: "ticket_authorizes (authority_registry (source_consensus p)) flow_policy (binding_asset (request_binding r))
    (cycle_ticket request) (transfer_commit (request_binding r))"
    using recorded by (auto simp: run_registered_meter_def split: if_splits)
  then show ?thesis by (auto simp: ticket_authorizes_def degrees_for_initiator_def)
qed

end

end
