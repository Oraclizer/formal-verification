theory Freeze_Spend_Examples
  imports "../Frozen_Spend" "Evidence_Atomic_Binding.Regulatory_Finality_Scenarios"
begin

lemma published_freeze_is_the_value_of_the_actual_regulatory_read:
  "stored_query (Regulatory_State 2 20) (capture_snapshot regulation_published) = Regulatory_Value (Some FROZEN)"
  using actual_freeze_preserves_the_earlier_financial_effects
  by (simp add: capture_snapshot_def)

lemmas actual_ordinary_rejection_after_freeze = ordinary_descendant_is_rejected_after_actual_freeze

lemma the_same_frozen_root_meets_all_lawful_enforcement_preconditions:
  "lawful_enforcement_preconditions regulation_denied 2 0
    (regulation_spend_request (Enforcement_Transfer_Effect Legal_Recover)) regulation_money_binding 3 4 1 Legal_Recover"
  by (simp add: lawful_enforcement_preconditions_def regulation_denied_state regulation_denied_current_context
    regulation_published_shape regulation_frozen_shape regulation_recorded_shape regulation_root_ready_core_fields
    regulation_root_ready_financial_state regulation_root_record_def record_reference_def
    regulation_spend_definitions regulation_payload_definitions example_snapshot_def descendant_binding_def Let_def)

lemma the_lawful_transfer_in_the_frozen_state_consumes_its_confirmed_root:
  "let result = regulation_case.invoke_protocol 2 (core_epoch regulation_denied) 0 regulation_enforcement_intent regulation_denied
    in snd result = Protocol_Response Descendant_Executed \<and>
       (\<exists>event. lawful_descendants (machine_state (core_parent (fst result))) =
          lawful_descendants (machine_state (core_parent regulation_denied)) @ [event] \<and>
          lineage_root event = regulation_money_binding \<and> lineage_from event = 3 \<and> lineage_to event = 4 \<and>
          lineage_amount event = 1 \<and>
          lineage_caller event = request_caller (regulation_spend_request (Enforcement_Transfer_Effect Legal_Recover)))"
  unfolding regulation_enforcement_intent_def
  by (rule source_attestation.lawful_enforcement_consumes_the_exact_confirmed_root
      [OF regulation_case.source_attestation_axioms the_same_frozen_root_meets_all_lawful_enforcement_preconditions])

lemma using_the_old_configured_policy_would_execute_the_frozen_ordinary_spend:
  "snd (execute_descendant (core_contexts regulation_published 2)
    (regulation_spend_request Ordinary_Transfer_Effect) regulation_money_binding 3 4 1 (core_parent regulation_published)) =
    Descendant_Executed"
  by (simp add: regulation_published_shape regulation_frozen_shape regulation_recorded_shape regulation_root_ready_core_fields
    regulation_root_ready_financial_state regulation_context_def regulation_spend_definitions regulation_payload_definitions
    example_snapshot_def Let_def)

context source_attestation
begin

lemma applying_a_regulatory_effect_keeps_the_current_reservation_machine:
  "core_parent (fst (invoke_regulatory endpoint epoch index request s)) = core_parent s"
  by (simp add: invoke_regulatory_def split: option.splits if_splits)

end

end
