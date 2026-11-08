theory Reference_Settlement_Code
  imports "Native_Original_Settlement" "OIP_Reference_Profile.Reference_Central_Trace"
begin

definition reference_origin_table where
  "reference_origin_table connection snapshot =
    settlement_primary (service_settlement (reopen_retained_product connection (reference_product snapshot)))"

theorem the_native_duplicate_credit_returns_the_original_reference_of_the_current_product:
  assumes selected: "released_credit_reference (reference_permitted_at (reference_inputs snapshot))
      verified registered entry actor call_id payload (reference_origin_table connection snapshot) = Some (binding, index)"
    and rows: "list_all2 (\<lambda>row step. exact_applied_credit binding row =
      inserts_native_settlement (binding_key binding) step)
      (call_authority_log (product_calls (outcome_source (origin_outcomes (reference_origin_table connection snapshot))))) steps"
    and exact_binding: "duplicate_binding_value input = binding"
    and slot: "duplicate_origins_value input (binding_key binding) =
      Some (native_slot_after_settlement_replay binding steps revision prior_slot)"
    and decision: "slot_decision_value prior_slot = Some (True, decision_commit)"
    and command: "duplicate_command_value input = Native_Credit reference"
    and evidence: "duplicate_evidence_value input reference = Some (binding, True, reference)"
  shows "duplicate_return (native_duplicate_value_run input 20 duplicate_initial_registers) =
      Some (Native_Settlement True (native_revision_at_log_position revision steps index))"
  by (rule native_duplicate_value_uses_the_revision_of_the_product_original_credit[OF
      selected rows exact_binding slot decision command evidence])

theorem the_corresponding_model_receipt_cannot_change_its_primary_decision:
  assumes selected: "released_credit_reference (reference_permitted_at (reference_inputs snapshot))
      verified registered entry actor call_id payload (reference_origin_table connection snapshot) = Some (binding, index)"
  shows "let before = reference_origin_table connection snapshot;
       after = fst (record_released_credit_receipt (reference_permitted_at (reference_inputs snapshot))
         verified registered entry actor call_id payload before)
    in origin_decisions after = origin_decisions before \<and>
       outcome_source (origin_outcomes after) = outcome_source (origin_outcomes before)"
  using released_credit_receipt_preserves_authority_and_old_results(2,3)[OF selected]
  by (simp add: Let_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_native_duplicate_credit_returns_the_original_reference_of_the_current_product
      the_corresponding_model_receipt_cannot_change_its_primary_decision})
  then () else error "Unexpected oracle in native duplicate settlement correspondence"
\<close>

end
