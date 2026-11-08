theory Protected_Source_Debit
  imports Frozen_Spend
begin

context source_attestation
begin

theorem protected_source_debit_does_not_move_funds:
  assumes op: "binding_operation (request_binding r) = Destination_Credit"
    and actual: "get_reg_state (lock_metadata (current_lock_view s endpoint))
      (fst (binding_key (request_binding r))) (binding_asset (request_binding r)) = Some policy"
    and protected: "protected_freeze_mode policy"
  shows "let result = invoke_protocol endpoint (core_epoch s) index (Source_Intent r generation versions) s
    in machine_state (core_parent (fst result)) = machine_state (core_parent s)"
proof -
  have denied: "\<not> metadata_permission (current_lock_view s endpoint) r (fst (binding_key (request_binding r)))"
    using op actual protected_mode_closes_ordinary_spending[OF protected]
    by (simp add: metadata_permission_def)
  show ?thesis using denied
    by (simp add: invoke_protocol_def execute_source_effect_def lift_protocol_result_def record_observation_def
      Let_def split: if_splits)
qed

end

end
