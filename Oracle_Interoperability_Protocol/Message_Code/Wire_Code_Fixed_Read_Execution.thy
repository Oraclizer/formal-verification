theory Wire_Code_Fixed_Read_Execution
  imports Wire_Code_Read_Service "OIP_Reference_Execution.Reference_Trace_Consumers"
begin

context reference_trace_consumer
begin

definition code_execute_fixed_source_read where
  "code_execute_fixed_source_read verify_wire attest scope token bytes connection before =
    (case code_select_nonreceipt_read_service verify_wire attest scope token bytes of
       None \<Rightarrow> (before,None)
     | Some action \<Rightarrow> serve connection action None before)"

lemma an_unselected_source_read_cannot_enter_the_current_authority:
  assumes "code_select_nonreceipt_read_service verify_wire attest scope token bytes = None"
  shows "code_execute_fixed_source_read verify_wire attest scope token bytes connection before = (before,None)"
  using assms by (simp add: code_execute_fixed_source_read_def)

theorem a_fixed_decoded_source_read_uses_the_actual_current_reference_consumer:
  fixes before :: reference_authority_snapshot
  assumes selected: "code_select_nonreceipt_read_service verify_wire attest scope token bytes = Some action"
  shows "code_execute_fixed_source_read verify_wire attest scope token bytes connection before =
    service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
      authenticated connection action None before"
  using selected
  unfolding code_execute_fixed_source_read_def
  by (simp add: actual_execute reference_service_input.select_convs)

theorem an_executed_source_read_has_the_exact_received_core_and_fixed_current_service:
  fixes before after :: reference_authority_snapshot
  assumes profile: "negotiated_version (boundary_profile scope) = 6"
    and precheck: "code_check_declared_version bytes (boundary_max_frame scope) = None"
    and threshold: "\<not> boundary_threshold_supported scope"
    and replied: "code_execute_fixed_source_read verify_wire attest scope token bytes connection before = (after,Some reply)"
  obtains packet :: wire_packet and action :: "'token retained_service_action"
  where "decode_wire_packet bytes = Some packet" "encode_wire_packet packet = bytes"
    "code_source_nonreceipt_read_service token (packet_core packet) = Some action"
    "current_wire_scope scope (packet_core packet)"
    "serve connection action None before = (after,Some reply)"
proof -
  obtain action where selected: "code_select_nonreceipt_read_service verify_wire attest scope token bytes = Some action"
    and run: "serve connection action None before = (after,Some reply)"
    using replied by (auto simp: code_execute_fixed_source_read_def split: option.splits)
  obtain packet where exact:
    "decode_wire_packet bytes = Some packet" "encode_wire_packet packet = bytes"
    "code_source_nonreceipt_read_service token (packet_core packet) = Some action"
    "current_wire_scope scope (packet_core packet)"
    by (rule the_source_read_service_consumes_only_the_received_canonical_core[OF profile precheck threshold selected])
  show thesis by (rule that[OF exact run])
qed

theorem the_current_identity_policy_can_refuse_the_fixed_read_without_a_cache_or_state_effect:
  fixes before :: reference_authority_snapshot
  assumes selected: "code_select_nonreceipt_read_service verify_wire attest scope token bytes =
      Some (Service_Read token session_auth target request None)"
    and grants: "reference_grants_fit registered (reference_product before) (reference_inputs before)"
    and denied: "\<not> identity_read_allowed directory read_policy authenticate verify_read token session_auth target request
      (identity_source (reopen_retained_product connection (reference_product before)))"
  shows "code_execute_fixed_source_read verify_wire attest scope token bytes connection before =
      (before,Some (Scheduled_Endpoint (Service_Read_Result Identity_Read_Rejected)))"
proof -
  have actual: "serve connection (Service_Read token session_auth target request None) None before =
      (before,Some (Scheduled_Endpoint (Service_Read_Result Identity_Read_Rejected)))"
    unfolding actual_execute reference_service_input.select_convs
    by (rule an_actual_denied_reference_read_preserves_the_snapshot_and_refuses_every_cache[OF grants denied])
  show ?thesis using selected actual by (simp add: code_execute_fixed_source_read_def)
qed

end

text \<open>
  The decoder is fixed to code_source_nonreceipt_read_service; the consumer
  is the existing reference service with its current directory, policy,
  grants and snapshot through reference_trace_consumer.actual_execute.
  There is no arbitrary decode or run argument. This consumes Query1..7
  values at that model boundary. The surrounding fullconsume/publication
  source checks, raw signature/context FFI and actual Rust/reference-model
  execution receipts remain separate M145/M159 obligations.
\<close>

end
