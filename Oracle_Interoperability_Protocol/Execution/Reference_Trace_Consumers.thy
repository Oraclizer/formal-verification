theory Reference_Trace_Consumers
  imports "OIP_Reference_Profile.Reference_Entry_Closure" "OIP_Reference_Profile.Reference_Parallel_Consumption"
    "OIP_Reference_Profile.Reference_Queue_Consumption" "OIP_Reference_Profile.Reference_Handover_Consumption"
begin

locale reference_trace_consumer = source_attestation +
  fixes execute :: "'token reference_service_input \<Rightarrow> reference_authority_snapshot \<Rightarrow> reference_authority_snapshot \<times> scheduled_service_reply option"
    and directory policy read_policy authenticate verify verify_read endorse approve
    and legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack authenticated
  assumes actual_execute: "execute = (\<lambda>entry snapshot.
    service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
      authenticated (reference_connection entry) (reference_service_action entry)
      (reference_supplied_grants entry) snapshot)"
begin

abbreviation serve where
  "serve connection action supplied \<equiv> execute \<lparr>reference_connection = connection,
     reference_service_action = action, reference_supplied_grants = supplied\<rparr>"

lemma every_reference_prefix_keeps_the_central_authority_contract:
  assumes "reference_service_contract registered genesis initial"
  shows "reference_service_contract registered genesis (run_reference_word execute prefix initial)"
  unfolding actual_execute by (rule an_actual_reference_word_preserves_its_authority_contract[OF assms])

lemma a_reference_prefix_consumes_the_current_grants:
  assumes "reference_service_contract registered genesis initial"
  shows "reference_grants_fit registered (reference_product (run_reference_word execute prefix initial))
     (reference_inputs (run_reference_word execute prefix initial))"
  using every_reference_prefix_keeps_the_central_authority_contract[OF assms] by (simp add: reference_service_contract_def)

theorem a_read_denied_by_the_current_identity_after_any_prefix_cannot_use_a_cache:
  fixes before prefix initial
  defines "before \<equiv> run_reference_word execute prefix initial"
  assumes start: "reference_service_contract registered genesis initial"
    and denied: "\<not> identity_read_allowed directory read_policy authenticate verify_read token proof target request
      (identity_source (reopen_retained_product connection (reference_product before)))"
  shows "serve connection (Service_Read token proof target request cache) supplied before =
      (before, Some (Scheduled_Endpoint (Service_Read_Result Identity_Read_Rejected)))"
proof -
  have grants: "reference_grants_fit registered (reference_product before) (reference_inputs before)"
    unfolding before_def by (rule a_reference_prefix_consumes_the_current_grants[OF start])
  show ?thesis unfolding actual_execute reference_service_input.select_convs
    by (rule an_actual_denied_reference_read_preserves_the_snapshot_and_refuses_every_cache[OF grants denied])
qed

lemma a_reference_word_can_be_run_in_two_parts:
  "run_reference_word execute (prefix @ suffix) initial =
    run_reference_word execute suffix (run_reference_word execute prefix initial)"
  by (induction prefix arbitrary: initial) simp_all

theorem after_any_reference_prefix_an_compatible_exchange_keeps_labeled_results_and_the_rest_of_the_trace:
  fixes before first_entry second_entry prefix initial connection first second
  defines "before \<equiv> run_reference_word execute prefix initial"
    and "first_entry \<equiv> \<lparr>reference_connection = connection, reference_service_action = first, reference_supplied_grants = None\<rparr>"
    and "second_entry \<equiv> \<lparr>reference_connection = connection, reference_service_action = second, reference_supplied_grants = None\<rparr>"
  assumes start: "reference_service_contract registered genesis initial"
    and compatible: "compatible_service_actions first second
       (service_settlement (reopen_retained_product connection (reference_product before)))"
  shows "service_ordered_pair (\<lambda>action. serve connection action None) first second before =
      service_exchanged_pair (\<lambda>action. serve connection action None) first second before"
    "run_reference_word execute (prefix @ first_entry # second_entry # suffix) initial =
     run_reference_word execute (prefix @ second_entry # first_entry # suffix) initial"
proof -
  have grants: "reference_grants_fit registered (reference_product before) (reference_inputs before)"
    unfolding before_def by (rule a_reference_prefix_consumes_the_current_grants[OF start])
  show pair: "service_ordered_pair (\<lambda>action. serve connection action None) first second before =
      service_exchanged_pair (\<lambda>action. serve connection action None) first second before"
    unfolding actual_execute reference_service_input.select_convs
    by (rule compatible_actions_exchange_in_the_actual_reference_service[OF grants compatible, unfolded Let_def])
  have state: "fst (serve connection second None (fst (serve connection first None before))) =
      fst (serve connection first None (fst (serve connection second None before)))"
    using arg_cong[OF pair, where f=fst] by (simp add: service_ordered_pair_def service_exchanged_pair_def Let_def)
  show "run_reference_word execute (prefix @ first_entry # second_entry # suffix) initial =
     run_reference_word execute (prefix @ second_entry # first_entry # suffix) initial"
    using state by (simp add: a_reference_word_can_be_run_in_two_parts first_entry_def second_entry_def before_def)
qed

theorem an_ack_after_any_reference_prefix_can_change_only_its_exact_queue_and_keeps_primary_decisions:
  fixes before prefix initial
  defines "before \<equiv> run_reference_word execute prefix initial"
  assumes start: "reference_service_contract registered genesis initial"
  shows "let step = serve connection (Service_Maintenance (Exact_Acknowledge ack)) None before;
        expected = step_settlement_slot verified_ack (Slot_Ack ack) (retained_secondary (reference_product before));
        retained = reference_product (fst step)
    in retained = (reference_product before)\<lparr>retained_secondary := fst expected\<rparr> \<and>
       retained_decisions retained = retained_decisions (reference_product before) \<and>
       retained_source retained = retained_source (reference_product before) \<and>
       snd step = Some (Scheduled_Settlement (snd expected))"
proof -
  have grants: "reference_grants_fit registered (reference_product before) (reference_inputs before)"
    unfolding before_def by (rule a_reference_prefix_consumes_the_current_grants[OF start])
  have slot: "classify_service_action (Service_Maintenance (Exact_Acknowledge ack))
        (service_settlement (reopen_retained_product connection (reference_product before))) = Service_Slot (Slot_Ack ack)"
    by simp
  then have nonserial: "classify_service_action (Service_Maintenance (Exact_Acknowledge ack))
        (service_settlement (reopen_retained_product connection (reference_product before))) \<noteq> Service_Serial"
    by simp
  let ?action = "Service_Maintenance (Exact_Acknowledge ack)"
  let ?scheduled = "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted (reference_permitted_at (reference_inputs before))
    verified maintainers registered verified_ack connection ?action (reference_product before)"
  let ?expected = "step_settlement_slot verified_ack (Slot_Ack ack) (retained_secondary (reference_product before))"
  have actual: "serve connection ?action None before =
     (before\<lparr>reference_product := fst ?scheduled\<rparr>, Some (snd ?scheduled))"
    unfolding actual_execute reference_service_input.select_convs
    by (rule a_nonserial_reference_step_keeps_the_live_grants[OF grants nonserial, unfolded Let_def])
  have effect: "?scheduled = ((reference_product before)\<lparr>retained_secondary := fst ?expected\<rparr>,
         Scheduled_Settlement (snd ?expected))"
    by (rule classified_settlement_action_updates_only_its_real_slot[OF slot, unfolded Let_def])
  show ?thesis using actual effect by (simp add: Let_def)
qed

theorem a_handover_after_any_reference_prefix_keeps_pending_and_refuses_the_immediate_old_session_read:
  fixes before prefix initial
  defines "before \<equiv> run_reference_word execute prefix initial"
  assumes start: "reference_service_contract registered genesis initial"
    and changed: "serve connection (Service_Handover owner_token successor_token maintainer proposal) supplied before =
         (after, Some (Scheduled_Endpoint (Service_Handover_Result True)))"
    and old: "proof_session proof = transfer_old_session proposal"
  shows "core_parent (retained_core (retained_source (reference_product after))) =
        core_parent (retained_core (retained_source (reference_product before)))"
    "product_owners (retained_authority (retained_source (reference_product after))) (transfer_asset proposal) =
        Some (transfer_successor proposal)"
    "serve next_connection (Service_Read old_token proof target request cache) next_supplied after =
        (after, Some (Scheduled_Endpoint (Service_Read_Result Identity_Read_Rejected)))"
proof -
  note transfer = the_actual_reference_handover_updates_owner_sessions_and_grants_at_one_epoch
    [OF changed[unfolded actual_execute reference_service_input.select_convs]]
  show "core_parent (retained_core (retained_source (reference_product after))) =
        core_parent (retained_core (retained_source (reference_product before)))" by (rule transfer(5))
  show "product_owners (retained_authority (retained_source (reference_product after))) (transfer_asset proposal) =
        Some (transfer_successor proposal)" by (rule transfer(1))
  have contract: "reference_service_contract registered genesis before"
    unfolding before_def by (rule every_reference_prefix_keeps_the_central_authority_contract[OF start])
  have after_contract: "reference_service_contract registered genesis after"
    by (rule an_actual_reference_service_step_preserves_its_authority_contract
        [OF contract changed[unfolded actual_execute reference_service_input.select_convs]])
  then have grants: "reference_grants_fit registered (reference_product after) (reference_inputs after)"
    by (simp add: reference_service_contract_def)
  have denied: "\<not> identity_read_allowed directory read_policy authenticate verify_read old_token proof target request
        (identity_source (reopen_retained_product next_connection (reference_product after)))"
    using old transfer(2) by (simp add: identity_read_allowed_def active_identity_def recovery_projection_supplies_the_exact_source
      reopen_retained_source_def)
  show "serve next_connection (Service_Read old_token proof target request cache) next_supplied after =
        (after, Some (Scheduled_Endpoint (Service_Read_Result Identity_Read_Rejected)))"
    unfolding actual_execute reference_service_input.select_convs
    by (rule an_actual_denied_reference_read_preserves_the_snapshot_and_refuses_every_cache[OF grants denied])
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms reference_trace_consumer.a_read_denied_by_the_current_identity_after_any_prefix_cannot_use_a_cache
    reference_trace_consumer.after_any_reference_prefix_an_compatible_exchange_keeps_labeled_results_and_the_rest_of_the_trace
    reference_trace_consumer.an_ack_after_any_reference_prefix_can_change_only_its_exact_queue_and_keeps_primary_decisions
    reference_trace_consumer.a_handover_after_any_reference_prefix_keeps_pending_and_refuses_the_immediate_old_session_read})
  then () else error "Unexpected oracle in central trace consumers"
\<close>

end
