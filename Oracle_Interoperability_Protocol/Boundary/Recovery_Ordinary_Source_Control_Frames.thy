theory Recovery_Ordinary_Source_Control_Frames
  imports "OIP_Product.Recovery_Service"
begin

text \<open>The fields below distinguish client execution from ownership/context maintenance.
  Product request rows and authority logs are allowed to change. These are equations about the
  actual frozen producers, not new frame assumptions of the eventual RFE theorem.\<close>

context source_attestation
begin

lemma ordinary_product_submit_keeps_owner_epoch_sessions_and_local_status:
  "product_owners (product_durable (product_submit verified actor call_id envelope s)) = product_owners (product_durable s)"
  "product_authority_epoch (product_durable (product_submit verified actor call_id envelope s)) = product_authority_epoch (product_durable s)"
  "product_sessions (product_durable (product_submit verified actor call_id envelope s)) = product_sessions (product_durable s)"
  "call_local_status (product_calls (product_submit verified actor call_id envelope s)) = call_local_status (product_calls s)"
proof -
  have begin_status: "call_local_status (finality_calls.begin_client_call call_id (envelope_command envelope) calls) =
      call_local_status calls" for calls
    by (simp add: finality_calls.begin_client_call_def split: option.splits if_splits)
  have dispatch_status: "call_local_status (finality_calls.dispatch_client_call call_id (envelope_command envelope) calls) =
      call_local_status calls" for calls
    by (simp add: finality_calls.dispatch_client_call_def finality_calls.execute_authority_once_def Let_def
      split: option.splits prod.splits if_splits)
  have collect_status: "call_local_status (finality_calls.collect_client_response call_id (envelope_command envelope) calls) =
      call_local_status calls" for calls
    by (simp add: finality_calls.collect_client_response_def split: option.splits prod.splits if_splits)
  have complete_status: "call_local_status (finality_calls.complete_client_call call_id calls) = call_local_status calls" for calls
    by (simp add: finality_calls.complete_client_call_def split: option.splits prod.splits if_splits)
  show "product_owners (product_durable (product_submit verified actor call_id envelope s)) = product_owners (product_durable s)"
    and "product_authority_epoch (product_durable (product_submit verified actor call_id envelope s)) = product_authority_epoch (product_durable s)"
    and "product_sessions (product_durable (product_submit verified actor call_id envelope s)) = product_sessions (product_durable s)"
    by (simp_all add: product_submit_def product_apply_public_def split: if_splits)
  show "call_local_status (product_calls (product_submit verified actor call_id envelope s)) = call_local_status (product_calls s)"
    by (simp add: product_submit_def product_apply_public_def begin_status dispatch_status collect_status complete_status
      split: if_splits)
qed

lemma ordinary_lock_submission_keeps_owner_epoch_sessions_and_local_status:
  "product_owners (product_durable (submit_lock_entry permitted verified entry actor call_id envelope credential s)) = product_owners (product_durable s)"
  "product_authority_epoch (product_durable (submit_lock_entry permitted verified entry actor call_id envelope credential s)) = product_authority_epoch (product_durable s)"
  "product_sessions (product_durable (submit_lock_entry permitted verified entry actor call_id envelope credential s)) = product_sessions (product_durable s)"
  "call_local_status (product_calls (submit_lock_entry permitted verified entry actor call_id envelope credential s)) = call_local_status (product_calls s)"
  by (simp_all add: submit_lock_entry_def ordinary_product_submit_keeps_owner_epoch_sessions_and_local_status split: if_splits)

lemma ordinary_lock_submit_step_keeps_owner_epoch_sessions_and_local_status:
  "product_owners (product_durable (lock_product_step permitted verified maintainers registered
      (Lock_Submit entry actor call_id envelope credential) s)) = product_owners (product_durable s)"
  "product_authority_epoch (product_durable (lock_product_step permitted verified maintainers registered
      (Lock_Submit entry actor call_id envelope credential) s)) = product_authority_epoch (product_durable s)"
  "product_sessions (product_durable (lock_product_step permitted verified maintainers registered
      (Lock_Submit entry actor call_id envelope credential) s)) = product_sessions (product_durable s)"
  "call_local_status (product_calls (lock_product_step permitted verified maintainers registered
      (Lock_Submit entry actor call_id envelope credential) s)) = call_local_status (product_calls s)"
  by (simp_all add: ordinary_lock_submission_keeps_owner_epoch_sessions_and_local_status split: if_splits)

lemma ordinary_new_authoritative_submit_keeps_owner_epoch_sessions_and_local_status:
  "product_owners (product_durable (outcome_source
      (submit_new_authoritative_call permitted maintainers registered entry actor call_id payload outcomes))) =
    product_owners (product_durable (outcome_source outcomes))"
  "product_authority_epoch (product_durable (outcome_source
      (submit_new_authoritative_call permitted maintainers registered entry actor call_id payload outcomes))) =
    product_authority_epoch (product_durable (outcome_source outcomes))"
  "product_sessions (product_durable (outcome_source
      (submit_new_authoritative_call permitted maintainers registered entry actor call_id payload outcomes))) =
    product_sessions (product_durable (outcome_source outcomes))"
  "call_local_status (product_calls (outcome_source
      (submit_new_authoritative_call permitted maintainers registered entry actor call_id payload outcomes))) =
    call_local_status (product_calls (outcome_source outcomes))"
  by (simp_all add: submit_new_authoritative_call_def store_product_result_def Let_def
    ordinary_lock_submit_step_keeps_owner_epoch_sessions_and_local_status
    ordinary_lock_submission_keeps_owner_epoch_sessions_and_local_status
    split: option.splits prod.splits if_splits)

lemma ordinary_authoritative_submit_keeps_owner_epoch_sessions_and_local_status:
  "product_owners (product_durable (outcome_source
      (submit_authoritative_call permitted verified maintainers registered entry actor call_id payload outcomes))) =
    product_owners (product_durable (outcome_source outcomes))"
  "product_authority_epoch (product_durable (outcome_source
      (submit_authoritative_call permitted verified maintainers registered entry actor call_id payload outcomes))) =
    product_authority_epoch (product_durable (outcome_source outcomes))"
  "product_sessions (product_durable (outcome_source
      (submit_authoritative_call permitted verified maintainers registered entry actor call_id payload outcomes))) =
    product_sessions (product_durable (outcome_source outcomes))"
  "call_local_status (product_calls (outcome_source
      (submit_authoritative_call permitted verified maintainers registered entry actor call_id payload outcomes))) =
    call_local_status (product_calls (outcome_source outcomes))"
  by (simp_all add: submit_authoritative_call_def
    ordinary_new_authoritative_submit_keeps_owner_epoch_sessions_and_local_status split: if_splits)

lemma ordinary_origin_submit_keeps_owner_epoch_sessions_and_local_status:
  "product_owners (product_durable (outcome_source (origin_outcomes
      (submit_origin_call permitted verified maintainers registered entry actor call_id payload origins)))) =
    product_owners (product_durable (outcome_source (origin_outcomes origins)))"
  "product_authority_epoch (product_durable (outcome_source (origin_outcomes
      (submit_origin_call permitted verified maintainers registered entry actor call_id payload origins)))) =
    product_authority_epoch (product_durable (outcome_source (origin_outcomes origins)))"
  "product_sessions (product_durable (outcome_source (origin_outcomes
      (submit_origin_call permitted verified maintainers registered entry actor call_id payload origins)))) =
    product_sessions (product_durable (outcome_source (origin_outcomes origins)))"
  "call_local_status (product_calls (outcome_source (origin_outcomes
      (submit_origin_call permitted verified maintainers registered entry actor call_id payload origins)))) =
    call_local_status (product_calls (outcome_source (origin_outcomes origins)))"
  by (simp_all add: submit_origin_call_def Let_def origin_metadata_retention_keeps_the_authority_result
    ordinary_authoritative_submit_keeps_owner_epoch_sessions_and_local_status
    split: option.splits prod.splits if_splits)

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.ordinary_product_submit_keeps_owner_epoch_sessions_and_local_status
      source_attestation.ordinary_lock_submission_keeps_owner_epoch_sessions_and_local_status
      source_attestation.ordinary_lock_submit_step_keeps_owner_epoch_sessions_and_local_status
      source_attestation.ordinary_new_authoritative_submit_keeps_owner_epoch_sessions_and_local_status
      source_attestation.ordinary_authoritative_submit_keeps_owner_epoch_sessions_and_local_status
      source_attestation.ordinary_origin_submit_keeps_owner_epoch_sessions_and_local_status})
  then () else error "Unexpected oracle in ordinary source control frames"
\<close>

end
