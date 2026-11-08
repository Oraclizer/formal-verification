theory Recovery_Checked_Source_Control_Frames
  imports Recovery_Ordinary_Source_Control_Frames
begin

lemma checked_product_read_selector_is_the_read_world:
  "legal_reads (governed_legal (regulated_orders s)) = regulated_read_world s"
  by (simp add: regulated_read_world_def)

lemma checked_legal_outcome_source_is_the_observed_source:
  "outcome_source (legal_underlying_outcomes legal) = observed_product_source (read_authority (legal_reads legal))"
  by (simp add: legal_underlying_outcomes_def observed_product_source_def)

lemma checked_current_outcome_source_is_the_observed_source:
  "outcome_source (current_product_outcomes s) = observed_product_source (read_authority (regulated_read_world s))"
  by (simp add: current_product_outcomes_def checked_legal_outcome_source_is_the_observed_source regulated_read_world_def)

lemma checked_read_replacement_supplies_its_exact_source:
  "observed_product_source (read_authority (regulated_read_world (replace_regulated_reads reads s))) =
    observed_product_source (read_authority reads)"
  by (simp add: regulated_read_world_def replace_regulated_reads_def)

context source_attestation
begin

lemma checked_execution_keeps_owner_epoch_sessions_and_local_status:
  assumes produced: "after = fst (execute_at_checked_cut permitted verified maintainers registered verified_ack
    entry actor expected call_id payload reads)"
  shows "product_owners (product_durable (observed_product_source (read_authority after))) =
      product_owners (product_durable (observed_product_source (read_authority reads)))"
    and "product_authority_epoch (product_durable (observed_product_source (read_authority after))) =
      product_authority_epoch (product_durable (observed_product_source (read_authority reads)))"
    and "product_sessions (product_durable (observed_product_source (read_authority after))) =
      product_sessions (product_durable (observed_product_source (read_authority reads)))"
    and "call_local_status (product_calls (observed_product_source (read_authority after))) =
      call_local_status (product_calls (observed_product_source (read_authority reads)))"
  using produced
  by (simp_all add: execute_at_checked_cut_def observed_product_source_def Let_def
    ordinary_origin_submit_keeps_owner_epoch_sessions_and_local_status split: if_splits)

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms checked_product_read_selector_is_the_read_world
      checked_legal_outcome_source_is_the_observed_source
      checked_current_outcome_source_is_the_observed_source checked_read_replacement_supplies_its_exact_source
      source_attestation.checked_execution_keeps_owner_epoch_sessions_and_local_status})
  then () else error "Unexpected oracle in shared checked consumer source frames"
\<close>

end
