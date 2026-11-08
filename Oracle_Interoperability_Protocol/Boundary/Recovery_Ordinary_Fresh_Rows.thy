theory Recovery_Ordinary_Fresh_Rows
  imports "OIP_Product.Recovery_Service"
begin

text \<open>Exact outcome-row producers used by fresh ordinary execution. These lemmas preserve
  the frozen producers and cover refusal rows as well as successful replies; they do not assume
  that a changing fresh execution has already completed its result.\<close>

context source_attestation
begin

lemma ordinary_new_submit_stutters_or_stores_one_exact_result:
  "submit_new_authoritative_call permitted maintainers registered entry actor call_id payload outcomes = outcomes \<or>
    (\<exists>source reply. submit_new_authoritative_call permitted maintainers registered entry actor call_id payload outcomes =
      store_product_result call_id payload reply source outcomes)"
  by (auto simp: submit_new_authoritative_call_def Let_def split: option.splits prod.splits if_splits)

lemma ordinary_submit_stutters_or_stores_one_exact_result:
  "submit_authoritative_call permitted verified maintainers registered entry actor call_id payload outcomes = outcomes \<or>
    (\<exists>source reply. submit_authoritative_call permitted verified maintainers registered entry actor call_id payload outcomes =
      store_product_result call_id payload reply source outcomes)"
  by (cases "result_access_bound verified actor call_id payload outcomes \<and> outcome_entries outcomes call_id = None")
    (simp_all add: submit_authoritative_call_def ordinary_new_submit_stutters_or_stores_one_exact_result)

lemma ordinary_origin_submission_stutters_or_inserts_the_exact_request_row:
  assumes fresh: "outcome_entries (origin_outcomes origins) call_id = None"
  shows "submit_origin_call permitted verified maintainers registered entry actor call_id payload origins = origins \<or>
    (\<exists>reply. outcome_entries (origin_outcomes
      (submit_origin_call permitted verified maintainers registered entry actor call_id payload origins)) =
      (outcome_entries (origin_outcomes origins))
        (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>))"
proof -
  let ?old = "origin_outcomes origins"
  let ?submitted = "submit_authoritative_call
    (\<lambda>route who command. permitted route who command \<and>
      origin_command_allowed origins (payload_envelope payload) (payload_origin_epoch payload) command)
    verified maintainers registered entry actor call_id payload ?old"
  have alternatives: "?submitted = ?old \<or>
      (\<exists>source reply. ?submitted = store_product_result call_id payload reply source ?old)"
    by (rule ordinary_submit_stutters_or_stores_one_exact_result)
  from alternatives show ?thesis
  proof (elim disjE)
    assume stutter: "?submitted = ?old"
    show ?thesis
      by (rule disjI1) (simp add: submit_origin_call_def Let_def stutter fresh)
  next
    assume stored: "\<exists>source reply. ?submitted = store_product_result call_id payload reply source ?old"
    then obtain changed_source reply where actual:
      "?submitted = store_product_result call_id payload reply changed_source ?old" by blast
    show ?thesis
    proof (rule disjI2, rule exI[of _ reply])
      show "outcome_entries (origin_outcomes
          (submit_origin_call permitted verified maintainers registered entry actor call_id payload origins)) =
        (outcome_entries (origin_outcomes origins))
          (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>)"
        using fresh actual
        by (simp add: submit_origin_call_def Let_def store_product_result_def
          origin_metadata_retention_keeps_the_authority_result split: option.splits prod.splits if_splits)
    qed
  qed
qed

end

lemma ordinary_released_credit_recording_stutters_or_inserts_the_exact_request_row:
  "fst (record_released_credit_receipt permitted verified registered entry actor call_id payload origins) = origins \<or>
    (\<exists>reply. outcome_entries (origin_outcomes
      (fst (record_released_credit_receipt permitted verified registered entry actor call_id payload origins))) =
      (outcome_entries (origin_outcomes origins))
        (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>))"
  by (auto simp: record_released_credit_receipt_def store_product_result_def Let_def
    split: option.splits prod.splits)

lemma ordinary_a_fresh_result_changes_the_outcome_map:
  assumes fresh: "before call_id = None"
    and inserted: "after = before (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>)"
  shows "after \<noteq> before"
proof
  assume same: "after = before"
  have "after call_id = Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>"
    using inserted by simp
  then show False using same fresh by simp
qed

lemma ordinary_completion_keeps_the_entire_outcome_map:
  "outcome_entries (fst (complete_authoritative_result verified actor call_id payload outcomes)) = outcome_entries outcomes"
  by (simp add: complete_authoritative_result_def split: option.splits if_splits)

text \<open>Fresh/prior Execute separation must still lift these row facts through checked
  execution, regulated replacement and finishing, then derive the actual changing cases.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.ordinary_new_submit_stutters_or_stores_one_exact_result
      source_attestation.ordinary_submit_stutters_or_stores_one_exact_result
      source_attestation.ordinary_origin_submission_stutters_or_inserts_the_exact_request_row
      ordinary_released_credit_recording_stutters_or_inserts_the_exact_request_row
      ordinary_a_fresh_result_changes_the_outcome_map ordinary_completion_keeps_the_entire_outcome_map})
  then () else error "Unexpected oracle in ordinary fresh result-row producers"
\<close>

end
