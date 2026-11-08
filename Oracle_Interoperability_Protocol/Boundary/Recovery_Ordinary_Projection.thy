theory Recovery_Ordinary_Projection
  imports "OIP_Product.Recovery_Service"
begin

text \<open>Read-only consequences of the frozen retained projection. Equal live status is an
  explicit helper input, not a new premise of the target product RFE. The scheduler reopens Up;
  its changing Execute branches must supply the corresponding status facts.\<close>

lemma ordinary_identity_source_is_the_outcome_source:
  "identity_source s = outcome_source (current_product_outcomes s)"
  by (simp add: identity_source_def observed_product_source_def current_product_outcomes_def
    legal_underlying_outcomes_def regulated_read_world_def)

lemma ordinary_capture_keeps_the_exact_source:
  "capture_retained_source (outcome_source (current_product_outcomes s)) =
    retained_source (capture_retained_product s)"
  by (simp add: capture_retained_product_def current_product_outcomes_def
    legal_underlying_outcomes_def Let_def)

lemma ordinary_capture_keeps_the_source_durable:
  "product_durable (outcome_source (current_product_outcomes s)) =
    retained_authority (retained_source (capture_retained_product s))"
  using arg_cong[OF ordinary_capture_keeps_the_exact_source[of s], of retained_authority]
  by (simp add: capture_retained_source_def Let_def)

lemma ordinary_capture_keeps_the_source_core:
  "call_authority_state (product_calls (outcome_source (current_product_outcomes s))) =
    retained_core (retained_source (capture_retained_product s))"
  using arg_cong[OF ordinary_capture_keeps_the_exact_source[of s], of retained_core]
  by (simp add: capture_retained_source_def Let_def)

lemma ordinary_capture_keeps_the_source_log:
  "call_authority_log (product_calls (outcome_source (current_product_outcomes s))) =
    retained_log (retained_source (capture_retained_product s))"
  using arg_cong[OF ordinary_capture_keeps_the_exact_source[of s], of retained_log]
  by (simp add: capture_retained_source_def Let_def)

lemma ordinary_capture_keeps_the_outcome_map:
  "outcome_entries (current_product_outcomes s) = retained_outcomes (capture_retained_product s)"
  by (simp add: capture_retained_product_def current_product_outcomes_def
    legal_underlying_outcomes_def Let_def)

lemma ordinary_capture_keeps_the_legal_receipt_map:
  "legal_receipts (regulated_orders s) = retained_legal_receipts (capture_retained_product s)"
  by (simp add: capture_retained_product_def Let_def)

lemma ordinary_capture_keeps_the_spend_receipt_map:
  "spend_receipts s = retained_spend_receipts (capture_retained_product s)"
  by (simp add: capture_retained_product_def Let_def)

lemma ordinary_equal_captures_have_equal_source_cuts:
  assumes same: "capture_retained_product a = capture_retained_product b"
  shows "current_product_cut (outcome_source (current_product_outcomes a)) =
    current_product_cut (outcome_source (current_product_outcomes b))"
  using same
  by (simp add: current_product_cut_def ordinary_capture_keeps_the_source_durable
    ordinary_capture_keeps_the_source_log)

lemma ordinary_result_access_depends_only_on_the_capture:
  assumes same: "capture_retained_product a = capture_retained_product b"
  shows "result_access_bound verified actor call_id payload (current_product_outcomes a) =
    result_access_bound verified actor call_id payload (current_product_outcomes b)"
  using same ordinary_equal_captures_have_equal_source_cuts[OF same]
  by (simp add: result_access_bound_def product_identity_bound_def ordinary_capture_keeps_the_source_durable)

lemma ordinary_completion_readiness_depends_only_on_the_capture:
  assumes same: "capture_retained_product a = capture_retained_product b"
  shows "result_completion_ready saved (current_product_outcomes a) =
    result_completion_ready saved (current_product_outcomes b)"
proof -
  have captured_cores: "retained_core (retained_source (capture_retained_product a)) =
      retained_core (retained_source (capture_retained_product b))"
    by (rule arg_cong[OF same, of "\<lambda>retained. retained_core (retained_source retained)"])
  have source_cores: "call_authority_state (product_calls (outcome_source (current_product_outcomes a))) =
      call_authority_state (product_calls (outcome_source (current_product_outcomes b)))"
  proof -
    have "call_authority_state (product_calls (outcome_source (current_product_outcomes a))) =
        retained_core (retained_source (capture_retained_product a))"
      by (rule ordinary_capture_keeps_the_source_core)
    also have "... = retained_core (retained_source (capture_retained_product b))" by (rule captured_cores)
    also have "... = call_authority_state (product_calls (outcome_source (current_product_outcomes b)))"
      by (rule sym[OF ordinary_capture_keeps_the_source_core])
    finally show ?thesis .
  qed
  show ?thesis by (simp only: result_completion_ready_def Let_def source_cores)
qed

lemma ordinary_result_read_depends_only_on_the_capture:
  assumes same: "capture_retained_product a = capture_retained_product b"
  shows "read_authoritative_result verified actor call_id payload (current_product_outcomes a) =
    read_authoritative_result verified actor call_id payload (current_product_outcomes b)"
proof -
  have access: "result_access_bound verified actor call_id payload (current_product_outcomes a) =
      result_access_bound verified actor call_id payload (current_product_outcomes b)"
    by (rule ordinary_result_access_depends_only_on_the_capture[OF same])
  have entries: "outcome_entries (current_product_outcomes a) = outcome_entries (current_product_outcomes b)"
    using same by (simp add: ordinary_capture_keeps_the_outcome_map)
  have ready: "result_completion_ready saved (current_product_outcomes a) =
      result_completion_ready saved (current_product_outcomes b)" for saved
    by (rule ordinary_completion_readiness_depends_only_on_the_capture[OF same])
  show ?thesis by (simp only: read_authoritative_result_def access entries ready)
qed

lemma ordinary_collection_depends_only_on_capture_and_local_status:
  assumes same: "capture_retained_product a = capture_retained_product b"
    and status: "call_local_status (product_calls (outcome_source (current_product_outcomes a))) =
      call_local_status (product_calls (outcome_source (current_product_outcomes b)))"
  shows "observe_collection verified actor call_id payload (current_product_outcomes a) =
    observe_collection verified actor call_id payload (current_product_outcomes b)"
proof -
  have access: "result_access_bound verified actor call_id payload (current_product_outcomes a) =
      result_access_bound verified actor call_id payload (current_product_outcomes b)"
    by (rule ordinary_result_access_depends_only_on_the_capture[OF same])
  have entries: "outcome_entries (current_product_outcomes a) = outcome_entries (current_product_outcomes b)"
    using same by (simp add: ordinary_capture_keeps_the_outcome_map)
  have ready: "result_completion_ready saved (current_product_outcomes a) =
      result_completion_ready saved (current_product_outcomes b)" for saved
    by (rule ordinary_completion_readiness_depends_only_on_the_capture[OF same])
  show ?thesis by (simp only: observe_collection_def access status entries ready)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ordinary_identity_source_is_the_outcome_source
      ordinary_capture_keeps_the_exact_source ordinary_capture_keeps_the_source_durable
      ordinary_capture_keeps_the_source_core ordinary_capture_keeps_the_source_log
      ordinary_capture_keeps_the_outcome_map ordinary_capture_keeps_the_legal_receipt_map
      ordinary_capture_keeps_the_spend_receipt_map ordinary_equal_captures_have_equal_source_cuts
      ordinary_result_access_depends_only_on_the_capture
      ordinary_completion_readiness_depends_only_on_the_capture
      ordinary_result_read_depends_only_on_the_capture
      ordinary_collection_depends_only_on_capture_and_local_status})
  then () else error "Unexpected oracle in ordinary retained observation projection"
\<close>

end
