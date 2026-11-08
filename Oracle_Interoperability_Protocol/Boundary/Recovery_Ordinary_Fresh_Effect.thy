theory Recovery_Ordinary_Fresh_Effect
  imports Recovery_Ordinary_Fresh_Rows "Recovery_Ordinary_Completion_Shape"
begin

lemma ordinary_replacing_the_current_reads_is_identity:
  "replace_regulated_reads (regulated_read_world s) s = s"
  by (simp add: replace_regulated_reads_def regulated_read_world_def)

lemma ordinary_read_replacement_exposes_exact_outcomes:
  "current_product_outcomes (replace_regulated_reads reads s) =
    origin_outcomes (settlement_primary (read_authority reads))"
  by (simp add: current_product_outcomes_def legal_underlying_outcomes_def replace_regulated_reads_def)

context source_attestation
begin

lemma ordinary_checked_effect_stutters_or_inserts_the_exact_request_row:
  assumes fresh: "outcome_entries (current_product_outcomes s) call_id = None"
  shows "regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified
      maintainers registered verified_ack (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s = s \<or>
    (\<exists>reply. outcome_entries (current_product_outcomes
      (regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified
        maintainers registered verified_ack (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s)) =
      (outcome_entries (current_product_outcomes s))
        (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>))"
proof -
  let ?reads = "regulated_read_world s"
  let ?authority = "read_authority ?reads"
  let ?origins = "settlement_primary ?authority"
  let ?submitted = "submit_origin_call permitted verified maintainers registered entry actor call_id payload ?origins"
  have old_outcomes: "origin_outcomes ?origins = current_product_outcomes s"
    by (simp add: current_product_outcomes_def legal_underlying_outcomes_def regulated_read_world_def)
  have origin_fresh: "outcome_entries (origin_outcomes ?origins) call_id = None"
    using fresh old_outcomes by simp
  have alternatives: "?submitted = ?origins \<or>
      (\<exists>reply. outcome_entries (origin_outcomes ?submitted) =
        (outcome_entries (origin_outcomes ?origins))
          (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>))"
    by (rule ordinary_origin_submission_stutters_or_inserts_the_exact_request_row[OF origin_fresh])
  from alternatives show ?thesis
  proof (elim disjE)
    assume stutter: "?submitted = ?origins"
    have checked_stutter: "fst (execute_at_checked_cut permitted verified maintainers registered verified_ack
        entry actor expected call_id payload ?reads) = ?reads"
      by (simp add: execute_at_checked_cut_def Let_def stutter split: if_splits)
    have actual_stutter: "regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified
        maintainers registered verified_ack (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s = s"
      by (simp add: checked_stutter ordinary_replacing_the_current_reads_is_identity)
    show ?thesis by (rule disjI1[OF actual_stutter])
  next
    assume rows: "\<exists>reply. outcome_entries (origin_outcomes ?submitted) =
        (outcome_entries (origin_outcomes ?origins))
          (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>)"
    then obtain reply where inserted: "outcome_entries (origin_outcomes ?submitted) =
        (outcome_entries (origin_outcomes ?origins))
          (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>)" by blast
    show ?thesis
      using inserted old_outcomes
      by (auto simp: execute_at_checked_cut_def Let_def
        ordinary_read_replacement_exposes_exact_outcomes ordinary_replacing_the_current_reads_is_identity
        split: if_splits)
  qed
qed

lemma ordinary_fresh_effect_stutters_or_inserts_the_exact_request_row:
  assumes no_prior: "\<not> authority_has_call_id call_id s"
  shows "run_fresh_durable_effect permitted verified maintainers registered verified_ack legal_grant order_verified
      spend_grant spend_verified read_permitted
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s = s \<or>
    (\<exists>reply. outcome_entries (current_product_outcomes
      (run_fresh_durable_effect permitted verified maintainers registered verified_ack legal_grant order_verified
        spend_grant spend_verified read_permitted
        (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s)) =
      (outcome_entries (current_product_outcomes s))
        (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>))"
proof -
  let ?effect = "run_fresh_durable_effect permitted verified maintainers registered verified_ack legal_grant order_verified
    spend_grant spend_verified read_permitted
    (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s"
  let ?normal = "regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified
    maintainers registered verified_ack (Ordinary_Product_Action (Execute_Checked Normal_Lock_Entry actor expected call_id payload)) s"
  let ?source = "identity_source s"
  let ?envelope = "payload_envelope payload"
  let ?origins = "settlement_primary (read_authority (regulated_read_world s))"
  let ?recorded = "record_released_credit_receipt permitted verified registered Normal_Lock_Entry actor call_id payload ?origins"
  let ?released = "replace_product_outcomes (origin_outcomes (fst ?recorded)) s"
  have fresh: "outcome_entries (current_product_outcomes s) call_id = None"
    using no_prior by (simp add: authority_has_call_id_def)
  have old_outcomes: "origin_outcomes ?origins = current_product_outcomes s"
    by (simp add: current_product_outcomes_def legal_underlying_outcomes_def regulated_read_world_def)
  have normal: "?normal = s \<or> (\<exists>reply. outcome_entries (current_product_outcomes ?normal) =
      (outcome_entries (current_product_outcomes s))
        (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>))"
    by (rule ordinary_checked_effect_stutters_or_inserts_the_exact_request_row[OF fresh])
  have recorded: "fst ?recorded = ?origins \<or>
      (\<exists>reply. outcome_entries (origin_outcomes (fst ?recorded)) =
        (outcome_entries (origin_outcomes ?origins))
          (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>))"
    by (rule ordinary_released_credit_recording_stutters_or_inserts_the_exact_request_row)
  have released: "?released = s \<or> (\<exists>reply. outcome_entries (current_product_outcomes ?released) =
      (outcome_entries (current_product_outcomes s))
        (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>))"
    using recorded old_outcomes
    by (auto simp: replacing_the_exact_current_outcomes_is_identity)
  have refusal: "record_checked_refusal call_id payload refused s = s \<or>
      (\<exists>reply. outcome_entries (current_product_outcomes (record_checked_refusal call_id payload refused s)) =
        (outcome_entries (current_product_outcomes s))
          (call_id := Some \<lparr>result_payload = payload, result_outcome = reply\<rparr>))" for refused
    by (rule disjI2, rule exI[of _ refused])
      (simp add: record_checked_refusal_def no_prior store_product_result_def Let_def)
  show ?thesis
  proof (cases "governed_command (envelope_command ?envelope) \<or> expected \<noteq> envelope_cut ?envelope")
    case True
    have effect: "?effect = s"
      by (simp only: run_fresh_durable_effect.simps Let_def True if_True)
    show ?thesis by (rule disjI1[OF effect])
  next
    case gate: False
    show ?thesis
    proof (cases "call_connection (product_calls ?source) \<noteq> Authority_Connected")
      case True
      have effect: "?effect = record_checked_refusal call_id payload Authority_Unavailable s"
        using gate True by (simp add: Let_def)
      show ?thesis using refusal[of Authority_Unavailable] effect by simp
    next
      case connected: False
      show ?thesis
      proof (cases "expected \<noteq> current_product_cut ?source")
        case True
        have effect: "?effect = record_checked_refusal call_id payload Authority_Busy s"
          using gate connected True by (simp add: Let_def)
        show ?thesis using refusal[of Authority_Busy] effect by simp
      next
        case exact: False
        show ?thesis
        proof (cases "snd ?recorded")
          case None
          have effect: "?effect = ?normal"
            by (simp only: run_fresh_durable_effect.simps Let_def gate connected exact no_prior None
              if_True if_False simp_thms option.simps canonical_consumer_action.simps)
          show ?thesis using normal unfolding effect .
        next
          case (Some position)
          have effect: "?effect = ?released"
            by (simp only: run_fresh_durable_effect.simps Let_def gate connected exact no_prior Some
              if_True if_False simp_thms option.simps canonical_consumer_action.simps)
          show ?thesis using released unfolding effect .
        qed
      qed
    qed
  qed
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ordinary_replacing_the_current_reads_is_identity
      ordinary_read_replacement_exposes_exact_outcomes
      source_attestation.ordinary_checked_effect_stutters_or_inserts_the_exact_request_row
      source_attestation.ordinary_fresh_effect_stutters_or_inserts_the_exact_request_row})
  then () else error "Unexpected oracle in ordinary fresh effect reconstruction"
\<close>

end
