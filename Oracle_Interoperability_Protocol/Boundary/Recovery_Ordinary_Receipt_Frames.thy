theory Recovery_Ordinary_Receipt_Frames
  imports "OIP_Product.Recovery_Service"
begin

lemma ordinary_outcome_replacement_keeps_both_regulated_receipt_maps:
  "legal_receipts (regulated_orders (replace_product_outcomes outcomes s)) = legal_receipts (regulated_orders s)"
  "spend_receipts (replace_product_outcomes outcomes s) = spend_receipts s"
  by (simp_all add: replace_product_outcomes_def replace_regulated_reads_def Let_def)

context source_attestation
begin

lemma ordinary_regulated_actions_keep_both_regulated_receipt_maps:
  "legal_receipts (regulated_orders
      (regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified
        maintainers registered verified_ack (Ordinary_Product_Action action) s)) = legal_receipts (regulated_orders s)"
  "spend_receipts
      (regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified
        maintainers registered verified_ack (Ordinary_Product_Action action) s) = spend_receipts s"
  by (simp_all add: replace_regulated_reads_def split: if_splits)

lemma ordinary_fresh_effect_keeps_both_regulated_receipt_maps:
  "legal_receipts (regulated_orders
      (run_fresh_durable_effect permitted verified maintainers registered verified_ack legal_grant order_verified
        spend_grant spend_verified read_permitted
        (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s)) =
    legal_receipts (regulated_orders s)"
  "spend_receipts
      (run_fresh_durable_effect permitted verified maintainers registered verified_ack legal_grant order_verified
        spend_grant spend_verified read_permitted
        (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s) = spend_receipts s"
proof -
  have read_legal: "legal_receipts (regulated_orders (replace_regulated_reads reads s)) = legal_receipts (regulated_orders s)" for reads
    by (simp add: replace_regulated_reads_def)
  have read_spend: "spend_receipts (replace_regulated_reads reads s) = spend_receipts s" for reads
    by (simp add: replace_regulated_reads_def)
  show "legal_receipts (regulated_orders
      (run_fresh_durable_effect permitted verified maintainers registered verified_ack legal_grant order_verified
        spend_grant spend_verified read_permitted
        (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s)) =
      legal_receipts (regulated_orders s)"
    and "spend_receipts
      (run_fresh_durable_effect permitted verified maintainers registered verified_ack legal_grant order_verified
        spend_grant spend_verified read_permitted
        (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s) = spend_receipts s"
    by (simp_all add: Let_def record_checked_refusal_def read_legal read_spend
      ordinary_outcome_replacement_keeps_both_regulated_receipt_maps
      ordinary_regulated_actions_keep_both_regulated_receipt_maps split: if_splits)
qed

lemma ordinary_finishing_keeps_both_regulated_receipt_maps:
  "legal_receipts (regulated_orders (fst (finish_durable_execution verified actor
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect claimed_actor call_id payload))) s))) =
    legal_receipts (regulated_orders s)"
  "spend_receipts (fst (finish_durable_execution verified actor
      (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect claimed_actor call_id payload))) s)) = spend_receipts s"
  by (simp_all add: Let_def ordinary_outcome_replacement_keeps_both_regulated_receipt_maps split: if_splits)

lemma ordinary_durable_execute_keeps_both_regulated_receipt_maps:
  "legal_receipts (regulated_orders (fst (durable_execute directory policy authenticate verify endorse route token proof target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s))) =
    legal_receipts (regulated_orders s)"
  "spend_receipts (fst (durable_execute directory policy authenticate verify endorse route token proof target
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s)) =
    spend_receipts s"
  by (simp_all only: durable_execute_def external_call_claim.simps execution_receipt_request.simps
    case_prod_conv option.simps Let_def fst_conv if_True if_False not_True_eq_False not_False_eq_True simp_thms
    ordinary_finishing_keeps_both_regulated_receipt_maps
    ordinary_fresh_effect_keeps_both_regulated_receipt_maps split: if_splits)

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ordinary_outcome_replacement_keeps_both_regulated_receipt_maps
      source_attestation.ordinary_regulated_actions_keep_both_regulated_receipt_maps
      source_attestation.ordinary_fresh_effect_keeps_both_regulated_receipt_maps
      source_attestation.ordinary_finishing_keeps_both_regulated_receipt_maps
      source_attestation.ordinary_durable_execute_keeps_both_regulated_receipt_maps})
  then () else error "Unexpected oracle in ordinary regulated receipt frames"
\<close>

end
