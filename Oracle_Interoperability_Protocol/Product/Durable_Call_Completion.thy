theory Durable_Call_Completion
  imports Recovery_Anchor
begin

definition current_product_outcomes where
  "current_product_outcomes s = legal_underlying_outcomes (governed_legal (regulated_orders s))"

definition replace_product_outcomes where
  "replace_product_outcomes outcomes s =
    (let reads = regulated_read_world s;
         updated = update_settlement_outcomes outcomes (read_authority reads)
     in replace_regulated_reads (reads\<lparr>read_authority := updated\<rparr>) s)"

lemma replacement_supplies_exact_outcome_table [simp]:
  "current_product_outcomes (replace_product_outcomes outcomes s) = outcomes"
  by (simp add: current_product_outcomes_def replace_product_outcomes_def regulated_read_world_def
      replace_regulated_reads_def legal_underlying_outcomes_def update_settlement_outcomes_def Let_def)

definition authority_has_call_id where
  "authority_has_call_id call_id s \<longleftrightarrow>
    outcome_entries (current_product_outcomes s) call_id \<noteq> None \<or> \<not> unclaimed_regulated_call s call_id"

fun execution_receipt_request where
  "execution_receipt_request (Apply_Governed_Order stage entry actor expected call_id order payload) =
     Some (Collect_Governed_Order stage entry actor call_id order payload)"
| "execution_receipt_request (Apply_Governed_Spend entry actor expected call_id payload authorization) =
     Some (Collect_Governed_Spend actor call_id payload authorization)"
| "execution_receipt_request (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) =
     Some (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect actor call_id payload)))"
| "execution_receipt_request action = None"

datatype durable_execution_reply =
    Durable_Execution_Reply authorized_receipt
  | Durable_Execution_Reject
  | Durable_Execution_Wait

definition record_checked_refusal where
  "record_checked_refusal call_id payload refusal s =
    (let outcomes = current_product_outcomes s
     in if authority_has_call_id call_id s then s
        else replace_product_outcomes (store_product_result call_id payload refusal (outcome_source outcomes) outcomes) s)"

lemma checked_refusal_keeps_the_exact_underlying_source:
  "outcome_source (current_product_outcomes (record_checked_refusal call_id payload refusal s)) =
    outcome_source (current_product_outcomes s)"
  by (simp add: record_checked_refusal_def store_product_result_def Let_def)

lemma fresh_checked_refusal_records_the_exact_request:
  assumes "\<not> authority_has_call_id call_id s"
  shows "outcome_entries (current_product_outcomes (record_checked_refusal call_id payload refusal s)) call_id =
    Some \<lparr>result_payload = payload, result_outcome = refusal\<rparr>"
  using assms by (simp add: record_checked_refusal_def store_product_result_def Let_def)

context source_attestation
begin

fun finish_durable_execution where
  "finish_durable_execution verified actor
    (Ordinary_Product_Action (Read_Authority_Action (Exact_Collect who call_id payload))) s =
      (if \<not> unclaimed_regulated_call s call_id then (s, Durable_Execution_Reject)
       else let outcome = current_product_outcomes s;
                completed = fst (complete_authoritative_result verified actor call_id payload outcome)
            in (replace_product_outcomes completed s,
                Durable_Execution_Reply (Observed_Ordinary_Result (observe_collection verified actor call_id payload outcome))))"
| "finish_durable_execution verified actor action s =
    (s, case exact_endpoint_receipt verified actor action s of None \<Rightarrow> Durable_Execution_Reject
      | Some receipt \<Rightarrow> Durable_Execution_Reply receipt)"

lemma finishing_does_not_reapply_authority_effects:
  "outcome_source (current_product_outcomes (fst (finish_durable_execution verified actor action s))) =
    outcome_source (current_product_outcomes s)"
proof -
  have unchanged: "outcome_source (fst (complete_authoritative_result verified actor call_id payload outcomes)) =
    outcome_source outcomes" for verified actor call_id payload outcomes
    by (simp add: complete_authoritative_result_def split: option.splits if_splits)
  show ?thesis
    by (induction verified actor action s rule: finish_durable_execution.induct)
      (simp_all add: Let_def unchanged split: if_splits)
qed

end

end
