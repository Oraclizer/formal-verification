theory Governed_Orders
  imports Legal_Product
begin

record legal_request_receipt =
  receipt_stage :: legal_stage
  receipt_order :: product_legal_order
  receipt_payload :: product_call_payload
  legal_result :: legal_execution_reply

record governed_world =
  governed_legal :: legal_product_world
  legal_receipts :: "client_call_id \<Rightarrow> legal_request_receipt option"

definition initial_governed_world where
  "initial_governed_world s = \<lparr>governed_legal = initial_legal_world s, legal_receipts = (\<lambda>_. None)\<rparr>"

definition legal_receipt_matches where
  "legal_receipt_matches receipt stage order payload \<longleftrightarrow>
    receipt_stage receipt = stage \<and> receipt_order receipt = order \<and> receipt_payload receipt = payload"

definition legal_call_access where
  "legal_call_access order_verified verified stage entry who call_id order payload s \<longleftrightarrow>
    order_verified stage entry who order \<and>
    result_access_bound verified who call_id payload (legal_underlying_outcomes (governed_legal s))"

context source_attestation
begin

definition submit_governed_order where
  "submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
       stage entry who expected call_id order payload s =
    (let authority = governed_legal s in
      if \<not> legal_call_access order_verified verified stage entry who call_id order payload s
      then (s, Legal_Blocked Invalid_Legal_Authority)
      else if call_local_status (exact_calls (read_authority (legal_reads authority))) \<noteq> Endpoint_Up
      then (s, Legal_Checked Checked_Execution_Unavailable)
      else case legal_receipts s call_id of Some receipt \<Rightarrow>
        if legal_receipt_matches receipt stage order payload then (s, legal_result receipt)
        else (s, Legal_Blocked Conflicting_Legal_Order)
      | None \<Rightarrow> if outcome_entries (legal_underlying_outcomes authority) call_id \<noteq> None
        then (s, Legal_Blocked Conflicting_Legal_Order)
        else let result = (if read_authority_available (legal_reads authority) then
             run_legal_effect legal_grant order_verified permitted verified maintainers registered verified_ack
               stage entry who expected call_id order payload authority
           else (authority, Legal_Checked Checked_Execution_Unavailable));
             receipt = \<lparr>receipt_stage = stage, receipt_order = order, receipt_payload = payload, legal_result = snd result\<rparr>
           in (s\<lparr>governed_legal := fst result, legal_receipts := (legal_receipts s)(call_id := Some receipt)\<rparr>, snd result))"

theorem governed_legal_rejection_preserves_source_receiver_and_terminal_state:
  assumes "submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
       stage entry who expected call_id order payload s = (next, Legal_Blocked reason)"
  shows "governed_legal next = governed_legal s"
  using assms by (auto simp: submit_governed_order_def Let_def
      intro: any_rejected_legal_entry_preserves_all_authority_state split: option.splits if_splits)

lemma legal_order_retry_cannot_reexecute:
  "legal_receipts s call_id = Some receipt \<Longrightarrow>
    fst (submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
       stage entry who expected call_id order payload s) = s"
  by (simp add: submit_governed_order_def Let_def split: if_splits)

lemma exact_live_legal_order_retry_gets_the_retained_reply:
  assumes "legal_receipts s call_id = Some receipt" "legal_receipt_matches receipt stage order payload"
    "legal_call_access order_verified verified stage entry who call_id order payload s"
    "call_local_status (exact_calls (read_authority (legal_reads (governed_legal s)))) = Endpoint_Up"
  shows "submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
       stage entry who expected call_id order payload s = (s, legal_result receipt)"
  using assms by (simp add: submit_governed_order_def Let_def)

end

end
