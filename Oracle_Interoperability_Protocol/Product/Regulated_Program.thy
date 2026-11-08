theory Regulated_Program
  imports Spending_Receipts Protected_Source_Debit
begin

fun governed_command where
  "governed_command (Client_Terminal cert) =
    (case binding_operation (statement_binding (certificate_statement cert)) of Regulatory_State_Effect action \<Rightarrow> True | _ \<Rightarrow> False)"
| "governed_command (Client_Regulatory endpoint index request) = True"
| "governed_command (Client_Protocol endpoint index (Descendant_Intent r root sender recipient amount)) = True"
| "governed_command command = False"

definition unclaimed_regulated_call where
  "unclaimed_regulated_call s call_id \<longleftrightarrow>
    legal_receipts (regulated_orders s) call_id = None \<and> spend_receipts s call_id = None"

fun ungoverned_read_action where
  "ungoverned_read_action s (Execute_Checked entry who expected call_id payload) =
     (\<not> governed_command (envelope_command (payload_envelope payload)) \<and> unclaimed_regulated_call s call_id)"
| "ungoverned_read_action s (Read_Authority_Action (Exact_Collect who call_id payload)) = unclaimed_regulated_call s call_id"
| "ungoverned_read_action s (Read_Authority_Action (Exact_Submit entry who call_id payload)) = False"
| "ungoverned_read_action s action = True"

datatype regulated_product_action =
    Apply_Governed_Order legal_stage regulatory_entry product_principal product_cut client_call_id product_legal_order product_call_payload
  | Apply_Governed_Spend regulatory_entry product_principal product_cut client_call_id product_call_payload "product_spend_authorization option"
  | Collect_Governed_Order legal_stage regulatory_entry product_principal client_call_id product_legal_order product_call_payload
  | Collect_Governed_Spend product_principal client_call_id product_call_payload "product_spend_authorization option"
  | Ordinary_Product_Action product_read_action

context source_attestation
begin

fun regulated_product_step where
  "regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    (Apply_Governed_Order stage entry who expected call_id order payload) s =
    (if spend_receipts s call_id \<noteq> None then s else s\<lparr>regulated_orders := fst
      (submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
        stage entry who expected call_id order payload (regulated_orders s))\<rparr>)"
| "regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    (Apply_Governed_Spend entry who expected call_id payload authorization) s =
    fst (submit_governed_spend spend_grant spend_verified permitted verified maintainers registered verified_ack
      entry who expected call_id payload authorization s)"
| "regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    (Collect_Governed_Order stage entry who call_id order payload) s =
    (if legal_call_access order_verified verified stage entry who call_id order payload (regulated_orders s) \<and>
        (\<exists>receipt. legal_receipts (regulated_orders s) call_id = Some receipt \<and> legal_receipt_matches receipt stage order payload)
     then replace_regulated_reads (product_read_step read_permitted permitted verified maintainers registered verified_ack
       (Read_Authority_Action (Exact_Collect who call_id payload)) (regulated_read_world s)) s else s)"
| "regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    (Collect_Governed_Spend who call_id payload authorization) s =
    (if (\<exists>receipt. spend_receipts s call_id = Some receipt \<and> spend_receipt_payload receipt = payload \<and>
      spend_receipt_order receipt = authorization) then
      replace_regulated_reads (product_read_step read_permitted permitted verified maintainers registered verified_ack
        (Read_Authority_Action (Exact_Collect who call_id payload)) (regulated_read_world s)) s else s)"
| "regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    (Ordinary_Product_Action action) s =
    (if ungoverned_read_action s action then replace_regulated_reads
      (product_read_step read_permitted permitted verified maintainers registered verified_ack action (regulated_read_world s)) s else s)"

lemma ordinary_entry_cannot_bypass_a_governed_consumer:
  assumes "governed_command (envelope_command (payload_envelope payload))"
  shows "regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    (Ordinary_Product_Action (Execute_Checked entry who expected call_id payload)) s = s"
  using assms by simp

lemma legally_refused_stage_keeps_primary_and_financial_view:
  assumes refused: "snd (submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
      stage entry who expected call_id order payload (regulated_orders s)) = Legal_Blocked reason"
  shows "regulated_read_world (regulated_product_step legal_grant order_verified spend_grant spend_verified
    read_permitted permitted verified maintainers registered verified_ack
    (Apply_Governed_Order stage entry who expected call_id order payload) s) = regulated_read_world s"
proof -
  let ?result = "submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
    stage entry who expected call_id order payload (regulated_orders s)"
  have actual: "?result = (fst ?result, Legal_Blocked reason)" using refused by (cases ?result) simp
  have same: "governed_legal (fst ?result) = governed_legal (regulated_orders s)"
    by (rule governed_legal_rejection_preserves_source_receiver_and_terminal_state[OF actual])
  show ?thesis by (simp add: regulated_read_world_def same)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    source_attestation.governed_legal_rejection_preserves_source_receiver_and_terminal_state
    shortened_appeal_deadline_cannot_authorize_confiscation
    confiscation_spend_checks_the_recorded_appeal_deadline
    source_attestation.confiscation_forwarding_consumes_the_current_seizure_and_deadline
    source_attestation.legal_order_retry_cannot_reexecute
    source_attestation.ordinary_entry_cannot_bypass_a_governed_consumer
    source_attestation.ordinary_spend_after_freeze_without_thaw_is_rejected
    source_attestation.protected_source_debit_does_not_move_funds
    source_attestation.lawful_enforcement_consumes_the_exact_confirmed_root})
  then () else error "Unexpected oracle in legal admission and regulated spending"
\<close>

end
