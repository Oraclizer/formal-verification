theory Legal_Receipt_Check
  imports "OIP_Product.Governed_Orders"
begin

section \<open>Existing legal result selection before fresh execution\<close>

text \<open>
  The current native actor, session, officer, and request verification supply
  the admission input. The retained row contains the full stage, order, and
  payload. A fresh decision may separately examine the live revision, grant,
  origin mode, evidence, and deadline. The exact retained result selection
  precedes that fresh decision.
\<close>

datatype 'reply lr_step = LR_Invalid_Authority | LR_Unavailable | LR_Conflicting_Order |
  LR_Retained 'reply | LR_Fresh

definition lr_matches where
  "lr_matches check_stage lr_stage lr_order lr_payload lr_old_stage lr_old_order lr_old_payload \<longleftrightarrow>
    (\<not> check_stage \<or> lr_old_stage = lr_stage) \<and> lr_old_order = lr_order \<and> lr_old_payload = lr_payload"

definition lr_selection where
  "lr_selection check_stage lr_admitted lr_up lr_other_claim lr_stage lr_order lr_payload lr_stored =
    (if \<not> lr_admitted then LR_Invalid_Authority
     else if \<not> lr_up then LR_Unavailable
     else case lr_stored of
       Some (lr_old_stage,lr_old_order,lr_old_payload,lr_reply) \<Rightarrow>
         if lr_matches check_stage lr_stage lr_order lr_payload lr_old_stage lr_old_order lr_old_payload
         then LR_Retained lr_reply else LR_Conflicting_Order
       | None \<Rightarrow> if lr_other_claim then LR_Conflicting_Order else LR_Fresh)"

lemma lr_full_match_is_the_public_legal_receipt_match:
  "lr_matches True lr_stage lr_order lr_payload (receipt_stage lr_row) (receipt_order lr_row) (receipt_payload lr_row) =
   legal_receipt_matches lr_row lr_stage lr_order lr_payload"
  by (simp add: lr_matches_def legal_receipt_matches_def)

lemma lr_authority_and_availability_precede_retained_values:
  "lr_selection check_stage False lr_up lr_other_claim lr_stage lr_order lr_payload lr_stored = LR_Invalid_Authority"
  "lr_selection check_stage True False lr_other_claim lr_stage lr_order lr_payload lr_stored = LR_Unavailable"
  by (simp_all add: lr_selection_def)

lemma lr_another_claim_cannot_reach_fresh_legal_execution:
  "lr_selection check_stage True True True lr_stage lr_order lr_payload None = LR_Conflicting_Order"
  by (simp add: lr_selection_def)

lemma lr_removing_the_stage_guard_releases_the_same_wrong_stage_value:
  assumes "lr_old_stage \<noteq> lr_stage"
  shows "lr_selection True True True lr_other_claim lr_stage lr_order lr_payload
      (Some (lr_old_stage,lr_order,lr_payload,lr_reply)) = LR_Conflicting_Order"
    "lr_selection False True True lr_other_claim lr_stage lr_order lr_payload
      (Some (lr_old_stage,lr_order,lr_payload,lr_reply)) = LR_Retained lr_reply"
  using assms by (simp_all add: lr_selection_def lr_matches_def)

context source_attestation
begin

lemma lr_exact_retained_native_selection_agrees_with_the_public_retry:
  assumes slot: "legal_receipts lr_state lr_call_id = Some lr_row"
    and access: "legal_call_access order_verified verified lr_stage entry who lr_call_id lr_order lr_payload lr_state"
    and up: "call_local_status (exact_calls (read_authority (legal_reads (governed_legal lr_state)))) = Endpoint_Up"
    and retained: "lr_selection True True True lr_other_claim lr_stage lr_order lr_payload
      (Some (receipt_stage lr_row,receipt_order lr_row,receipt_payload lr_row,legal_result lr_row)) =
      LR_Retained lr_value"
  shows "submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
       lr_stage entry who expected lr_call_id lr_order lr_payload lr_state = (lr_state,lr_value)"
proof -
  have retained_match: "legal_receipt_matches lr_row lr_stage lr_order lr_payload"
    and retained_value: "lr_value = legal_result lr_row"
    using retained by (auto simp: lr_selection_def lr_full_match_is_the_public_legal_receipt_match split: if_splits)
  show ?thesis
    using exact_live_legal_order_retry_gets_the_retained_reply[OF slot retained_match access up] retained_value by simp
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms lr_full_match_is_the_public_legal_receipt_match
    lr_authority_and_availability_precede_retained_values lr_another_claim_cannot_reach_fresh_legal_execution
    lr_removing_the_stage_guard_releases_the_same_wrong_stage_value
    source_attestation.lr_exact_retained_native_selection_agrees_with_the_public_retry})
  then () else error "Unexpected oracle in retained legal selection"
\<close>

end
