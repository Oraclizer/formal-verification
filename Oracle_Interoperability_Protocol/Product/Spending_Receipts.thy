theory Spending_Receipts
  imports Spend_Effects
begin

context source_attestation
begin

definition submit_governed_spend where
  "submit_governed_spend grant spend_verified permitted verified maintainers registered verified_ack
      entry who expected call_id payload authorization s =
    (let legal = governed_legal (regulated_orders s); reads = legal_reads legal;
         old = legal_underlying_outcomes legal in
      if \<not> result_access_bound verified who call_id payload old then (s, Spend_Blocked)
      else if call_local_status (exact_calls (read_authority reads)) \<noteq> Endpoint_Up
        then (s, Spend_Checked Checked_Execution_Unavailable)
      else case spend_receipts s call_id of Some receipt \<Rightarrow>
        if spend_receipt_payload receipt = payload \<and> spend_receipt_order receipt = authorization
        then (s, spend_receipt_reply receipt) else (s, Spend_Blocked)
      | None \<Rightarrow> if legal_receipts (regulated_orders s) call_id \<noteq> None \<or> outcome_entries old call_id \<noteq> None
        then (s, Spend_Blocked)
        else let result = run_spend_effect grant spend_verified permitted verified maintainers registered verified_ack
                   entry who expected call_id payload authorization s;
             next = fst result;
             receipt = \<lparr>spend_receipt_payload = payload, spend_receipt_order = authorization, spend_receipt_reply = snd result\<rparr>
           in (next\<lparr>spend_receipts := (spend_receipts s)(call_id := Some receipt)\<rparr>, snd result))"

lemma blocked_spend_preserves_the_authority_view:
  assumes refused: "snd (submit_governed_spend grant spend_verified permitted verified maintainers registered verified_ack
    entry who expected call_id payload authorization s) = Spend_Blocked"
  shows "regulated_read_world (fst (submit_governed_spend grant spend_verified permitted verified maintainers registered verified_ack
    entry who expected call_id payload authorization s)) = regulated_read_world s"
proof -
  let ?legal = "governed_legal (regulated_orders s)"
  let ?old = "legal_underlying_outcomes ?legal"
  let ?reads = "legal_reads ?legal"
  let ?effect = "run_spend_effect grant spend_verified permitted verified maintainers registered verified_ack
    entry who expected call_id payload authorization s"
  show ?thesis
  proof (cases "result_access_bound verified who call_id payload ?old")
    case False
    then show ?thesis by (simp add: submit_governed_spend_def Let_def)
  next
    case True
    note access = this
    show ?thesis
    proof (cases "call_local_status (exact_calls (read_authority ?reads)) = Endpoint_Up")
      case False
      with access show ?thesis by (simp add: submit_governed_spend_def Let_def)
    next
      case True
      note live = this
      show ?thesis
      proof (cases "spend_receipts s call_id")
        case (Some receipt)
        with access live show ?thesis by (simp add: submit_governed_spend_def Let_def split: if_splits)
      next
        case None
        note fresh = this
        show ?thesis
        proof (cases "legal_receipts (regulated_orders s) call_id \<noteq> None \<or> outcome_entries ?old call_id \<noteq> None")
          case True
          with access live fresh show ?thesis by (simp add: submit_governed_spend_def Let_def)
        next
          case False
          have denied: "snd ?effect = Spend_Blocked"
            using refused access live fresh False
            by (simp only: submit_governed_spend_def Let_def option.simps simp_thms if_True if_False prod.sel)
          have noop: "fst ?effect = s" by (rule blocked_spend_effect_leaves_the_world_unchanged[OF denied])
          show ?thesis using access live fresh False noop
            by (simp add: submit_governed_spend_def regulated_read_world_def Let_def)
        qed
      qed
    qed
  qed
qed

lemma spending_retry_does_not_reexecute:
  "spend_receipts s call_id = Some receipt \<Longrightarrow>
    fst (submit_governed_spend grant spend_verified permitted verified maintainers registered verified_ack
    entry who expected call_id payload authorization s) = s"
  by (simp add: submit_governed_spend_def Let_def split: if_splits)

end

end
