theory Recovery_Legal_Spend_Reply_Records
  imports Recovery_Reply_Table_Insertions
begin

text \<open>These facts concern the legal and spend subproducers of Execute. Different authority
  connections may have different live worlds but the same retained base map. The outer durable
  Execute/collector and cross-constructor relation are handled by separate modules.\<close>

context source_attestation
begin

lemma a_changed_legal_submission_inserts_its_exact_returned_reply:
  assumes produced: "result = submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
      stage entry who expected call_id order payload before"
    and changed: "fst result \<noteq> before"
  shows "legal_receipts before call_id = None"
    and "legal_receipts (fst result) = (legal_receipts before)(call_id := Some
      \<lparr>receipt_stage = stage, receipt_order = order, receipt_payload = payload, legal_result = snd result\<rparr>)"
  using produced changed
  by (auto simp: submit_governed_order_def Let_def split: option.splits if_splits)

lemma a_changed_spend_submission_inserts_its_exact_returned_reply:
  assumes produced: "result = submit_governed_spend grant spend_verified permitted verified maintainers registered verified_ack
      entry who expected call_id payload authorization before"
    and changed: "fst result \<noteq> before"
  shows "spend_receipts before call_id = None"
    and "spend_receipts (fst result) = (spend_receipts before)(call_id := Some
      \<lparr>spend_receipt_payload = payload, spend_receipt_order = authorization, spend_receipt_reply = snd result\<rparr>)"
  using produced changed
  by (auto simp: submit_governed_spend_def Let_def split: option.splits if_splits)

lemma equal_changed_legal_receipt_maps_determine_the_returned_reply:
  assumes produced_a: "result_a = submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
      stage_a entry_a who_a expected_a id_a order_a payload_a before_a"
    and produced_b: "result_b = submit_governed_order legal_grant order_verified permitted verified maintainers registered verified_ack
      stage_b entry_b who_b expected_b id_b order_b payload_b before_b"
    and changed_a: "fst result_a \<noteq> before_a"
    and changed_b: "fst result_b \<noteq> before_b"
    and base_maps: "legal_receipts before_a = legal_receipts before_b"
    and result_maps: "legal_receipts (fst result_a) = legal_receipts (fst result_b)"
  shows "snd result_a = snd result_b"
proof -
  let ?a = "\<lparr>receipt_stage = stage_a, receipt_order = order_a, receipt_payload = payload_a, legal_result = snd result_a\<rparr>"
  let ?b = "\<lparr>receipt_stage = stage_b, receipt_order = order_b, receipt_payload = payload_b, legal_result = snd result_b\<rparr>"
  note first = a_changed_legal_submission_inserts_its_exact_returned_reply[OF produced_a changed_a]
  note second = a_changed_legal_submission_inserts_its_exact_returned_reply[OF produced_b changed_b]
  have updates: "(legal_receipts before_a)(id_a := Some ?a) = (legal_receipts before_b)(id_b := Some ?b)"
    using first(2) second(2) result_maps by simp
  have records: "?a = ?b"
    by (rule equal_insertions_over_equal_base_tables_identify_the_value[OF base_maps first(1) second(1) updates])
  have "legal_result ?a = legal_result ?b" by (rule arg_cong[OF records])
  then show ?thesis by simp
qed

lemma equal_changed_spend_receipt_maps_determine_the_returned_reply:
  assumes produced_a: "result_a = submit_governed_spend grant spend_verified permitted verified maintainers registered verified_ack
      entry_a who_a expected_a id_a payload_a authorization_a before_a"
    and produced_b: "result_b = submit_governed_spend grant spend_verified permitted verified maintainers registered verified_ack
      entry_b who_b expected_b id_b payload_b authorization_b before_b"
    and changed_a: "fst result_a \<noteq> before_a"
    and changed_b: "fst result_b \<noteq> before_b"
    and base_maps: "spend_receipts before_a = spend_receipts before_b"
    and result_maps: "spend_receipts (fst result_a) = spend_receipts (fst result_b)"
  shows "snd result_a = snd result_b"
proof -
  let ?a = "\<lparr>spend_receipt_payload = payload_a, spend_receipt_order = authorization_a, spend_receipt_reply = snd result_a\<rparr>"
  let ?b = "\<lparr>spend_receipt_payload = payload_b, spend_receipt_order = authorization_b, spend_receipt_reply = snd result_b\<rparr>"
  note first = a_changed_spend_submission_inserts_its_exact_returned_reply[OF produced_a changed_a]
  note second = a_changed_spend_submission_inserts_its_exact_returned_reply[OF produced_b changed_b]
  have updates: "(spend_receipts before_a)(id_a := Some ?a) = (spend_receipts before_b)(id_b := Some ?b)"
    using first(2) second(2) result_maps by simp
  have records: "?a = ?b"
    by (rule equal_insertions_over_equal_base_tables_identify_the_value[OF base_maps first(1) second(1) updates])
  have "spend_receipt_reply ?a = spend_receipt_reply ?b" by (rule arg_cong[OF records])
  then show ?thesis by simp
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.a_changed_legal_submission_inserts_its_exact_returned_reply
      source_attestation.a_changed_spend_submission_inserts_its_exact_returned_reply
      source_attestation.equal_changed_legal_receipt_maps_determine_the_returned_reply
      source_attestation.equal_changed_spend_receipt_maps_determine_the_returned_reply})
  then () else error "Unexpected oracle in legal/spend reply reconstruction"
\<close>

end
