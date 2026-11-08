theory Recovery_Fixed_Tag_Reply_Pairs
  imports "Recovery_Product_Changed_Replies"
begin

context source_attestation
begin

lemma two_changed_scheduled_handovers_have_equal_replies:
  assumes produced_a: "result_a = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_a (Service_Handover owner_a successor_a maintainer_a proposal_a) R"
    and produced_b: "result_b = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_b (Service_Handover owner_b successor_b maintainer_b proposal_b) R"
    and changed_a: "fst result_a \<noteq> R"
    and changed_b: "fst result_b \<noteq> R"
  shows "snd result_a = snd result_b"
proof -
  have change_a: "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_a (Service_Handover owner_a successor_a maintainer_a proposal_a) R) \<noteq> R"
    using produced_a changed_a by simp
  have change_b: "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_b (Service_Handover owner_b successor_b maintainer_b proposal_b) R) \<noteq> R"
    using produced_b changed_b by simp
  have reply_a: "snd result_a = Scheduled_Endpoint (Service_Handover_Result True)"
    using a_changed_owner_handover_has_the_true_handover_reply[OF change_a] produced_a by simp
  have reply_b: "snd result_b = Scheduled_Endpoint (Service_Handover_Result True)"
    using a_changed_owner_handover_has_the_true_handover_reply[OF change_b] produced_b by simp
  show ?thesis using reply_a reply_b by simp
qed

lemma two_changed_nonsettlement_maintenances_have_equal_replies:
  assumes produced_a: "result_a = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_a (Service_Maintenance maintenance_a) R"
    and produced_b: "result_b = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_b (Service_Maintenance maintenance_b) R"
    and nonsettlement_a: "\<not> is_settlement_action maintenance_a"
    and nonsettlement_b: "\<not> is_settlement_action maintenance_b"
    and changed_a: "fst result_a \<noteq> R"
    and changed_b: "fst result_b \<noteq> R"
  shows "snd result_a = snd result_b"
proof -
  have change_a: "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_a (Service_Maintenance maintenance_a) R) \<noteq> R" using produced_a changed_a by simp
  have change_b: "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection_b (Service_Maintenance maintenance_b) R) \<noteq> R" using produced_b changed_b by simp
  have reply_a: "snd result_a = Scheduled_Endpoint (Service_Maintenance_Result True)"
    using a_changed_nonsettlement_maintenance_has_the_true_maintenance_reply[OF nonsettlement_a change_a] produced_a by simp
  have reply_b: "snd result_b = Scheduled_Endpoint (Service_Maintenance_Result True)"
    using a_changed_nonsettlement_maintenance_has_the_true_maintenance_reply[OF nonsettlement_b change_b] produced_b by simp
  show ?thesis using reply_a reply_b by simp
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.two_changed_scheduled_handovers_have_equal_replies
      source_attestation.two_changed_nonsettlement_maintenances_have_equal_replies})
  then () else error "Unexpected oracle in fixed success-tag reply pairs"
\<close>

end
