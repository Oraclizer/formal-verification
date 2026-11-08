theory Promotion_Primary_Decisions
  imports Promotion_Call_Ids
begin

definition current_primary_decisions where
  "current_primary_decisions s = origin_decisions (settlement_primary (read_authority (regulated_read_world s)))"

lemma replacing_the_outcome_table_preserves_primary_decisions [simp]:
  "current_primary_decisions (replace_product_outcomes outcomes s) = current_primary_decisions s"
  by (simp add: current_primary_decisions_def replace_product_outcomes_def update_settlement_outcomes_def Let_def)

lemma replacing_product_source_preserves_primary_decisions [simp]:
  "current_primary_decisions (replace_identity_source source s) = current_primary_decisions s"
  by (simp add: current_primary_decisions_def replace_identity_source_def update_settlement_outcomes_def Let_def)

lemma replacing_queue_preserves_primary_decisions [simp]:
  "current_primary_decisions (replace_service_jobs jobs s) = current_primary_decisions s"
  by (simp add: current_primary_decisions_def service_settlement_def)

lemma capture_uses_the_actual_primary_decisions [simp]:
  "retained_decisions (capture_retained_product s) = current_primary_decisions s"
  by (simp add: capture_retained_product_def current_primary_decisions_def regulated_read_world_def Let_def)

lemma reopening_uses_the_exact_retained_primary_decisions [simp]:
  "current_primary_decisions (reopen_retained_product connection retained) = retained_decisions retained"
  by (simp add: reopen_retained_product_def current_primary_decisions_def regulated_read_world_def initial_product_reads_def Let_def)

context source_attestation
begin

lemma checked_result_finishing_preserves_primary_decisions [simp]:
  "current_primary_decisions (fst (finish_durable_execution verified actor action s)) = current_primary_decisions s"
  by (induction verified actor action s rule: finish_durable_execution.induct)
    (simp_all add: Let_def split: if_splits)

lemma checked_preflight_refusal_preserves_primary_decisions [simp]:
  "current_primary_decisions (record_checked_refusal call_id payload refusal s) = current_primary_decisions s"
  by (simp add: record_checked_refusal_def Let_def split: if_splits)

lemma regulated_admission_keeps_a_recorded_primary_decision:
  assumes "current_primary_decisions s key = Some recorded"
  shows "current_primary_decisions
     (regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers
        registered verified_ack action s) key = Some recorded"
proof -
  let ?next = "regulated_product_step legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers
     registered verified_ack action s"
  have segment: "read_source_segment (regulated_read_world s) (regulated_read_world ?next)"
    by (rule regulated_step_has_an_actual_source_segment)
  show ?thesis using segment assms unfolding read_source_segment_def current_primary_decisions_def by blast
qed

lemma fresh_durable_execution_keeps_a_recorded_primary_decision:
  assumes "current_primary_decisions s key = Some recorded"
  shows "current_primary_decisions (run_fresh_durable_effect permitted verified maintainers registered verified_ack
    legal_grant order_verified spend_grant spend_verified read_permitted action s) key = Some recorded"
  using assms
  by (induction permitted verified maintainers registered verified_ack legal_grant order_verified
      spend_grant spend_verified read_permitted action s rule: run_fresh_durable_effect.induct)
    (simp_all del: regulated_product_step.simps add: Let_def regulated_admission_keeps_a_recorded_primary_decision
      split: if_splits)

lemma durable_execution_keeps_a_recorded_primary_decision:
  assumes "current_primary_decisions s key = Some recorded"
  shows "current_primary_decisions (fst (durable_execute directory policy authenticate verify endorse route token proof target action authorization
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s)) key = Some recorded"
proof (cases "external_call_claim action")
  case None
  then show ?thesis using assms by (simp add: durable_execute_def)
next
  case (Some claimed)
  obtain operation actor call_id payload where tuple: "claimed = (operation, actor, call_id, payload)"
    by (cases claimed) auto
  from Some tuple assms show ?thesis
    by (cases "execution_receipt_request action")
      (simp_all add: durable_execute_def Let_def fresh_durable_execution_keeps_a_recorded_primary_decision
        split: if_splits)
qed

lemma product_service_keeps_a_recorded_primary_decision:
  assumes "current_primary_decisions s key = Some recorded"
  shows "current_primary_decisions (fst (live_product_service_step directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action s))
      key = Some recorded"
proof (cases action)
  case (Service_Execute route token session_value target submitted endorsement)
  then show ?thesis using assms by (simp add: Let_def durable_execution_keeps_a_recorded_primary_decision)
next
  case (Service_Maintenance maintenance)
  have kept: "origin_decisions (settlement_primary (exact_step permitted verified maintainers registered verified_ack
      maintenance (read_authority (regulated_read_world s)))) key = Some recorded"
    by (rule exact_step_keeps_existing_decision) (use assms in \<open>simp add: current_primary_decisions_def\<close>)
  show ?thesis using Service_Maintenance kept assms
    by (simp add: current_primary_decisions_def Let_def split: if_splits)
qed (simp_all add: assms Let_def handover_product_owner_def split: if_splits)

lemma scheduled_service_keeps_a_recorded_primary_decision:
  assumes "current_primary_decisions s key = Some recorded"
  shows "current_primary_decisions (fst (schedule_service_step directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action s))
      key = Some recorded"
  using assms by (cases action)
    (simp_all del: live_product_service_step.simps add: schedule_service_step_def Let_def
      product_service_keeps_a_recorded_primary_decision split: if_splits)

theorem no_actual_product_continuation_overwrites_a_primary_decision:
  fixes execute :: "authority_connection \<Rightarrow> 'token retained_service_action \<Rightarrow> retained_product \<Rightarrow> retained_product \<times> scheduled_service_reply"
    and directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
  defines "execute \<equiv> schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack"
  assumes recorded_initial: "retained_decisions initial key = Some recorded"
  shows "retained_decisions (run_product_action_word execute actions initial) key = Some recorded"
  using recorded_initial
proof (induction actions arbitrary: initial)
  case Nil
  then show ?case by simp
next
  case (Cons first rest)
  note tail_induction = Cons(1)
  obtain connection action where head: "first = (connection, action)" by (cases first)
  let ?s = "reopen_retained_product connection initial"
  have before: "current_primary_decisions ?s key = Some recorded"
    using Cons.prems by simp
  have next_decision: "retained_decisions (fst (execute connection action initial)) key = Some recorded"
    unfolding execute_def schedule_at_retained_state_def Let_def
    using scheduled_service_keeps_a_recorded_primary_decision[OF before] by simp
  show ?case using tail_induction[OF next_decision] unfolding head by simp
qed

end

end
