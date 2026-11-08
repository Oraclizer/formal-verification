theory Promotion_Call_Ids
  imports Promotion_Financial
begin

definition retained_call_ids_exact where
  "retained_call_ids_exact retained \<longleftrightarrow>
    authority_cache_contract (product_calls (reopen_retained_source Authority_Connected (retained_source retained)))"

lemma retained_call_ids_exact_of_capture [simp]:
  "retained_call_ids_exact (capture_retained_product s) = authority_cache_contract (actual_product_calls s)"
  by (simp add: retained_call_ids_exact_def retained_call_source_is_the_actual_product_source actual_product_calls_def
      authority_cache_contract_def reopen_retained_source_def capture_retained_source_def Let_def)

lemma reopened_has_the_retained_call_id_contract:
  "retained_call_ids_exact retained = authority_cache_contract (actual_product_calls (reopen_retained_product connection retained))"
  by (simp add: retained_call_ids_exact_def actual_product_calls_def recovery_projection_supplies_the_exact_source
      authority_cache_contract_def reopen_retained_source_def)

lemma initialized_product_has_exact_retained_call_ids:
  "retained_call_ids_exact (initial_promotable_product balances regulatory contexts durable target provider)"
  by (simp add: initial_promotable_product_def actual_product_calls_def identity_source_def regulated_read_world_def
      observed_product_source_def initial_regulated_product_def initial_governed_world_def initial_legal_world_def
      initial_product_reads_def initial_exact_product_def initial_settlement_world_def initial_origin_world_def
      initial_outcome_world_def initial_lock_world_def initial_call_machine_def authority_cache_contract_def)

context source_attestation
begin

lemma a_public_segment_cannot_duplicate_the_effect_for_a_call_id:
  assumes "authority_cache_contract before" "source_segment before after"
  shows "authority_cache_contract after"
proof -
  obtain word where actual: "after = finality_calls.run_calls word before"
    using assms(2) unfolding source_segment_def by blast
  show ?thesis unfolding actual using assms(1)
    by (induction word arbitrary: before) (auto intro: finality_calls.authority_cache_contract_step)
qed

lemma the_actual_scheduled_step_preserves_retained_call_id_uniqueness:
  assumes "retained_call_ids_exact retained"
  shows "retained_call_ids_exact (fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack connection action retained))"
proof -
  let ?s = "reopen_retained_product connection retained"
  let ?step = "fst (schedule_service_step directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action ?s)"
  have valid: "authority_cache_contract (actual_product_calls ?s)"
    by (rule reopened_has_the_retained_call_id_contract[THEN iffD1, OF assms])
  have segment: "source_segment (actual_product_calls ?s) (actual_product_calls ?step)"
    by (rule every_scheduled_service_action_has_a_public_source_segment)
  show ?thesis using a_public_segment_cannot_duplicate_the_effect_for_a_call_id[OF valid segment]
    by (simp add: schedule_at_retained_state_def Let_def)
qed

theorem every_actual_product_trace_executes_each_authoritative_call_id_at_most_once:
  fixes execute :: "authority_connection \<Rightarrow> 'token retained_service_action \<Rightarrow> retained_product \<Rightarrow> retained_product \<times> scheduled_service_reply"
    and directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
  defines "execute \<equiv> schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack"
  assumes valid_initial: "retained_call_ids_exact initial"
  shows "distinct (authority_execution_ids (retained_log (retained_source (run_product_action_word execute actions initial))))"
proof -
  have "retained_call_ids_exact (run_product_action_word execute actions initial)"
    using valid_initial
  proof (induction actions arbitrary: initial)
    case Nil
    then show ?case by simp
  next
    case (Cons first rest)
    note tail_induction = Cons(1)
    obtain connection action where head: "first = (connection, action)" by (cases first)
    have next_valid: "retained_call_ids_exact (fst (execute connection action initial))"
      unfolding execute_def by (rule the_actual_scheduled_step_preserves_retained_call_id_uniqueness[OF Cons.prems])
    show ?case using tail_induction[OF next_valid] unfolding head by simp
  qed
  then show ?thesis by (simp add: retained_call_ids_exact_def authority_cache_contract_def reopen_retained_source_def)
qed

end

end
