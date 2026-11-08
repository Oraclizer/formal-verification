theory Promotion_Trace_Retention
  imports Promotion_Trace_Service
begin

lemma retained_call_source_is_the_actual_product_source:
  "retained_source (capture_retained_product s) = capture_retained_source (identity_source s)"
  by (simp add: capture_retained_product_def identity_source_def regulated_read_world_def observed_product_source_def Let_def)

lemma reopened_source_call_genesis:
  "call_genesis (actual_product_calls (reopen_retained_product connection retained)) =
    retained_genesis (retained_source retained)"
  by (simp add: actual_product_calls_def recovery_projection_supplies_the_exact_source reopen_retained_source_def)

fun run_product_action_word where
  "run_product_action_word execute [] retained = retained"
| "run_product_action_word execute ((connection, action) # rest) retained =
    run_product_action_word execute rest (fst (execute connection action retained))"

context source_attestation
begin

definition retained_source_replay_valid where
  "retained_source_replay_valid retained \<longleftrightarrow>
    finality_calls.authority_replay_contract (product_calls (reopen_retained_source Authority_Connected (retained_source retained)))"

lemma retained_source_replay_valid_of_capture [simp]:
  "retained_source_replay_valid (capture_retained_product s) =
    finality_calls.authority_replay_contract (actual_product_calls s)"
  by (simp add: retained_source_replay_valid_def retained_call_source_is_the_actual_product_source
    actual_product_calls_def finality_calls.authority_replay_contract_def
    reopen_retained_source_def capture_retained_source_def Let_def)

lemma valid_reopened_call_replay:
  "retained_source_replay_valid retained =
    finality_calls.authority_replay_contract (actual_product_calls (reopen_retained_product connection retained))"
  by (simp add: retained_source_replay_valid_def actual_product_calls_def recovery_projection_supplies_the_exact_source
      finality_calls.authority_replay_contract_def reopen_retained_source_def)

lemma scheduled_product_step_preserves_exact_authority_replay:
  assumes "retained_source_replay_valid retained"
  shows "retained_source_replay_valid (fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection action retained))"
proof -
  let ?s = "reopen_retained_product connection retained"
  let ?step = "fst (schedule_service_step directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action ?s)"
  have valid: "finality_calls.authority_replay_contract (actual_product_calls ?s)"
    using assms valid_reopened_call_replay by blast
  have segment: "source_segment (actual_product_calls ?s) (actual_product_calls ?step)"
    by (rule every_scheduled_service_action_has_a_public_source_segment)
  obtain word where actual: "actual_product_calls ?step = finality_calls.run_calls word (actual_product_calls ?s)"
    using segment unfolding source_segment_def by blast
  have "finality_calls.authority_replay_contract (actual_product_calls ?step)"
    unfolding actual by (rule public_word_preserves_read_replay_contract[OF valid])
  then show ?thesis by (simp add: schedule_at_retained_state_def Let_def)
qed

lemma scheduled_product_step_keeps_the_fixed_public_genesis:
  "retained_genesis (retained_source (fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection action retained))) = retained_genesis (retained_source retained)"
proof -
  let ?s = "reopen_retained_product connection retained"
  let ?step = "fst (schedule_service_step directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action ?s)"
  have segment: "source_segment (actual_product_calls ?s) (actual_product_calls ?step)"
    by (rule every_scheduled_service_action_has_a_public_source_segment)
  obtain word where actual: "actual_product_calls ?step = finality_calls.run_calls word (actual_product_calls ?s)"
    using segment unfolding source_segment_def by blast
  have genesis: "call_genesis (actual_product_calls ?step) = retained_genesis (retained_source retained)"
    by (simp add: actual reopened_source_call_genesis)
  show ?thesis by (simp add: schedule_at_retained_state_def Let_def retained_call_source_is_the_actual_product_source
    capture_retained_source_def actual_product_calls_def[symmetric] genesis)
qed

lemma every_product_word_keeps_its_actual_genesis_and_authority_replay:
  fixes execute :: "authority_connection \<Rightarrow> 'token retained_service_action \<Rightarrow> retained_product \<Rightarrow> retained_product \<times> scheduled_service_reply"
    and directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
  defines "execute \<equiv> schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack"
  assumes valid_initial: "retained_source_replay_valid initial"
  shows "retained_source_replay_valid (run_product_action_word execute actions initial) \<and>
    retained_genesis (retained_source (run_product_action_word execute actions initial)) = retained_genesis (retained_source initial)"
  using valid_initial
proof (induction actions arbitrary: initial)
  case Nil
  then show ?case by simp
next
  case (Cons first rest)
  note tail_induction = Cons(1)
  obtain connection action where head: "first = (connection, action)" by (cases first)
  let ?after = "fst (execute connection action initial)"
  have valid: "retained_source_replay_valid ?after"
    unfolding execute_def by (rule scheduled_product_step_preserves_exact_authority_replay[OF Cons.prems])
  have genesis: "retained_genesis (retained_source ?after) = retained_genesis (retained_source initial)"
    unfolding execute_def by (rule scheduled_product_step_keeps_the_fixed_public_genesis)
  show ?case using tail_induction[OF valid] genesis unfolding head by simp
qed

end

end
