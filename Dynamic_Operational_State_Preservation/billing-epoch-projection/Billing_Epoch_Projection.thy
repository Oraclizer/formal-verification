theory Billing_Epoch_Projection
  imports DOSP_Degree.Degree_Examples
begin

definition second_commit_without_promotion :: "nat cutover_state" where
  "second_commit_without_promotion =
    old_committed\<lparr>
      binding_state := fst (evaluate_flow two_origin_policy Atomic True
        (binding_state old_committed) (Commit_From 2 1 12)),
      billing_history := billing_history old_committed @
        [billing_record 2 old_plan (Commit_From (2::nat) 1 12)]\<rparr>"

lemma second_commit_before_promotion_admitted:
  "cutover_step two_origin_policy {(9,5)} old_committed (Commit_Binding 2 old_plan 2 1 12 True)
    (Accepted Binding_Committed) second_commit_without_promotion"
  unfolding second_commit_without_promotion_def
  by (rule cutover_step.Commit)
     (simp_all add: can_commit_def two_origin_policy_def old_committed_def cutover_start_def
       old_plan_def billing_record_def flow_step_def)

theorem distinct_commits_can_share_one_cutover_epoch:
  "cutover_step two_origin_policy {(9,5)} cutover_start (Commit_Binding 1 old_plan 1 2 10 True)
    (Accepted Binding_Committed) old_committed"
  "cutover_step two_origin_policy {(9,5)} old_committed (Commit_Binding 2 old_plan 2 1 12 True)
    (Accepted Binding_Committed) second_commit_without_promotion"
  "map binding_id (billing_history second_commit_without_promotion) = [1,2]"
  "map billing_epoch (billing_history second_commit_without_promotion) = [8,8]"
  by (rule old_commit_admitted, rule second_commit_before_promotion_admitted,
      simp_all add: second_commit_without_promotion_def old_committed_def cutover_start_def
        billing_record_def old_plan_def)

corollary cutover_stamps_cannot_equal_two_distinct_settlement_epochs:
  assumes "first_epoch \<noteq> second_epoch"
  shows "map billing_epoch (billing_history second_commit_without_promotion) \<noteq>
    [first_epoch, second_epoch]"
  using assms distinct_commits_can_share_one_cutover_epoch(4) by auto

lemma partial_write_does_not_append_a_committed_cycle:
  "billing_history partial_commit = billing_history soft_start"
  by (rule commit_failure_keeps_billing_history[OF partial_soft_commit_occurs])

end
