theory Degree_Examples
  imports Promotion_Cutover
begin

definition two_origin_policy :: "nat flow_policy" where
  "two_origin_policy = \<lparr>hub = 0, domain_set = {0,1,2}, allowed_sources = {1,2}\<rparr>"

definition old_plan :: cutover_metadata where
  "old_plan = \<lparr>required_level = Coupled, chosen_path = Atomic, meter_version = 4, cutover_epoch = 8\<rparr>"

definition cutover_start :: "nat cutover_state" where
  "cutover_start =
    \<lparr>route_metadata = old_plan,
     binding_state = \<lparr>committed = (\<lambda>_. 0), observation_cache = (\<lambda>_. 0)\<rparr>,
     billing_history = [], unreconciled_soft_write = False\<rparr>"

definition old_committed :: "nat cutover_state" where
  "old_committed = cutover_start\<lparr>
    binding_state := fst (evaluate_flow two_origin_policy Atomic True (binding_state cutover_start) (Commit_From 1 2 10)),
    billing_history := billing_history cutover_start @ [billing_record 1 old_plan (Commit_From (1::nat) 2 10)]\<rparr>"

definition promoted :: "nat cutover_state" where
  "promoted = old_committed\<lparr>route_metadata := promoted_metadata 9 5\<rparr>"

definition new_committed :: "nat cutover_state" where
  "new_committed = promoted\<lparr>
    binding_state := fst (evaluate_flow two_origin_policy Atomic True (binding_state promoted) (Commit_From 2 1 12)),
    billing_history := billing_history promoted @
      [billing_record 2 (promoted_metadata 9 5) (Commit_From (2::nat) 1 12)]\<rparr>"

lemma old_commit_admitted:
  "cutover_step two_origin_policy {(9,5)} cutover_start (Commit_Binding 1 old_plan 1 2 10 True)
    (Accepted Binding_Committed) old_committed"
  unfolding old_committed_def
  by (rule cutover_step.Commit)
     (simp_all add: can_commit_def two_origin_policy_def old_plan_def cutover_start_def flow_step_def)

lemma boundary_promotion_admitted:
  "cutover_step two_origin_policy {(9,5)} old_committed (Confirm_Promotion 9 5) (Accepted Promotion_Finalized) promoted"
  unfolding promoted_def
  by (rule cutover_step.Promote)
     (simp add: promotion_allowed_def old_committed_def cutover_start_def old_plan_def)

lemma old_metadata_rejected_after_boundary:
  "cutover_step two_origin_policy {(9,5)} promoted (Commit_Binding 2 old_plan 2 1 12 True)
    (Rejected Stale_Ticket) promoted"
  by (rule cutover_step.Refuse_Stale) (simp add: promoted_def promoted_metadata_def old_plan_def)

lemma new_commit_admitted:
  "cutover_step two_origin_policy {(9,5)} promoted (Commit_Binding 2 (promoted_metadata 9 5) 2 1 12 True)
    (Accepted Binding_Committed) new_committed"
  unfolding new_committed_def
  by (rule cutover_step.Commit)
     (simp_all add: can_commit_def two_origin_policy_def promoted_def promoted_metadata_def
       old_committed_def cutover_start_def billing_record_def flow_step_def)

theorem cutover_bills_old_and_new_requirement_without_repricing:
  "map billing_level (billing_history new_committed) = [Coupled, Atomic] \<and>
   map billing_version (billing_history new_committed) = [4,5] \<and>
   map billing_epoch (billing_history new_committed) = [8,9] \<and>
   map domains_written (billing_history new_committed) = [2,2]"
  by (simp add: new_committed_def promoted_def old_committed_def cutover_start_def
    billing_record_def old_plan_def promoted_metadata_def)

definition soft_start :: "nat cutover_state" where
  "soft_start = cutover_start\<lparr>route_metadata := old_plan\<lparr>chosen_path := Coupled\<rparr>\<rparr>"

definition partial_commit :: "nat cutover_state" where
  "partial_commit = soft_start\<lparr>
    binding_state := fst (evaluate_flow two_origin_policy Coupled False (binding_state soft_start) (Commit_From 1 2 10)),
    unreconciled_soft_write := True\<rparr>"

lemma partial_soft_commit_occurs:
  "cutover_step two_origin_policy {(9,5)} soft_start
    (Commit_Binding 1 (route_metadata soft_start) 1 2 10 False)
    (Operational_Failure Partial_Write) partial_commit"
proof -
  have "cutover_step two_origin_policy {(9,5)} soft_start
    (Commit_Binding 1 (route_metadata soft_start) 1 2 10 False)
    (Operational_Failure Partial_Write)
    (soft_start\<lparr>binding_state := fst (evaluate_flow two_origin_policy Coupled False (binding_state soft_start)
        (Commit_From 1 2 10)), unreconciled_soft_write := unreconciled_soft_write soft_start \<or> Partial_Write = Partial_Write\<rparr>)"
    by (rule cutover_step.Binding_Failed[where a="Commit_From 1 2 10"])
       (simp_all add: can_commit_def two_origin_policy_def soft_start_def cutover_start_def old_plan_def flow_step_def)
  then show ?thesis by (simp add: partial_commit_def)
qed

theorem actual_partial_commit_refuses_the_promotion:
  "cutover_step two_origin_policy {(9,5)} partial_commit (Confirm_Promotion 9 5)
    (Rejected Ineligible_Promotion) partial_commit"
proof -
  have "unreconciled_soft_write partial_commit" by (simp add: partial_commit_def)
  then show ?thesis using unsafe_soft_effect_blocks_promotion by blast
qed

end
