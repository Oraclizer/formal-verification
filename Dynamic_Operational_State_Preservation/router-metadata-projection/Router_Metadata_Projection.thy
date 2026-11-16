theory Router_Metadata_Projection
  imports DOSP_Degree.Degree_Examples
begin

theorem promoted_fixture_has_distinct_ticket_outcomes_on_one_path:
  "chosen_path old_plan = chosen_path (promoted_metadata 9 5)"
  "cutover_step two_origin_policy {(9,5)} promoted
      (Commit_Binding 2 old_plan 2 1 12 True) (Rejected Stale_Ticket) promoted"
  "cutover_step two_origin_policy {(9,5)} promoted
      (Commit_Binding 2 (promoted_metadata 9 5) 2 1 12 True)
      (Accepted Binding_Committed) new_committed"
  by (simp add: old_plan_def promoted_metadata_def,
      rule old_metadata_rejected_after_boundary, rule new_commit_admitted)

corollary chosen_path_cannot_reproduce_both_ticket_outcomes:
  "\<not> (\<exists>classify :: operational_level \<Rightarrow> cutover_result.
    classify (chosen_path old_plan) = Rejected Stale_Ticket \<and>
    classify (chosen_path (promoted_metadata 9 5)) = Accepted Binding_Committed)"
  using promoted_fixture_has_distinct_ticket_outcomes_on_one_path(1) by auto

end
