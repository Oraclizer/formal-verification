theory Quiet_Run_Projection_Harness
  imports Quiet_Run_Examples
begin

definition comparison_replica :: "nat \<Rightarrow> nat" where
  "comparison_replica = update_cells (active_domains repair_start)
    (\<lambda>_. primary_record repair_start) (replica repair_start)"

lemma departed_copy_matches_comparison:
  "comparison_replica 1 = replica leave_after_repair 1"
  by (simp add: comparison_replica_def update_cells_def leave_after_repair_def
    repair_end_def repair_start_def install_replica_def)

end
