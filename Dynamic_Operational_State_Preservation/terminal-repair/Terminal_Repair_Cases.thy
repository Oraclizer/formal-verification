theory Terminal_Repair_Cases
  imports Terminal_Repair_View DOSP_Recovery.Recovery_Examples REOS_Rollback_Examples.Rollback_Examples
begin

definition terminal_recovery_start :: "nat recovery_state" where
  "terminal_recovery_start = repair_start\<lparr>active_domains := {1}, primary_record := 13,
    replica := (\<lambda>_. 8), irreversible_facts := {77}\<rparr>"

definition terminal_recovery_end :: "nat recovery_state" where
  "terminal_recovery_end = install_replica terminal_recovery_start 7 1"

lemma linked_terminal_fixture:
  "terminal_cell_view with_finality 77 receipt terminal terminal_recovery_start"
  by (auto simp: terminal_cell_view_def terminal_recovery_start_def repair_start_def
      with_finality_def fixture_setup decision_rules dom_def)

lemma terminal_fixture_installs:
  "recovery_step {} {} terminal_recovery_start (Apply_Repair 7 20)
    (Accepted (Installed 7 1 20)) terminal_recovery_end"
  unfolding terminal_recovery_end_def
  by (rule recovery_step.Ordinary_Repair) (simp_all add: terminal_recovery_start_def repair_start_def)

theorem installed_terminal_fixture_agrees_in_both_models:
  "rollback_step with_finality (Repair_From_Record 77 1) (Internal (Repaired_From_Record 77 1)) replica_repaired \<and>
    terminal_cell_view replica_repaired 77 receipt terminal terminal_recovery_end \<and>
    replica terminal_recovery_end 1 = 13 \<and> replica terminal_recovery_end 2 = 8 \<and>
    completion_log terminal_recovery_end = {7} \<and> pending_ids terminal_recovery_end = {}"
proof -
  from terminal_replay_matches_fv14_installation[OF linked_terminal_fixture terminal_fixture_installs]
  obtain updated where replay:
    "rollback_step with_finality (Repair_From_Record 77 1) (Internal (Repaired_From_Record 77 1)) updated"
    and bound: "terminal_cell_view updated 77 receipt terminal terminal_recovery_end"
    by blast
  have expected: "rollback_step with_finality (Repair_From_Record 77 1)
    (Internal (Repaired_From_Record 77 1)) replica_repaired"
    by (rule primary_finality_and_rollback_controls(8))
  have "updated = replica_repaired"
    using replay expected by (simp add: rollback_step_def)
  with bound expected show ?thesis
    by (simp add: terminal_recovery_end_def install_replica_def terminal_recovery_start_def repair_start_def pending_ids_def)
qed

lemma incorrect_payload_breaks_the_actual_record_binding:
  "\<not> terminal_cell_view with_finality 77 receipt terminal (terminal_recovery_start\<lparr>primary_record := 2\<rparr>)"
  by (simp add: terminal_cell_view_def receipt_def)

lemma record_repair_does_not_authorize_stale_fv14_sequence:
  "rollback_step with_finality (Repair_From_Record 77 1) (Internal (Repaired_From_Record 77 1)) replica_repaired \<and>
    (\<forall>t. \<not> recovery_step {} {} terminal_recovery_start (Apply_Repair 7 19) (Accepted (Installed 7 1 19)) t)"
proof -
  have blocked: "\<And>t. \<not> recovery_step {} {} terminal_recovery_start (Apply_Repair 7 19) (Accepted (Installed 7 1 19)) t"
  proof
    fix t
    assume step: "recovery_step {} {} terminal_recovery_start (Apply_Repair 7 19) (Accepted (Installed 7 1 19)) t"
    from actual_install_uses_primary_record[OF step] have "19 = primary_sequence terminal_recovery_start" by simp
    then show False by (simp add: terminal_recovery_start_def repair_start_def)
  qed
  with primary_finality_and_rollback_controls(8) show ?thesis by simp
qed

lemma replay_of_installed_record_cannot_complete_job_again:
  defines "again \<equiv> Repair_From_Record 77 1"
  shows "rollback_step replica_repaired again (Internal (Repaired_From_Record 77 1)) (snd (execute replica_repaired again)) \<and>
    (\<forall>a sequence t. \<not> recovery_step {} {} terminal_recovery_end a (Accepted (Installed 7 1 sequence)) t)"
proof -
  have "terminal_records replica_repaired 77 = Some receipt"
    using installed_terminal_fixture_agrees_in_both_models by (simp add: terminal_cell_view_def)
  then have replay: "rollback_step replica_repaired again (Internal (Repaired_From_Record 77 1))
      (snd (execute replica_repaired again))"
    by (simp add: again_def rollback_step_def)
  have "7 \<notin> pending_ids terminal_recovery_end"
    using installed_terminal_fixture_agrees_in_both_models by blast
  then show ?thesis using replay by (auto intro!: installed_requires_the_bound_job)
qed

end
