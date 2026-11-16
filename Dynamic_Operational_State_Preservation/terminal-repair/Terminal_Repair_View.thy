theory Terminal_Repair_View
  imports DOSP_Recovery.Domain_Recovery REOS_Rollback.Rollback_Contracts
begin

definition terminal_cell_view ::
  "rollback_state \<Rightarrow> nat \<Rightarrow> terminal_record \<Rightarrow> ledger_cell \<Rightarrow> nat recovery_state \<Rightarrow> bool"
where
  "terminal_cell_view authority key p cell s \<longleftrightarrow>
    terminal_records authority key = Some p \<and>
    cell \<in> terminal_cells p \<and>
    primary_record s = terminal_value p cell \<and>
    irreversible_facts s = dom (terminal_records authority) \<and>
    (\<forall>d. replica s d = replica_value authority d cell)"

lemma installed_job_and_primary:
  assumes "recovery_step grants governance s a (Accepted (Installed job domain sequence)) t"
  shows "primary_record t = primary_record s"
    and "work_owner t = (work_owner s)(job := None)"
    and "completion_log t = insert job (completion_log s)"
  using assms by (cases rule: recovery_step.cases; simp add: install_replica_def)+

theorem terminal_replay_matches_fv14_installation:
  assumes binding: "terminal_cell_view authority key p cell s"
    and install: "recovery_step grants governance s a (Accepted (Installed job domain sequence)) t"
  obtains updated where
    "rollback_step authority (Repair_From_Record key domain) (Internal (Repaired_From_Record key domain)) updated"
    "terminal_cell_view updated key p cell t"
    "terminal_records updated = terminal_records authority"
    "cell_value updated = cell_value authority"
    "replica_value updated domain cell = primary_record s"
    "preserves_outside (\<lambda>x. replica_value x domain) (terminal_cells p) authority updated"
    "completion_log t = insert job (completion_log s)"
    "work_owner t = (work_owner s)(job := None)"
proof -
  from binding have stored: "terminal_records authority key = Some p"
    and inside: "cell \<in> terminal_cells p"
    and payload: "primary_record s = terminal_value p cell"
    and ids: "irreversible_facts s = dom (terminal_records authority)"
    and projected: "\<And>d. replica s d = replica_value authority d cell"
    by (auto simp: terminal_cell_view_def)
  let ?updated = "authority\<lparr>replica_value := (replica_value authority)(domain :=
    update_cells (terminal_cells p) (terminal_value p) (replica_value authority domain))\<rparr>"
  have replay: "rollback_step authority (Repair_From_Record key domain)
      (Internal (Repaired_From_Record key domain)) ?updated"
    using stored by (simp add: rollback_step_def)
  from Rollback_Contracts.finality_repair_matches_record[OF replay] obtain q where
    old: "terminal_records authority key = Some q"
    and installed: "\<forall>x \<in> terminal_cells q. replica_value ?updated domain x = terminal_value q x"
    and frame: "preserves_outside (\<lambda>x. replica_value x domain) (terminal_cells q) authority ?updated"
    and ledger: "cell_value ?updated = cell_value authority"
    and records: "terminal_records ?updated = terminal_records authority" by blast
  have record_eq: "q = p" using stored old by simp
  have installed_payload: "replica_value ?updated domain cell = primary_record s"
    using installed record_eq inside payload by simp
  have view_installed: "replica t domain = primary_record s"
    and view_frame: "preserves_outside replica {domain} s t"
    using actual_install_uses_primary_record[OF install] by auto
  have views: "\<And>d. replica t d = replica_value ?updated d cell"
  proof -
    fix d
    show "replica t d = replica_value ?updated d cell"
    proof (cases "d = domain")
      case True
      then show ?thesis using installed_payload view_installed by simp
    next
      case False
      then have "replica t d = replica s d"
        using view_frame by (simp add: preserves_outside_def)
      with False show ?thesis by (simp add: projected)
    qed
  qed
  have still_bound: "terminal_cell_view ?updated key p cell t"
    using records stored inside payload ids views installed_job_and_primary(1)[OF install]
      recovery_never_changes_irreversible_facts[OF install]
    by (simp add: terminal_cell_view_def)
  from record_eq frame have exact_frame:
    "preserves_outside (\<lambda>x. replica_value x domain) (terminal_cells p) authority ?updated" by simp
  show thesis
    by (rule that[OF replay still_bound records ledger installed_payload exact_frame
          installed_job_and_primary(3)[OF install] installed_job_and_primary(2)[OF install]])
qed

lemma installed_requires_the_bound_job:
  assumes "job \<notin> pending_ids s"
  shows "\<not> recovery_step grants governance s a (Accepted (Installed job domain sequence)) t"
proof
  assume step: "recovery_step grants governance s a (Accepted (Installed job domain sequence)) t"
  from actual_install_uses_primary_record[OF step] have "work_owner s job = Some domain" by simp
  with assms show False by (simp add: pending_ids_def dom_def)
qed

end
