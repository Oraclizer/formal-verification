theory EAB_Dynamic_Cases
  imports EAB_Adapter_Cases
begin

definition changing_domains :: "nat routing_grants" where
  "changing_domains = {(Join_Domain 6 9, 2, 10), (Leave_Domain 2 6, 3, 11)}"

definition after_join :: "nat recovery_state" where
  "after_join = repair_fixture\<lparr>active_domains := insert 6 (active_domains repair_fixture),
    route_epoch := 2, work_owner := (work_owner repair_fixture)(9 := Some 6)\<rparr>"

definition after_handoff :: "nat recovery_state" where
  "after_handoff = after_join\<lparr>active_domains := active_domains after_join - {2}, route_epoch := 3,
    work_owner := carry_owner 2 6 (work_owner after_join)\<rparr>"

theorem membership_handoff_preserves_the_bound_primary_job:
  defines "authority \<equiv> source_authority (fst metered_fixture_result)"
  shows "recovery_step changing_domains {} repair_fixture (Activate (Join_Domain 6 9) 2 10 10)
      (transition_result.Accepted (Joined 6 9)) after_join" (is ?Join)
    and "recovery_step changing_domains {} after_join (Activate (Leave_Domain 2 6) 3 11 11)
      (transition_result.Accepted (Left 2 6)) after_handoff" (is ?Leave)
    and "receipt_repair_step changing_domains {} authority fixture_receipt after_handoff (Apply_Repair 8 50)
      (transition_result.Accepted (Installed 8 6 50)) (install_replica after_handoff 8 6)"
    and "replica (install_replica after_handoff 8 6) 2 = replica repair_fixture 2"
proof -
  show join: ?Join
    by (unfold after_join_def, rule recovery_step.Join_Route)
      (simp_all add: changing_domains_def current_grant_def fresh_work_def repair_fixture_def)
  show leave: ?Leave
    by (unfold after_handoff_def, rule recovery_step.Leave_Route)
      (simp_all add: after_join_def changing_domains_def current_grant_def repair_fixture_def)
  have "primary_receipt_matches authority fixture_receipt repair_fixture"
    using the_metered_published_transfer_reaches_replica_install
    by (simp add: authority_def receipt_repair_step_def split: if_splits)
  then have bound: "primary_receipt_matches authority fixture_receipt after_handoff"
    using recovery_keeps_the_primary_receipt[OF join]
      recovery_keeps_the_primary_receipt[OF leave] by blast
  have actual: "recovery_step changing_domains {} after_handoff (Apply_Repair 8 50)
      (transition_result.Accepted (Installed 8 6 50)) (install_replica after_handoff 8 6)"
    by (rule recovery_step.Ordinary_Repair)
      (simp_all add: after_handoff_def after_join_def repair_fixture_def carry_owner_def)
  show "receipt_repair_step changing_domains {} authority fixture_receipt after_handoff (Apply_Repair 8 50)
      (transition_result.Accepted (Installed 8 6 50)) (install_replica after_handoff 8 6)"
    using bound actual by (simp add: receipt_repair_step_def)
  show "replica (install_replica after_handoff 8 6) 2 = replica repair_fixture 2"
    by (simp add: install_replica_def after_handoff_def after_join_def)
qed

abbreviation repaired_first :: "nat recovery_state" where
  "repaired_first \<equiv> install_replica after_handoff 8 6"

abbreviation repaired_both :: "nat recovery_state" where
  "repaired_both \<equiv> install_replica repaired_first 9 6"

theorem the_second_job_must_finish_before_ordinary_trade:
  defines "authority \<equiv> source_authority (fst metered_fixture_result)"
  shows "recovery_step changing_domains {} repaired_first (Ordinary_Trade 10)
      (transition_result.Rejected Recovery_Blocks_Trade) repaired_first"
    and "receipt_repair_step changing_domains {} authority fixture_receipt repaired_first (Apply_Repair 9 50)
      (transition_result.Accepted (Installed 9 6 50)) repaired_both"
    and "pending_ids repaired_both = {}"
    and "completion_log repaired_both = {8, 9}"
    and "\<forall>d\<in>active_domains repaired_both. replica repaired_both d = primary_record repaired_both"
    and "recovery_step changing_domains {} repaired_both (Ordinary_Trade 10)
      (transition_result.Accepted (Traded 10)) repaired_both"
proof -
  have "work_owner repaired_first 9 = Some 6"
    by (simp add: after_join_def after_handoff_def install_replica_def carry_owner_def repair_fixture_def)
  then have "9 \<in> pending_ids repaired_first" by (auto simp: pending_ids_def intro: domI)
  then have unfinished: "pending_ids repaired_first \<noteq> {}" by blast
  show "recovery_step changing_domains {} repaired_first (Ordinary_Trade 10)
      (transition_result.Rejected Recovery_Blocks_Trade) repaired_first"
    by (rule recovery_step.Refuse_Trade) (simp add: unfinished)
  have matched: "primary_receipt_matches authority fixture_receipt after_handoff"
    using membership_handoff_preserves_the_bound_primary_job(3)
    by (simp add: authority_def receipt_repair_step_def split: if_splits)
  have "primary_receipt_matches authority fixture_receipt repaired_first"
    using matched by (simp add: primary_receipt_matches_def install_replica_def)
  moreover have "recovery_step changing_domains {} repaired_first (Apply_Repair 9 50)
      (transition_result.Accepted (Installed 9 6 50)) repaired_both"
    by (rule recovery_step.Ordinary_Repair)
      (simp_all add: after_join_def after_handoff_def repair_fixture_def carry_owner_def install_replica_def)
  ultimately show "receipt_repair_step changing_domains {} authority fixture_receipt repaired_first (Apply_Repair 9 50)
      (transition_result.Accepted (Installed 9 6 50)) repaired_both"
    by (simp add: receipt_repair_step_def)
  show closed: "pending_ids repaired_both = {}"
    by (auto simp: pending_ids_def dom_def after_join_def after_handoff_def install_replica_def
      carry_owner_def repair_fixture_def split: if_splits)
  show "completion_log repaired_both = {8, 9}"
    by (simp add: after_join_def after_handoff_def install_replica_def repair_fixture_def insert_commute)
  show "\<forall>d\<in>active_domains repaired_both. replica repaired_both d = primary_record repaired_both"
    by (auto simp: after_join_def after_handoff_def install_replica_def repair_fixture_def)
  show "recovery_step changing_domains {} repaired_both (Ordinary_Trade 10)
      (transition_result.Accepted (Traded 10)) repaired_both"
    by (rule recovery_step.Admit_Trade[OF closed])
      (simp add: after_join_def after_handoff_def install_replica_def repair_fixture_def)
qed

end
