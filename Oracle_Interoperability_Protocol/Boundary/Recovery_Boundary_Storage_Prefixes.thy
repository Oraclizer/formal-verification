theory Recovery_Boundary_Storage_Prefixes
  imports Recovery_Boundary_Storage_Dilemma
begin

text \<open>Arbitrary-prefix invariants supply the current stored cut and saved-copy premises of the
  storage-only recovery dilemma, using the unchanged disk-only transition.\<close>

definition disk_history_is_addressed where
  "disk_history_is_addressed digest s \<longleftrightarrow>
    records_are_at_their_own_addresses digest (sys_disk s) \<and>
    (\<forall>disk \<in> set (ghost_disks s). records_are_at_their_own_addresses digest disk) \<and>
    sys_disk s \<in> set (ghost_disks s)"

lemma disk_only_step_keeps_addressed_history:
  assumes inv: "disk_history_is_addressed digest s"
  shows "disk_history_is_addressed digest (disk_only_step accept step digest profile event s)"
proof (cases event)
  case (Ask c a)
  then show ?thesis using inv
    by (auto simp: disk_history_is_addressed_def request_effect_def stage_step_def split: option.splits if_splits)
next
  case (Flush_Record i)
  have correct: "records_are_at_their_own_addresses digest (flush_commit_record digest entry (sys_disk s))"
    for entry
    using inv complete_record_flush_keeps_address_correctness
      unfolding disk_history_is_addressed_def by blast
  show ?thesis using inv Flush_Record correct
    by (auto simp: disk_history_is_addressed_def flush_effect_def)
next
  case (Publish_Head i)
  have correct: "records_are_at_their_own_addresses digest
      (publish_recovery_head digest expected entry (sys_disk s))" for expected entry
    using inv head_publication_keeps_address_correctness unfolding disk_history_is_addressed_def by blast
  show ?thesis using inv Publish_Head correct
    by (auto simp: disk_history_is_addressed_def disk_only_publish_def Let_def)
next
  case (Select_Head i)
  then show ?thesis using inv by simp
next
  case (Issue_Reply i)
  then show ?thesis using inv by (simp add: disk_history_is_addressed_def disk_only_issue_def Let_def)
next
  case Repair_Head
  then show ?thesis using inv by simp
next
  case Crash_Endpoint
  then show ?thesis using inv by (simp add: disk_history_is_addressed_def)
next
  case (Reopen_Endpoint attachment)
  then show ?thesis using inv by (simp add: disk_history_is_addressed_def disk_only_reopen_def)
next
  case (Roll_Back_Disk j)
  have saved: "records_are_at_their_own_addresses digest (ghost_disks s ! j) \<and>
      ghost_disks s ! j \<in> set (ghost_disks s)" if "j < length (ghost_disks s)"
    using inv nth_mem[OF that] unfolding disk_history_is_addressed_def by blast
  show ?thesis using inv Roll_Back_Disk saved
    by (auto simp: disk_history_is_addressed_def roll_back_disk_effect_def)
next
  case (Roll_Back_Witness j)
  then show ?thesis using inv by simp
qed

lemma disk_only_prefix_has_addressed_history:
  "disk_history_is_addressed digest
    (fold (disk_only_step accept step digest profile) events (genesis_system digest profile R0))"
proof -
  have start: "disk_history_is_addressed digest (genesis_system digest profile R0)"
    by (simp add: disk_history_is_addressed_def genesis_system_def genesis_has_correct_record_addresses)
  have preserves: "disk_history_is_addressed digest s \<Longrightarrow>
      disk_history_is_addressed digest (fold (disk_only_step accept step digest profile) events s)" for s
    by (induction events arbitrary: s) (auto intro: disk_only_step_keeps_addressed_history)
  show ?thesis by (rule preserves[OF start])
qed

definition disk_only_cut_invariant where
  "disk_only_cut_invariant digest profile s \<longleftrightarrow>
    (\<forall>h R. sys_endpoint s = Some (h, R) \<longrightarrow>
       stored_cut_is_current digest profile h R (sys_disk s)) \<and>
    (sys_endpoint s = None \<longrightarrow> sys_staged s = []) \<and>
    (\<forall>p \<in> set (sys_staged s). image_profile (staged_record p) = profile)"

lemma flushing_keeps_a_current_stored_cut:
  "stored_cut_is_current digest profile h R disk \<Longrightarrow>
    stored_cut_is_current digest profile h R (flush_commit_record digest candidate disk)"
  by (auto simp: stored_cut_is_current_def flush_commit_record_def Let_def)

lemma disk_only_publication_keeps_the_live_cut:
  assumes inv: "disk_only_cut_invariant digest profile s"
  shows "disk_only_cut_invariant digest profile (disk_only_publish digest i s)"
proof -
  let ?p = "sys_staged s ! i"
  let ?record = "staged_record ?p"
  let ?next = "head_for_record digest ?record"
  show ?thesis
  proof (cases "i < length (sys_staged s) \<and> committed_head (sys_disk s) = Some (staged_base ?p) \<and>
      candidate_extends_head (Some (staged_base ?p)) ?record \<and> flushed_records (sys_disk s) ?next = Some ?record")
    case False
    then have "disk_only_publish digest i s = s" by (auto simp: disk_only_publish_def Let_def)
    then show ?thesis using inv by simp
  next
    case valid: True
    then have i: "i < length (sys_staged s)" by simp
    have live: "sys_endpoint s \<noteq> None"
      using inv i unfolding disk_only_cut_invariant_def by auto
    then obtain old R where endpoint: "sys_endpoint s = Some (old, R)" by (cases "sys_endpoint s") auto
    have cut: "stored_cut_is_current digest profile old R (sys_disk s)"
      using inv endpoint unfolding disk_only_cut_invariant_def by blast
    have base: "old = staged_base ?p"
      using cut valid unfolding stored_cut_is_current_def by auto
    have profile: "image_profile ?record = profile"
      using inv nth_mem[OF i] unfolding disk_only_cut_invariant_def by blast
    have publish: "publish_recovery_head digest (Some (staged_base ?p)) ?record (sys_disk s) =
        (sys_disk s)\<lparr>committed_head := Some ?next\<rparr>"
      using valid by (simp add: publish_recovery_head_def)
    show ?thesis
      using inv valid endpoint base profile publish
      by (auto simp: disk_only_cut_invariant_def stored_cut_is_current_def disk_only_publish_def
        advance_endpoint_def head_for_record_def Let_def)
  qed
qed

lemma disk_only_reopening_keeps_the_live_cut:
  assumes inv: "disk_only_cut_invariant digest profile s"
  shows "disk_only_cut_invariant digest profile (disk_only_reopen accept digest profile attachment s)"
  using inv by (auto simp: disk_only_cut_invariant_def disk_only_reopen_def stored_cut_is_current_def
    reopen_from_authenticated_head_def product_round_trip_preserves_the_durable_projection
    split: option.splits prod.splits if_splits)

lemma disk_only_step_keeps_the_live_cut:
  assumes inv: "disk_only_cut_invariant digest profile s"
  shows "disk_only_cut_invariant digest profile (disk_only_step accept step digest profile event s)"
proof (cases event)
  case (Ask c a)
  then show ?thesis using inv
    by (auto simp: disk_only_cut_invariant_def request_effect_def stage_step_def staged_commit_def
      split: option.splits if_splits)
next
  case (Flush_Record i)
  then show ?thesis using inv flushing_keeps_a_current_stored_cut
    by (auto simp: disk_only_cut_invariant_def flush_effect_def)
next
  case (Publish_Head i)
  then show ?thesis using disk_only_publication_keeps_the_live_cut[OF inv] by simp
next
  case (Select_Head i)
  then show ?thesis using inv by simp
next
  case (Issue_Reply i)
  then show ?thesis using inv by (simp add: disk_only_cut_invariant_def disk_only_issue_def Let_def)
next
  case Repair_Head
  then show ?thesis using inv by simp
next
  case Crash_Endpoint
  then show ?thesis using inv by (simp add: disk_only_cut_invariant_def)
next
  case (Reopen_Endpoint attachment)
  then show ?thesis using disk_only_reopening_keeps_the_live_cut[OF inv] by simp
next
  case (Roll_Back_Disk j)
  then show ?thesis using inv
    by (auto simp: disk_only_cut_invariant_def roll_back_disk_effect_def system_down_def split: if_splits)
next
  case (Roll_Back_Witness j)
  then show ?thesis using inv by simp
qed

lemma disk_only_prefix_has_the_live_cut:
  "disk_only_cut_invariant digest profile
    (fold (disk_only_step accept step digest profile) events (genesis_system digest profile R0))"
proof -
  have start: "disk_only_cut_invariant digest profile (genesis_system digest profile R0)"
    by (auto simp: disk_only_cut_invariant_def stored_cut_is_current_def genesis_system_def
      genesis_disk_def genesis_record_def head_for_record_def)
  have preserves: "disk_only_cut_invariant digest profile s \<Longrightarrow>
      disk_only_cut_invariant digest profile (fold (disk_only_step accept step digest profile) events s)" for s
    by (induction events arbitrary: s) (auto intro: disk_only_step_keeps_the_live_cut)
  show ?thesis by (rule preserves[OF start])
qed

context recovery_address_environment
begin

theorem a_globally_safe_storage_rule_holds_at_every_spendable_reachable_cut:
  assumes run: "s = fold (disk_only_step accept step digest profile) prefix (genesis_system digest profile R0)"
    and live: "sys_endpoint s = Some (h, R)"
    and action: "step c a R = (R1, reply)" "R1 \<noteq> R"
    and right: "right_of reply \<noteq> None"
    and attachment: "attachment_profile attachment = profile"
    and globally_safe: "\<forall>events. once_only right_of (sys_released
      (fold (disk_only_step accept step digest profile) events (genesis_system digest profile R0)))"
  shows "\<not> accept (sys_disk s)"
    and "sys_endpoint (fold (disk_only_step accept step digest profile)
      [Crash_Endpoint, Reopen_Endpoint attachment] s) = None"
proof -
  have history: "disk_history_is_addressed digest s"
    unfolding run by (rule disk_only_prefix_has_addressed_history)
  have live_cut: "disk_only_cut_invariant digest profile s"
    unfolding run by (rule disk_only_prefix_has_the_live_cut)
  have cut: "stored_cut_is_current digest profile h R (sys_disk s)"
    using live_cut live unfolding disk_only_cut_invariant_def by blast
  have addressed: "records_are_at_their_own_addresses digest (sys_disk s)"
    using history unfolding disk_history_is_addressed_def by blast
  obtain j where saved: "j < length (ghost_disks s)" "ghost_disks s ! j = sys_disk s"
    using history unfolding disk_history_is_addressed_def by (metis in_set_conv_nth)
  have safe_suffix: "\<forall>suffix. once_only right_of
      (sys_released (fold (disk_only_step accept step digest profile) suffix s))"
  proof
    fix suffix
    have complete_trace: "once_only right_of (sys_released
        (fold (disk_only_step accept step digest profile) (prefix @ suffix)
          (genesis_system digest profile R0)))"
      by (rule spec[OF globally_safe])
    show "once_only right_of
        (sys_released (fold (disk_only_step accept step digest profile) suffix s))"
      using complete_trace by (simp only: run fold_append comp_apply)
  qed
  show rejected: "\<not> accept (sys_disk s)"
    by (rule a_storage_only_rule_safe_on_all_suffixes_refuses_each_spendable_current_cut
      [OF cut addressed saved attachment action right safe_suffix])
  show "sys_endpoint (fold (disk_only_step accept step digest profile)
      [Crash_Endpoint, Reopen_Endpoint attachment] s) = None"
    by (rule storage_refusal_cannot_reopen_after_a_plain_crash[where s = s and accept = accept])
      (rule rejected)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms disk_only_prefix_has_addressed_history
      disk_only_prefix_has_the_live_cut
      recovery_address_environment.a_globally_safe_storage_rule_holds_at_every_spendable_reachable_cut})
  then () else error "Unexpected oracle in arbitrary-prefix recovery target"
\<close>

end
