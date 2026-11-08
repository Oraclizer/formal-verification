theory Recovery_Boundary_Storage_Dilemma
  imports "Recovery_Boundary_Environment"
begin

text \<open>A storage-only recovery rule is examined at an arbitrary current cut and saved-copy position.
  The step changes the retained image and releases a nonempty right. The refusal-or-duplicate-release
  alternative uses the explicit addressed-storage environment.\<close>

definition one_mutation_events where
  "one_mutation_events c a = [Ask c a, Flush_Record 0, Publish_Head 0, Issue_Reply 0]"

definition restart_saved_copy_events where
  "restart_saved_copy_events j attachment = [Crash_Endpoint, Roll_Back_Disk j, Reopen_Endpoint attachment]"

definition stored_cut_is_current where
  "stored_cut_is_current digest profile h R disk \<longleftrightarrow>
    committed_head disk = Some h \<and> head_profile h = profile \<and>
    (\<exists>record. flushed_records disk h = Some record \<and>
      head_for_record digest record = h \<and> image_records record = R)"

lemma reopen_current_stored_cut:
  assumes cut: "stored_cut_is_current digest profile h R disk"
    and attachment: "attachment_profile attachment = profile"
  shows "map_option (\<lambda>endpoint. (h, capture_retained_product endpoint))
      (reopen_from_authenticated_head digest profile (Some attachment) disk) = Some (h, R)"
  using cut attachment
  by (auto simp: stored_cut_is_current_def reopen_from_authenticated_head_def
    product_round_trip_preserves_the_durable_projection)

lemma restart_saved_current_copy:
  assumes saved: "j < length (ghost_disks s)" "ghost_disks s ! j = disk"
    and cut: "stored_cut_is_current digest profile h R disk"
    and attachment: "attachment_profile attachment = profile"
    and accepted: "accept disk"
  shows "fold (disk_only_step accept step digest profile) (restart_saved_copy_events j attachment) s =
    s\<lparr>sys_endpoint := Some (h, R), sys_staged := [], sys_disk := disk\<rparr>"
  using saved cut attachment accepted
  by (cases s) (auto simp: restart_saved_copy_events_def roll_back_disk_effect_def system_down_def
    disk_only_reopen_def stored_cut_is_current_def reopen_from_authenticated_head_def
    product_round_trip_preserves_the_durable_projection)

lemma storage_refusal_cannot_reopen_after_a_plain_crash:
  assumes "\<not> accept (sys_disk s)"
  shows "sys_endpoint (fold (disk_only_step accept step digest profile)
    [Crash_Endpoint, Reopen_Endpoint attachment] s) = None"
  using assms by (simp add: disk_only_reopen_def)

context recovery_address_environment
begin

lemma one_changing_step_from_a_clean_cut:
  assumes endpoint: "sys_endpoint s = Some (h, R)"
    and clean: "sys_staged s = []"
    and current: "committed_head (sys_disk s) = Some h"
    and profile: "head_profile h = profile"
    and addressed: "records_are_at_their_own_addresses digest (sys_disk s)"
    and action: "step c a R = (R1, reply)" "R1 \<noteq> R"
  shows "sys_disk (fold (disk_only_step accept step digest profile) (one_mutation_events c a) s) =
      (flush_commit_record digest (staged_commit profile h R1) (sys_disk s))
        \<lparr>committed_head := Some (head_for_record digest (staged_commit profile h R1))\<rparr>"
    and "sys_endpoint (fold (disk_only_step accept step digest profile) (one_mutation_events c a) s) =
      Some (head_for_record digest (staged_commit profile h R1), R1)"
    and "sys_released (fold (disk_only_step accept step digest profile) (one_mutation_events c a) s) =
      sys_released s @ [(length (ghost_word s), reply)]"
    and "ghost_word (fold (disk_only_step accept step digest profile) (one_mutation_events c a) s) =
      ghost_word s @ [(c, a)]"
    and "ghost_disks (fold (disk_only_step accept step digest profile) (one_mutation_events c a) s) =
      ghost_disks s @ [flush_commit_record digest (staged_commit profile h R1) (sys_disk s),
        (flush_commit_record digest (staged_commit profile h R1) (sys_disk s))
          \<lparr>committed_head := Some (head_for_record digest (staged_commit profile h R1))\<rparr>]"
proof -
  let ?record = "staged_commit profile h R1"
  let ?next_head = "head_for_record digest ?record"
  let ?flushed = "flush_commit_record digest ?record (sys_disk s)"
  let ?published = "?flushed\<lparr>committed_head := Some ?next_head\<rparr>"
  let ?after = "fold (disk_only_step accept step digest profile) (one_mutation_events c a) s"
  have exact_flush: "flushed_records ?flushed ?next_head = Some ?record"
    by (rule flushing_an_addressed_store_supplies_the_exact_candidate[OF addressed])
  have flush_head: "committed_head ?flushed = Some h"
    using current by (simp add: flushed_candidate_is_not_visible_before_the_head_changes)
  have extends: "candidate_extends_head (Some h) ?record"
    using profile by (simp add: staged_commit_def candidate_extends_head_def)
  have publish: "publish_recovery_head digest (Some h) ?record ?flushed = ?published"
    using flush_head extends exact_flush
    by (simp add: publish_recovery_head_def)
  show "sys_disk ?after = ?published"
    "sys_endpoint ?after = Some (?next_head, R1)"
    "sys_released ?after = sys_released s @ [(length (ghost_word s), reply)]"
    "ghost_word ?after = ghost_word s @ [(c, a)]"
    "ghost_disks ?after = ghost_disks s @ [?flushed, ?published]"
    unfolding one_mutation_events_def
    using endpoint clean current profile action exact_flush flush_head publish
    by (simp_all add: request_effect_def stage_step_def disk_fresh_def flush_effect_def
      disk_only_publish_def disk_only_issue_def advance_endpoint_def
      candidate_extends_head_def staged_commit_def Let_def)
qed

theorem any_saved_current_cut_has_the_storage_only_dilemma:
  assumes cut: "stored_cut_is_current digest profile h R (sys_disk s)"
    and addressed: "records_are_at_their_own_addresses digest (sys_disk s)"
    and saved: "j < length (ghost_disks s)" "ghost_disks s ! j = sys_disk s"
    and attachment: "attachment_profile attachment = profile"
    and action: "step c a R = (R1, reply)" "R1 \<noteq> R"
    and right: "right_of reply \<noteq> None"
  shows "(\<not> accept (sys_disk s) \<and>
       sys_endpoint (fold (disk_only_step accept step digest profile)
         [Crash_Endpoint, Reopen_Endpoint attachment] s) = None) \<or>
    (\<exists>suffix. \<not> once_only right_of (sys_released
       (fold (disk_only_step accept step digest profile) suffix s)))"
proof (cases "accept (sys_disk s)")
  case False
  have held: "sys_endpoint (fold (disk_only_step accept step digest profile)
      [Crash_Endpoint, Reopen_Endpoint attachment] s) = None"
    by (rule storage_refusal_cannot_reopen_after_a_plain_crash[where s = s and accept = accept])
      (rule False)
  then show ?thesis using False by blast
next
  case accepted: True
  let ?restart = "restart_saved_copy_events j attachment"
  let ?mutate = "one_mutation_events c a"
  let ?run = "\<lambda>events state. fold (disk_only_step accept step digest profile) events state"
  let ?s0 = "?run ?restart s"
  let ?s1 = "?run ?mutate ?s0"
  let ?s2 = "?run ?restart ?s1"
  let ?s3 = "?run ?mutate ?s2"
  have reset0: "?s0 = s\<lparr>sys_endpoint := Some (h, R), sys_staged := [], sys_disk := sys_disk s\<rparr>"
    by (rule restart_saved_current_copy[where s = s and disk = "sys_disk s" and j = j
        and digest = digest and profile = profile and h = h and R = R
        and attachment = attachment and accept = accept and step = step])
      (rule saved(1), rule saved(2), rule cut, rule attachment, rule accepted)
  have head: "committed_head (sys_disk s) = Some h" "head_profile h = profile"
    using cut unfolding stored_cut_is_current_def by blast+
  have s0_inputs: "sys_endpoint ?s0 = Some (h, R)" "sys_staged ?s0 = []"
      "committed_head (sys_disk ?s0) = Some h"
      "records_are_at_their_own_addresses digest (sys_disk ?s0)"
    using reset0 head addressed by simp_all
  note first = one_changing_step_from_a_clean_cut
    [where s = "?s0" and accept = accept and step = step and profile = profile
      and h = h and R = R and c = c and a = a,
     OF s0_inputs(1,2,3) head(2) s0_inputs(4) action]
  have first_release: "sys_released ?s1 = sys_released s @ [(length (ghost_word s), reply)]"
    using first(3) reset0 by simp
  have first_word: "ghost_word ?s1 = ghost_word s @ [(c, a)]"
    using first(4) reset0 by simp
  have saved_again: "j < length (ghost_disks ?s1)" "ghost_disks ?s1 ! j = sys_disk s"
    using first(5) saved reset0 by (simp_all add: nth_append)
  have reset2: "?s2 = ?s1\<lparr>sys_endpoint := Some (h, R), sys_staged := [], sys_disk := sys_disk s\<rparr>"
    by (rule restart_saved_current_copy[where s = "?s1" and disk = "sys_disk s" and j = j
        and digest = digest and profile = profile and h = h and R = R
        and attachment = attachment and accept = accept and step = step])
      (rule saved_again(1), rule saved_again(2), rule cut, rule attachment, rule accepted)
  have s2_inputs: "sys_endpoint ?s2 = Some (h, R)" "sys_staged ?s2 = []"
      "committed_head (sys_disk ?s2) = Some h"
      "records_are_at_their_own_addresses digest (sys_disk ?s2)"
    using reset2 head addressed by simp_all
  note second = one_changing_step_from_a_clean_cut
    [where s = "?s2" and accept = accept and step = step and profile = profile
      and h = h and R = R and c = c and a = a,
     OF s2_inputs(1,2,3) head(2) s2_inputs(4) action]
  have released_twice: "sys_released ?s3 = sys_released s @
      [(length (ghost_word s), reply), (Suc (length (ghost_word s)), reply)]"
    using second(3) reset2 first_release first_word by simp
  have failed: "\<not> once_only right_of (sys_released ?s3)"
  proof
    assume unique: "once_only right_of (sys_released ?s3)"
    have member_first: "(length (ghost_word s), reply) \<in> set (sys_released ?s3)"
      by (simp add: released_twice)
    have member_second: "(Suc (length (ghost_word s)), reply) \<in> set (sys_released ?s3)"
      by (simp add: released_twice)
    have "length (ghost_word s) = Suc (length (ghost_word s))"
      using unique member_first member_second right unfolding once_only_def by blast
    then show False by simp
  qed
  have fold_suffix: "?s3 = ?run (?restart @ ?mutate @ ?restart @ ?mutate) s"
    by (simp add: fold_append)
  have failed_suffix: "\<not> once_only right_of
      (sys_released (?run (?restart @ ?mutate @ ?restart @ ?mutate) s))"
    using failed by (simp only: fold_suffix not_False_eq_True)
  show ?thesis
    by (rule disjI2, rule exI[of _ "?restart @ ?mutate @ ?restart @ ?mutate"], rule failed_suffix)
qed

corollary a_storage_only_rule_safe_on_all_suffixes_refuses_each_spendable_current_cut:
  assumes cut: "stored_cut_is_current digest profile h R (sys_disk s)"
    and addressed: "records_are_at_their_own_addresses digest (sys_disk s)"
    and saved: "j < length (ghost_disks s)" "ghost_disks s ! j = sys_disk s"
    and attachment: "attachment_profile attachment = profile"
    and action: "step c a R = (R1, reply)" "R1 \<noteq> R"
    and right: "right_of reply \<noteq> None"
    and safe: "\<forall>suffix. once_only right_of (sys_released
      (fold (disk_only_step accept step digest profile) suffix s))"
  shows "\<not> accept (sys_disk s)"
proof -
  let ?closed_attachment = "\<lparr>attachment_profile = attachment_profile attachment,
      attachment_connection = attachment_connection attachment\<rparr> :: current_attachment"
  have closed_profile: "attachment_profile ?closed_attachment = profile"
    using attachment by simp
  have dilemma: "(\<not> accept (sys_disk s) \<and>
       sys_endpoint (fold (disk_only_step accept step digest profile)
         [Crash_Endpoint, Reopen_Endpoint ?closed_attachment] s) = None) \<or>
    (\<exists>suffix. \<not> once_only right_of (sys_released
       (fold (disk_only_step accept step digest profile) suffix s)))"
    by (rule any_saved_current_cut_has_the_storage_only_dilemma
        [where s = s and accept = accept and step = step and profile = profile
          and h = h and R = R and j = j and attachment = "?closed_attachment"
          and c = c and a = a and right_of = right_of])
      (rule cut, rule addressed, rule saved(1), rule saved(2), rule closed_profile,
       rule action(1), rule action(2), rule right)
  show ?thesis using dilemma safe by blast
qed

end

text \<open>The current-cut premise is structural: the disk contains the current exact retained
  record, with matching profile. Its derivation for every product prefix is a separate run
  invariant. Likewise, the saved-copy position must be supplied from the actual snapshot history.
  These obligations must not be replaced by an assumed final safety conclusion.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms reopen_current_stored_cut restart_saved_current_copy
      storage_refusal_cannot_reopen_after_a_plain_crash
      recovery_address_environment.one_changing_step_from_a_clean_cut
      recovery_address_environment.any_saved_current_cut_has_the_storage_only_dilemma
      recovery_address_environment.a_storage_only_rule_safe_on_all_suffixes_refuses_each_spendable_current_cut})
  then () else error "Unexpected oracle in the general storage-only dilemma"
\<close>

end
