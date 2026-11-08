theory Recovery_Request_Provenance_Step
  imports "Recovery_Request_Provenance_Types"
begin

lemma flushing_keeps_request_derived_images:
  assumes "archive_has_ask_witness step R0 requests disk"
    "state_has_ask_witness step R0 requests (image_records record)"
  shows "archive_has_ask_witness step R0 requests (flush_commit_record digest record disk)"
  using assms unfolding archive_has_ask_witness_def flush_commit_record_def Let_def by auto

lemma publication_keeps_request_derived_images:
  "archive_has_ask_witness step R0 requests disk \<Longrightarrow>
    archive_has_ask_witness step R0 requests (publish_recovery_head digest expected record disk)"
  unfolding archive_has_ask_witness_def publish_recovery_head_def by simp

lemma changing_only_the_head_keeps_request_derived_images:
  "archive_has_ask_witness step R0 requests disk \<Longrightarrow>
    archive_has_ask_witness step R0 requests (disk\<lparr>committed_head := head\<rparr>)"
  unfolding archive_has_ask_witness_def by simp

lemma a_successful_reopen_has_the_flushed_images_ask_witness:
  assumes archive: "archive_has_ask_witness step R0 requests disk"
    and reopened: "witnessed_reopen digest profile attachment disk witness = Some (head, R)"
  shows "state_has_ask_witness step R0 requests R"
proof -
  obtain entry where stored: "flushed_records disk head = Some entry" "image_records entry = R"
    using witnessed_reopen_returns_the_witnessed_record[OF reopened] by blast
  have "state_has_ask_witness step R0 requests (image_records entry)"
    using archive stored(1) unfolding archive_has_ask_witness_def by blast
  then show ?thesis using stored(2) by simp
qed

lemma every_boundary_event_preserves_trace_indexed_state_provenance:
  assumes inv: "boundary_has_ask_provenance step R0 requests s"
  shows "boundary_has_ask_provenance step R0 (requests @ ask_occurrence event)
    (boundary_step step digest profile event s)"
proof (cases event)
  case (Ask connection action)
  have extended: "boundary_has_ask_provenance step R0 (requests @ [(connection, action)]) s"
    by (rule boundary_ask_provenance_append_right[OF inv])
  show ?thesis
  proof (cases "sys_endpoint s")
    case None
    then show ?thesis using extended Ask by (simp add: request_effect_def)
  next
    case (Some endpoint)
    then obtain base R where endpoint: "sys_endpoint s = Some (base, R)" by (cases endpoint) auto
    have before: "state_has_ask_witness step R0 requests R"
      using inv endpoint unfolding boundary_has_ask_provenance_def by blast
    have produced: "state_has_ask_witness step R0 (requests @ [(connection, action)])
        (fst (step connection action R))"
      by (rule one_actual_ask_extends_its_base_witness[OF before])
    show ?thesis using extended Ask endpoint produced
      by (auto simp: boundary_has_ask_provenance_def request_effect_def stage_step_def staged_commit_def)
  qed
next
  case (Flush_Record i)
  have new_archive: "archive_has_ask_witness step R0 requests
      (flush_commit_record digest (staged_record (sys_staged s ! i)) (sys_disk s))"
    if bound: "i < length (sys_staged s)"
  proof -
    have staged: "state_has_ask_witness step R0 requests (image_records (staged_record (sys_staged s ! i)))"
      using inv nth_mem[OF bound] unfolding boundary_has_ask_provenance_def by blast
    have old_archive: "archive_has_ask_witness step R0 requests (sys_disk s)"
      using inv unfolding boundary_has_ask_provenance_def by blast
    show ?thesis by (rule flushing_keeps_request_derived_images[OF old_archive staged])
  qed
  show ?thesis using inv Flush_Record new_archive
    by (auto simp: boundary_has_ask_provenance_def flush_effect_def)
next
  case (Publish_Head i)
  have new_archive: "archive_has_ask_witness step R0 requests
      (publish_recovery_head digest expected entry (sys_disk s))" for expected entry
    using inv publication_keeps_request_derived_images
    unfolding boundary_has_ask_provenance_def by blast
  show ?thesis using inv Publish_Head new_archive
    by (auto simp: boundary_has_ask_provenance_def publish_effect_def Let_def)
next
  case (Select_Head i)
  have advanced: "\<forall>h R. advance_endpoint (sys_staged s ! i) selected (sys_endpoint s) = Some (h, R)
      \<longrightarrow> state_has_ask_witness step R0 requests R"
    if bound: "i < length (sys_staged s)" for selected
  proof -
    have staged: "state_has_ask_witness step R0 requests (image_records (staged_record (sys_staged s ! i)))"
      using inv nth_mem[OF bound] unfolding boundary_has_ask_provenance_def by blast
    show ?thesis using inv staged
      unfolding boundary_has_ask_provenance_def advance_endpoint_def
      by (auto split: option.splits if_splits)
  qed
  show ?thesis using inv Select_Head advanced
    by (auto simp: boundary_has_ask_provenance_def select_effect_def Let_def split: option.splits)
next
  case (Issue_Reply i)
  then show ?thesis using inv
    by (simp add: boundary_has_ask_provenance_def issue_effect_def Let_def)
next
  case Repair_Head
  have new_archive: "archive_has_ask_witness step R0 requests
      ((sys_disk s)\<lparr>committed_head := head\<rparr>)" for head
    using inv changing_only_the_head_keeps_request_derived_images
    unfolding boundary_has_ask_provenance_def by blast
  show ?thesis using inv Repair_Head new_archive
    by (auto simp: boundary_has_ask_provenance_def repair_effect_def)
next
  case Crash_Endpoint
  then show ?thesis using inv by (simp add: boundary_has_ask_provenance_def)
next
  case (Reopen_Endpoint attachment)
  have reopened: "\<forall>h R. witnessed_reopen digest profile attachment (sys_disk s) (sys_witness s) = Some (h, R)
      \<longrightarrow> state_has_ask_witness step R0 requests R"
    using inv a_successful_reopen_has_the_flushed_images_ask_witness
    unfolding boundary_has_ask_provenance_def by blast
  show ?thesis using inv Reopen_Endpoint reopened
    by (simp add: boundary_has_ask_provenance_def reopen_effect_def)
next
  case (Roll_Back_Disk j)
  have restored: "archive_has_ask_witness step R0 requests (ghost_disks s ! j)"
    if bound: "j < length (ghost_disks s)"
    using inv nth_mem[OF bound] unfolding boundary_has_ask_provenance_def by blast
  show ?thesis using inv Roll_Back_Disk restored
    by (auto simp: boundary_has_ask_provenance_def roll_back_disk_effect_def)
next
  case (Roll_Back_Witness j)
  then show ?thesis using inv
    by (simp add: boundary_has_ask_provenance_def roll_back_witness_effect_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms flushing_keeps_request_derived_images
      publication_keeps_request_derived_images changing_only_the_head_keeps_request_derived_images
      a_successful_reopen_has_the_flushed_images_ask_witness
      every_boundary_event_preserves_trace_indexed_state_provenance})
  then () else error "Unexpected oracle in trace-indexed state provenance transition"
\<close>

end
