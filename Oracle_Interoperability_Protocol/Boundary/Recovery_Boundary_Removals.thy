theory Recovery_Boundary_Removals
  imports Recovery_Boundary_Invariant
begin

section \<open>Concrete crash histories of the spending instance\<close>

abbreviation toy_attachment where
  "toy_attachment profile c \<equiv> \<lparr>attachment_profile = profile, attachment_connection = c\<rparr>"

abbreviation toy_run where
  "toy_run profile R0 events \<equiv> fold (boundary_step toy_step toy_digest profile) events (genesis_system toy_digest profile R0)"

lemma toy_replies_follow_effects: "replies_follow_effects toy_step"
proof -
  have "fst (toy_step c a R) \<noteq> R \<longrightarrow> fst (toy_step c a R) = fst (toy_step c' b R) \<longrightarrow>
      snd (toy_step c a R) = snd (toy_step c' b R)" for c a c' b R
    by (cases a; cases b) simp_all
  then show ?thesis unfolding replies_follow_effects_def by blast
qed

text \<open>A crash after preparation and before flush: the step is not in the word and nothing was released.\<close>

lemma crash_before_flush_drops_the_prepared_step:
  "sys_endpoint (toy_run profile R0 [Ask c Toy_Spend, Crash_Endpoint, Reopen_Endpoint (toy_attachment profile c)]) =
     Some (head_for_record toy_digest (genesis_record profile R0), R0)"
  "ghost_word (toy_run profile R0 [Ask c Toy_Spend, Crash_Endpoint, Reopen_Endpoint (toy_attachment profile c)]) = []"
  "sys_released (toy_run profile R0 [Ask c Toy_Spend, Crash_Endpoint, Reopen_Endpoint (toy_attachment profile c)]) = []"
  by (simp_all add: boundary_run_simps)

text \<open>The wrong conclusion that a reopened state runs every prepared step fails on the same history.\<close>

lemma reopened_state_is_not_the_run_of_every_prepared_step:
  "sys_endpoint (toy_run profile R0 [Ask c Toy_Spend, Crash_Endpoint, Reopen_Endpoint (toy_attachment profile c)]) \<noteq>
     Some (head_for_record toy_digest (genesis_record profile R0), run_product_action_word toy_step [(c, Toy_Spend)] R0)"
  by (simp add: boundary_run_simps)

lemma crash_after_flush_before_publication_keeps_the_old_state:
  "sys_endpoint (toy_run profile R0 [Ask c Toy_Spend, Flush_Record 0, Crash_Endpoint,
      Reopen_Endpoint (toy_attachment profile c)]) = Some (head_for_record toy_digest (genesis_record profile R0), R0)"
  "ghost_word (toy_run profile R0 [Ask c Toy_Spend, Flush_Record 0, Crash_Endpoint,
      Reopen_Endpoint (toy_attachment profile c)]) = []"
  by (simp_all add: boundary_run_simps)

lemma crash_after_publication_before_selection_holds_until_repair:
  "sys_endpoint (toy_run profile R0 [Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Crash_Endpoint,
      Reopen_Endpoint (toy_attachment profile c)]) = None"
  "sys_endpoint (toy_run profile R0 [Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Crash_Endpoint,
      Reopen_Endpoint (toy_attachment profile c), Repair_Head, Reopen_Endpoint (toy_attachment profile c)]) =
     Some (head_for_record toy_digest (genesis_record profile R0), R0)"
  "ghost_word (toy_run profile R0 [Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Crash_Endpoint,
      Reopen_Endpoint (toy_attachment profile c), Repair_Head, Reopen_Endpoint (toy_attachment profile c)]) = []"
  by (simp_all add: boundary_run_simps)

lemma crash_after_selection_before_issue_loses_only_the_reply:
  "sys_endpoint (toy_run profile R0 [Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Select_Head 0, Crash_Endpoint,
      Reopen_Endpoint (toy_attachment profile c)]) =
     Some (head_for_record toy_digest (staged_commit profile (head_for_record toy_digest (genesis_record profile R0))
       (toy_bump R0)), toy_bump R0)"
  "ghost_word (toy_run profile R0 [Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Select_Head 0, Crash_Endpoint,
      Reopen_Endpoint (toy_attachment profile c)]) = [(c, Toy_Spend)]"
  "sys_released (toy_run profile R0 [Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Select_Head 0, Crash_Endpoint,
      Reopen_Endpoint (toy_attachment profile c)]) = []"
  by (simp_all add: boundary_run_simps)

lemma a_stale_prepared_step_is_refused_by_the_disk_and_the_witness:
  "ghost_word (toy_run profile R0 [Ask c Toy_Spend, Ask c Toy_Spend, Flush_Record 0, Flush_Record 1, Publish_Head 0,
      Select_Head 0, Publish_Head 1, Select_Head 1]) = [(c, Toy_Spend)]"
  by (simp add: boundary_run_simps)

lemma storage_only_rollback_holds_and_the_latest_storage_reopens:
  "sys_endpoint (toy_run profile R0 [Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Select_Head 0, Crash_Endpoint,
      Roll_Back_Disk 0, Reopen_Endpoint (toy_attachment profile c)]) = None"
  "sys_endpoint (toy_run profile R0 [Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Select_Head 0, Crash_Endpoint,
      Roll_Back_Disk 0, Reopen_Endpoint (toy_attachment profile c), Roll_Back_Disk 2,
      Reopen_Endpoint (toy_attachment profile c)]) \<noteq> None"
  by (simp_all add: boundary_run_simps)

lemma witness_only_rollback_holds:
  "sys_endpoint (toy_run profile R0 [Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Select_Head 0, Crash_Endpoint,
      Roll_Back_Witness 0, Reopen_Endpoint (toy_attachment profile c)]) = None"
  by (simp add: boundary_run_simps)

section \<open>Two discriminating counterexamples\<close>

text \<open>Two different actions with one effect and different replies: the step that the witness did not
  select still releases its reply at the selected position. The reply conclusion needs
  @{const replies_follow_effects}.\<close>

lemma unselected_twin_step_releases_a_reply_outside_the_committed_run:
  fixes c profile R0
  defines "\<sigma> \<equiv> fold (boundary_step twin_step toy_digest profile)
      [Ask c Twin_Pay, Ask c Twin_Echo, Flush_Record 0, Publish_Head 0, Select_Head 0, Issue_Reply 1]
      (genesis_system toy_digest profile R0)"
  shows "(0, Toy_Seen (retained_provider R0)) \<in> set (sys_released \<sigma>)"
    and "snd (run_word_transcript twin_step (ghost_word \<sigma>) R0) ! 0 = Toy_Token (retained_provider R0)"
    and "\<not> replies_follow_effects twin_step"
proof -
  show "(0, Toy_Seen (retained_provider R0)) \<in> set (sys_released \<sigma>)"
    unfolding \<sigma>_def by (simp add: boundary_run_simps)
  show "snd (run_word_transcript twin_step (ghost_word \<sigma>) R0) ! 0 = Toy_Token (retained_provider R0)"
    unfolding \<sigma>_def by (simp add: boundary_run_simps)
  show "\<not> replies_follow_effects twin_step"
  proof
    assume follow: "replies_follow_effects twin_step"
    have moved: "fst (twin_step c Twin_Pay R0) \<noteq> R0" by simp
    have same: "fst (twin_step c Twin_Pay R0) = fst (twin_step c Twin_Echo R0)" by simp
    have "snd (twin_step c Twin_Pay R0) = snd (twin_step c Twin_Echo R0)"
      using follow moved same unfolding replies_follow_effects_def by blast
    then show False by simp
  qed
qed

text \<open>Linearizing the word at publication instead of selection is wrong: a published head that the
  witness never selected is repaired away, and the reopened state is not the run of that word.\<close>

definition publish_linearized_step where
  "publish_linearized_step step digest profile e \<sigma> =
    (case e of
       Publish_Head i \<Rightarrow>
         (if i < length (sys_staged \<sigma>) \<and>
             committed_head (sys_disk (boundary_step step digest profile e \<sigma>)) \<noteq> committed_head (sys_disk \<sigma>)
          then (boundary_step step digest profile e \<sigma>)\<lparr>ghost_word := ghost_word \<sigma> @ [staged_entry (sys_staged \<sigma> ! i)]\<rparr>
          else boundary_step step digest profile e \<sigma>)
     | Select_Head i \<Rightarrow> (boundary_step step digest profile e \<sigma>)\<lparr>ghost_word := ghost_word \<sigma>\<rparr>
     | _ \<Rightarrow> boundary_step step digest profile e \<sigma>)"

lemma publication_linearization_breaks_crash_transparency:
  fixes c profile R0
  defines "\<sigma> \<equiv> fold (publish_linearized_step toy_step toy_digest profile)
      [Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Crash_Endpoint, Repair_Head]
      (genesis_system toy_digest profile R0)"
  shows "witnessed_reopen toy_digest profile (toy_attachment profile c) (sys_disk \<sigma>) (sys_witness \<sigma>) =
      Some (head_for_record toy_digest (genesis_record profile R0), R0)"
    and "R0 \<noteq> run_product_action_word toy_step (ghost_word \<sigma>) R0"
  unfolding \<sigma>_def by (simp_all add: publish_linearized_step_def boundary_run_simps)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms toy_replies_follow_effects
      crash_before_flush_drops_the_prepared_step reopened_state_is_not_the_run_of_every_prepared_step
      crash_after_flush_before_publication_keeps_the_old_state
      crash_after_publication_before_selection_holds_until_repair
      crash_after_selection_before_issue_loses_only_the_reply
      a_stale_prepared_step_is_refused_by_the_disk_and_the_witness
      storage_only_rollback_holds_and_the_latest_storage_reopens witness_only_rollback_holds
      unselected_twin_step_releases_a_reply_outside_the_committed_run
      publication_linearization_breaks_crash_transparency})
  then () else error "Unexpected oracle in the crash histories"
\<close>

end
