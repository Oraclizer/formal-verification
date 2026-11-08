theory Recovery_Boundary_Reply_Positions
  imports "Recovery_Boundary_Invariant"
begin

text \<open>Reply erasure preserves the operational guards. The release-position result does not require
  the replies-follow-effects premise used for equality of reply values.\<close>

definition map_staged_replies ::
  "('r \<Rightarrow> 's) \<Rightarrow> ('a, 'r, 'd) staged_step \<Rightarrow> ('a, 's, 'd) staged_step" where
  "map_staged_replies f p = \<lparr>staged_entry = staged_entry p, staged_record = staged_record p,
    staged_reply = f (staged_reply p), staged_base = staged_base p\<rparr>"

definition map_boundary_replies ::
  "('r \<Rightarrow> 's) \<Rightarrow> ('a, 'r, 'd) boundary_system \<Rightarrow> ('a, 's, 'd) boundary_system" where
  "map_boundary_replies f s = \<lparr>sys_disk = sys_disk s, sys_witness = sys_witness s,
    sys_endpoint = sys_endpoint s, sys_staged = map (map_staged_replies f) (sys_staged s),
    sys_released = map (\<lambda>p. (fst p, f (snd p))) (sys_released s), ghost_word = ghost_word s,
    ghost_slot = ghost_slot s, ghost_disks = ghost_disks s, ghost_cuts = ghost_cuts s\<rparr>"

definition map_step_replies where
  "map_step_replies f step c a R = (fst (step c a R), f (snd (step c a R)))"

lemma mapped_stage_fields [simp]:
  "staged_entry (map_staged_replies f p) = staged_entry p"
  "staged_record (map_staged_replies f p) = staged_record p"
  "staged_reply (map_staged_replies f p) = f (staged_reply p)"
  "staged_base (map_staged_replies f p) = staged_base p"
  by (simp_all add: map_staged_replies_def)

lemma mapped_system_fields [simp]:
  "sys_disk (map_boundary_replies f s) = sys_disk s"
  "sys_witness (map_boundary_replies f s) = sys_witness s"
  "sys_endpoint (map_boundary_replies f s) = sys_endpoint s"
  "sys_staged (map_boundary_replies f s) = map (map_staged_replies f) (sys_staged s)"
  "sys_released (map_boundary_replies f s) = map (\<lambda>p. (fst p, f (snd p))) (sys_released s)"
  "ghost_word (map_boundary_replies f s) = ghost_word s"
  "ghost_slot (map_boundary_replies f s) = ghost_slot s"
  "ghost_disks (map_boundary_replies f s) = ghost_disks s"
  "ghost_cuts (map_boundary_replies f s) = ghost_cuts s"
  by (simp_all add: map_boundary_replies_def)

lemma reply_mapping_does_not_change_freshness [simp]:
  "witness_fresh (map_boundary_replies f s) base = witness_fresh s base"
  "disk_fresh (map_boundary_replies f s) base = disk_fresh s base"
  "system_down (map_boundary_replies f s) = system_down s"
  by (simp_all add: witness_fresh_def disk_fresh_def system_down_def)

lemma reply_mapping_does_not_change_endpoint_advance [simp]:
  "advance_endpoint (map_staged_replies f p) h endpoint = advance_endpoint p h endpoint"
  by (auto simp: advance_endpoint_def split: option.splits)

lemma boundary_step_commutes_with_reply_mapping:
  "map_boundary_replies f (boundary_step step digest profile e s) =
     boundary_step (map_step_replies f step) digest profile e (map_boundary_replies f s)"
proof (cases e)
  case (Ask c a)
  then show ?thesis
    by (auto simp: map_boundary_replies_def map_staged_replies_def map_step_replies_def
      request_effect_def stage_step_def witness_fresh_def split: option.splits if_splits)
next
  case (Flush_Record i)
  then show ?thesis
    by (auto simp: map_boundary_replies_def flush_effect_def split: if_splits)
next
  case (Publish_Head i)
  then show ?thesis
    by (auto simp: map_boundary_replies_def publish_effect_def Let_def split: if_splits)
next
  case (Select_Head i)
  then show ?thesis
    by (auto simp: map_boundary_replies_def select_effect_def selection_proposal_def
      advance_endpoint_def Let_def split: option.splits if_splits)
next
  case (Issue_Reply i)
  then show ?thesis
    by (auto simp: map_boundary_replies_def issue_effect_def Let_def split: if_splits)
next
  case Repair_Head
  then show ?thesis
    by (auto simp: map_boundary_replies_def repair_effect_def split: if_splits)
next
  case Crash_Endpoint
  then show ?thesis by (simp add: map_boundary_replies_def)
next
  case (Reopen_Endpoint attachment)
  then show ?thesis
    by (auto simp: map_boundary_replies_def reopen_effect_def split: if_splits)
next
  case (Roll_Back_Disk k)
  then show ?thesis
    by (auto simp: map_boundary_replies_def roll_back_disk_effect_def system_down_def split: if_splits)
next
  case (Roll_Back_Witness k)
  then show ?thesis
    by (auto simp: map_boundary_replies_def roll_back_witness_effect_def system_down_def split: if_splits)
qed

lemma boundary_run_commutes_with_reply_mapping:
  "map_boundary_replies f (fold (boundary_step step digest profile) events s) =
    fold (boundary_step (map_step_replies f step) digest profile) events (map_boundary_replies f s)"
proof (induction events arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons e events)
  show ?case by (simp add: Cons.IH boundary_step_commutes_with_reply_mapping)
qed

lemma genesis_commutes_with_reply_mapping [simp]:
  "map_boundary_replies f (genesis_system digest profile R0) = genesis_system digest profile R0"
  by (simp add: map_boundary_replies_def genesis_system_def)

lemma unit_replies_follow_effects:
  "replies_follow_effects (map_step_replies (\<lambda>_. ()) step)"
  by (simp add: replies_follow_effects_def map_step_replies_def)

theorem every_released_position_is_committed_without_a_reply_value_premise:
  assumes run: "s = fold (boundary_step step digest profile) events (genesis_system digest profile R0)"
    and honest_witness: "\<forall>e \<in> set events. \<not> is_witness_rollback e"
    and address_collision_free: "inj digest"
    and released: "(k, reply) \<in> set (sys_released s)"
  shows "k < length (ghost_word s)"
proof -
  let ?erase = "map_boundary_replies (\<lambda>_. ())"
  let ?step = "map_step_replies (\<lambda>_. ()) step"
  have erased_run: "?erase s = fold (boundary_step ?step digest profile) events (genesis_system digest profile R0)"
    unfolding run by (simp add: boundary_run_commutes_with_reply_mapping)
  have erased_release: "(k, ()) \<in> set (sys_released (?erase s))"
  proof -
    have mapped: "(\<lambda>p. (fst p, ())) (k, reply) \<in>
        (\<lambda>p. (fst p, ())) ` set (sys_released s)"
      by (rule imageI[OF released])
    then show ?thesis by (simp add: map_boundary_replies_def)
  qed
  have "k < length (ghost_word (?erase s)) \<and>
      () = snd (run_word_transcript ?step (ghost_word (?erase s)) R0) ! k"
    by (rule every_crash_point_recovers_the_committed_uninterrupted_run(3)
      [OF erased_run honest_witness address_collision_free unit_replies_follow_effects erased_release])
  then show ?thesis by simp
qed

text \<open>Reply erasure establishes position validity. It cannot establish equality of the original
  reply values and therefore does not discharge replies_follow_effects for the product step.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms boundary_step_commutes_with_reply_mapping
      boundary_run_commutes_with_reply_mapping unit_replies_follow_effects
      every_released_position_is_committed_without_a_reply_value_premise})
  then () else error "Unexpected oracle in reply-position target"
\<close>

end
