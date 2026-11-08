theory Recovery_Boundary_Rollback
  imports Recovery_Boundary_Removals
begin

section \<open>Rolling back the storage and the witness\<close>

subsection \<open>Rolling back both releases one right twice\<close>

lemma joint_rollback_releases_one_right_twice:
  fixes c profile R0
  defines "\<sigma> \<equiv> fold (boundary_step toy_step toy_digest profile)
      [Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Select_Head 0, Issue_Reply 0, Crash_Endpoint,
       Roll_Back_Disk 0, Roll_Back_Witness 0, Reopen_Endpoint (toy_attachment profile c),
       Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Select_Head 0, Issue_Reply 0]
      (genesis_system toy_digest profile R0)"
  shows "sys_released \<sigma> = [(0, Toy_Token (retained_provider R0)), (1, Toy_Token (retained_provider R0))]"
    and "\<not> once_only toy_right (sys_released \<sigma>)"
    and "ghost_word \<sigma> = [(c, Toy_Spend), (c, Toy_Spend)]"
proof -
  show released: "sys_released \<sigma> = [(0, Toy_Token (retained_provider R0)), (1, Toy_Token (retained_provider R0))]"
    unfolding \<sigma>_def by (simp add: boundary_run_simps)
  show "\<not> once_only toy_right (sys_released \<sigma>)"
    unfolding released
    by (rule two_positions_break_once_only[of 0 "Toy_Token (retained_provider R0)" _ 1
        "Toy_Token (retained_provider R0)"]) simp_all
  show "ghost_word \<sigma> = [(c, Toy_Spend), (c, Toy_Spend)]"
    unfolding \<sigma>_def by (simp add: boundary_run_simps)
qed

subsection \<open>Without the witness, storage alone cannot tell an old copy from the latest\<close>

lemma storage_only_recovery_that_accepts_releases_one_right_twice:
  fixes c profile R0
  defines "\<sigma> \<equiv> fold (disk_only_step (\<lambda>_. True) toy_step toy_digest profile)
      [Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Issue_Reply 0, Crash_Endpoint, Roll_Back_Disk 0,
       Reopen_Endpoint (toy_attachment profile c), Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Issue_Reply 0]
      (genesis_system toy_digest profile R0)"
  shows "sys_released \<sigma> = [(0, Toy_Token (retained_provider R0)), (1, Toy_Token (retained_provider R0))]"
    and "\<not> once_only toy_right (sys_released \<sigma>)"
proof -
  show released: "sys_released \<sigma> = [(0, Toy_Token (retained_provider R0)), (1, Toy_Token (retained_provider R0))]"
    unfolding \<sigma>_def by (simp add: boundary_run_simps)
  show "\<not> once_only toy_right (sys_released \<sigma>)"
    unfolding released
    by (rule two_positions_break_once_only[of 0 "Toy_Token (retained_provider R0)" _ 1
        "Toy_Token (retained_provider R0)"]) simp_all
qed

lemma storage_only_recovery_that_holds_never_reopens:
  "sys_endpoint (fold (disk_only_step (\<lambda>_. False) toy_step toy_digest profile)
      [Crash_Endpoint, Reopen_Endpoint (toy_attachment profile c)] (genesis_system toy_digest profile R0)) = None"
  by (simp add: boundary_run_simps)

text \<open>Every storage-only acceptance rule fails one way or the other. The start copy is both the
  latest copy before the first step and an old copy after a rollback, byte for byte.\<close>

lemma storage_only_acceptance_of_the_start_copy_releases_one_right_twice:
  fixes accept c profile R0
  assumes accepted: "accept (genesis_disk toy_digest profile R0)"
  defines "\<sigma> \<equiv> fold (disk_only_step accept toy_step toy_digest profile)
      [Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Issue_Reply 0, Crash_Endpoint, Roll_Back_Disk 0,
       Reopen_Endpoint (toy_attachment profile c), Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Issue_Reply 0]
      (genesis_system toy_digest profile R0)"
  shows "\<not> once_only toy_right (sys_released \<sigma>)"
proof -
  have released: "sys_released \<sigma> = [(0, Toy_Token (retained_provider R0)), (1, Toy_Token (retained_provider R0))]"
    unfolding \<sigma>_def using accepted by (simp add: boundary_run_simps)
  show ?thesis
    unfolding released
    by (rule two_positions_break_once_only[of 0 "Toy_Token (retained_provider R0)" _ 1
        "Toy_Token (retained_provider R0)"]) simp_all
qed

lemma storage_only_refusal_of_the_start_copy_cannot_reopen_after_a_plain_crash:
  assumes refused: "\<not> accept (genesis_disk toy_digest profile R0)"
  shows "sys_endpoint (fold (disk_only_step accept toy_step toy_digest profile)
      [Crash_Endpoint, Reopen_Endpoint (toy_attachment profile c)] (genesis_system toy_digest profile R0)) = None"
  using refused by (simp add: boundary_run_simps)

subsection \<open>The address premise of the crash theorem is satisfiable\<close>

definition list_digest ::
    "(bool \<times> recovery_profile \<times> nat \<times> retained_product) list persisted_commit \<Rightarrow>
     (bool \<times> recovery_profile \<times> nat \<times> retained_product) list" where
  "list_digest r = (image_parent r \<noteq> None, image_profile r, image_sequence r, image_records r) #
     (case image_parent r of None \<Rightarrow> [] | Some d \<Rightarrow> d)"

lemma list_digest_is_injective: "inj list_digest"
proof (rule injI)
  fix r r' :: "(bool \<times> recovery_profile \<times> nat \<times> retained_product) list persisted_commit"
  assume same: "list_digest r = list_digest r'"
  then have parts: "(image_parent r \<noteq> None) = (image_parent r' \<noteq> None)" "image_profile r = image_profile r'"
      "image_sequence r = image_sequence r'" "image_records r = image_records r'"
      "(case image_parent r of None \<Rightarrow> [] | Some d \<Rightarrow> d) = (case image_parent r' of None \<Rightarrow> [] | Some d \<Rightarrow> d)"
    by (simp_all add: list_digest_def)
  have "image_parent r = image_parent r'"
    using parts(1,5) by (cases "image_parent r"; cases "image_parent r'") simp_all
  then show "r = r'" using parts(2-4) by (cases r; cases r') simp
qed

lemma the_crash_theorem_applies_to_a_nontrivial_reopen:
  fixes c profile R0
  defines "\<sigma> \<equiv> fold (boundary_step toy_step list_digest profile)
      [Ask c Toy_Spend, Flush_Record 0, Publish_Head 0, Select_Head 0, Crash_Endpoint]
      (genesis_system list_digest profile R0)"
  shows "\<exists>h. witnessed_reopen list_digest profile (toy_attachment profile c) (sys_disk \<sigma>) (sys_witness \<sigma>) =
      Some (h, toy_bump R0)"
    and "ghost_word \<sigma> = [(c, Toy_Spend)]"
    and "run_product_action_word toy_step (ghost_word \<sigma>) R0 = toy_bump R0"
  unfolding \<sigma>_def by (simp_all add: boundary_run_simps list_digest_def)

subsection \<open>Under any rollback, every reopened state is still an actual product run\<close>

definition word_reachable where
  "word_reachable step R0 R \<longleftrightarrow> (\<exists>w. R = run_product_action_word step w R0)"

definition archive_reachable where
  "archive_reachable step R0 disk \<longleftrightarrow>
    (\<forall>h r. flushed_records disk h = Some r \<longrightarrow> word_reachable step R0 (image_records r))"

definition rollback_invariant where
  "rollback_invariant step R0 \<sigma> \<longleftrightarrow>
    (\<forall>h R. sys_endpoint \<sigma> = Some (h, R) \<longrightarrow> word_reachable step R0 R) \<and>
    (\<forall>p \<in> set (sys_staged \<sigma>). word_reachable step R0 (image_records (staged_record p))) \<and>
    archive_reachable step R0 (sys_disk \<sigma>) \<and>
    (\<forall>d \<in> set (ghost_disks \<sigma>). archive_reachable step R0 d)"

lemma word_reachable_start [simp]: "word_reachable step R0 R0"
  unfolding word_reachable_def by (rule exI[of _ "[]"]) simp

lemma word_reachable_step:
  assumes "word_reachable step R0 R"
  shows "word_reachable step R0 (fst (step c a R))"
proof -
  obtain w where w: "R = run_product_action_word step w R0" using assms unfolding word_reachable_def by blast
  have "fst (step c a R) = run_product_action_word step (w @ [(c, a)]) R0" using w by (simp add: product_word_snoc)
  then show ?thesis unfolding word_reachable_def by blast
qed

lemma archive_reachable_flush:
  assumes "archive_reachable step R0 disk" "word_reachable step R0 (image_records record)"
  shows "archive_reachable step R0 (flush_commit_record digest record disk)"
  using assms unfolding archive_reachable_def flush_commit_record_def Let_def by auto

lemma archive_reachable_publish:
  "archive_reachable step R0 disk \<Longrightarrow> archive_reachable step R0 (publish_recovery_head digest expected record disk)"
  unfolding archive_reachable_def publish_recovery_head_def by simp

lemma archive_reachable_head:
  "archive_reachable step R0 disk \<Longrightarrow> archive_reachable step R0 (disk\<lparr>committed_head := head\<rparr>)"
  unfolding archive_reachable_def by simp

lemma reopen_is_archive_reachable:
  assumes archive: "archive_reachable step R0 disk"
    and reopened: "witnessed_reopen digest profile attachment disk w = Some (h, R)"
  shows "word_reachable step R0 R"
proof -
  obtain r where r: "flushed_records disk h = Some r" "image_records r = R"
    using witnessed_reopen_returns_the_witnessed_record[OF reopened] by blast
  have "word_reachable step R0 (image_records r)" using archive r(1) unfolding archive_reachable_def by blast
  then show ?thesis using r(2) by simp
qed

lemma rollback_step_keeps_reachability:
  assumes inv: "rollback_invariant step R0 \<sigma>"
  shows "rollback_invariant step R0 (boundary_step step digest profile e \<sigma>)"
proof (cases e)
  case (Ask c a)
  show ?thesis
  proof (cases "sys_endpoint \<sigma>")
    case None
    then show ?thesis using inv Ask by (simp add: request_effect_def)
  next
    case (Some endpoint)
    then obtain base R where endpoint: "sys_endpoint \<sigma> = Some (base, R)" by (cases endpoint) auto
    have reach: "word_reachable step R0 R" using inv endpoint unfolding rollback_invariant_def by blast
    have next_reach: "word_reachable step R0 (fst (step c a R))" using reach by (rule word_reachable_step)
    show ?thesis
      using inv Ask endpoint next_reach
      by (auto simp: rollback_invariant_def request_effect_def stage_step_def staged_commit_def)
  qed
next
  case (Flush_Record i)
  have flushed: "archive_reachable step R0 (flush_commit_record digest (staged_record (sys_staged \<sigma> ! i)) (sys_disk \<sigma>))"
    if i: "i < length (sys_staged \<sigma>)"
  proof -
    have "word_reachable step R0 (image_records (staged_record (sys_staged \<sigma> ! i)))"
      using inv nth_mem[OF i] unfolding rollback_invariant_def by blast
    then show ?thesis using inv unfolding rollback_invariant_def by (blast intro: archive_reachable_flush)
  qed
  show ?thesis using inv Flush_Record flushed by (auto simp: rollback_invariant_def flush_effect_def)
next
  case (Publish_Head i)
  have published: "archive_reachable step R0 (publish_recovery_head digest expected candidate (sys_disk \<sigma>))"
    for expected candidate
    using inv unfolding rollback_invariant_def by (blast intro: archive_reachable_publish)
  show ?thesis using inv Publish_Head published by (auto simp: rollback_invariant_def publish_effect_def Let_def)
next
  case (Select_Head i)
  have advanced: "\<forall>h R. advance_endpoint (sys_staged \<sigma> ! i) h' (sys_endpoint \<sigma>) = Some (h, R) \<longrightarrow>
      word_reachable step R0 R" if i: "i < length (sys_staged \<sigma>)" for h'
  proof -
    have staged: "word_reachable step R0 (image_records (staged_record (sys_staged \<sigma> ! i)))"
      using inv nth_mem[OF i] unfolding rollback_invariant_def by blast
    show ?thesis
      using inv staged unfolding rollback_invariant_def advance_endpoint_def by (auto split: option.splits if_splits)
  qed
  show ?thesis using inv Select_Head advanced
    by (auto simp: rollback_invariant_def select_effect_def Let_def split: option.splits)
next
  case (Issue_Reply i)
  then show ?thesis using inv by (simp add: rollback_invariant_def issue_effect_def Let_def)
next
  case Repair_Head
  have repaired: "archive_reachable step R0 ((sys_disk \<sigma>)\<lparr>committed_head := head\<rparr>)" for head
    using inv unfolding rollback_invariant_def by (blast intro: archive_reachable_head)
  show ?thesis using inv Repair_Head repaired by (auto simp: rollback_invariant_def repair_effect_def)
next
  case Crash_Endpoint
  then show ?thesis using inv by (simp add: rollback_invariant_def)
next
  case (Reopen_Endpoint attachment)
  have reopened: "\<forall>h R. witnessed_reopen digest profile attachment (sys_disk \<sigma>) (sys_witness \<sigma>) = Some (h, R) \<longrightarrow>
      word_reachable step R0 R"
    using inv reopen_is_archive_reachable unfolding rollback_invariant_def by blast
  show ?thesis using inv Reopen_Endpoint reopened by (simp add: rollback_invariant_def reopen_effect_def)
next
  case (Roll_Back_Disk k)
  have rolled: "archive_reachable step R0 (ghost_disks \<sigma> ! k)" if k: "k < length (ghost_disks \<sigma>)"
    using inv nth_mem[OF k] unfolding rollback_invariant_def by blast
  show ?thesis using inv Roll_Back_Disk rolled by (auto simp: rollback_invariant_def roll_back_disk_effect_def)
next
  case (Roll_Back_Witness k)
  then show ?thesis using inv by (simp add: rollback_invariant_def roll_back_witness_effect_def)
qed

lemma genesis_keeps_reachability: "rollback_invariant step R0 (genesis_system digest profile R0)"
  by (auto simp: rollback_invariant_def archive_reachable_def genesis_system_def genesis_disk_def genesis_record_def
      split: if_splits)

lemma fold_keeps_reachability:
  "rollback_invariant step R0 \<sigma> \<Longrightarrow> rollback_invariant step R0 (fold (boundary_step step digest profile) events \<sigma>)"
proof (induction events arbitrary: \<sigma>)
  case Nil
  then show ?case by simp
next
  case (Cons e rest)
  show ?case using Cons.IH[OF rollback_step_keeps_reachability[OF Cons.prems]] by simp
qed

theorem every_reopened_state_after_any_rollback_is_an_actual_product_run:
  assumes run: "\<sigma> = fold (boundary_step step digest profile) events (genesis_system digest profile R0)"
  shows "witnessed_reopen digest profile attachment (sys_disk \<sigma>) (sys_witness \<sigma>) = Some (h, R) \<Longrightarrow>
      \<exists>w. R = run_product_action_word step w R0"
    and "sys_endpoint \<sigma> = Some (h, R) \<Longrightarrow> \<exists>w. R = run_product_action_word step w R0"
proof -
  have inv: "rollback_invariant step R0 \<sigma>"
    unfolding run by (rule fold_keeps_reachability[OF genesis_keeps_reachability])
  show "\<exists>w. R = run_product_action_word step w R0"
    if "witnessed_reopen digest profile attachment (sys_disk \<sigma>) (sys_witness \<sigma>) = Some (h, R)"
  proof -
    have "archive_reachable step R0 (sys_disk \<sigma>)" using inv unfolding rollback_invariant_def by blast
    then have "word_reachable step R0 R" using that by (rule reopen_is_archive_reachable)
    then show ?thesis unfolding word_reachable_def .
  qed
  show "\<exists>w. R = run_product_action_word step w R0" if "sys_endpoint \<sigma> = Some (h, R)"
    using inv that unfolding rollback_invariant_def word_reachable_def by blast
qed

context source_attestation
begin

theorem every_reopened_product_state_after_any_rollback_keeps_the_reservation_contract:
  fixes execute :: "authority_connection \<Rightarrow> 'token retained_service_action \<Rightarrow> retained_product \<Rightarrow> retained_product \<times> scheduled_service_reply"
    and directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
  defines "execute \<equiv> schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack"
  assumes run: "\<sigma> = fold (boundary_step execute digest profile) events
      (genesis_system digest profile (initial_promotable_product balances regulatory contexts durable target provider))"
    and reopened: "witnessed_reopen digest profile attachment (sys_disk \<sigma>) (sys_witness \<sigma>) = Some (h, R)"
  shows "reservation_contract balances (core_parent (retained_core (retained_source R)))"
proof -
  obtain w where word: "R = run_product_action_word execute w
      (initial_promotable_product balances regulatory contexts durable target provider)"
    using every_reopened_state_after_any_rollback_is_an_actual_product_run(1)[OF run reopened] by blast
  show ?thesis
    unfolding word execute_def by (rule every_actual_product_word_preserves_the_public_source_reservation_contract)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms joint_rollback_releases_one_right_twice
      storage_only_recovery_that_accepts_releases_one_right_twice storage_only_recovery_that_holds_never_reopens
      storage_only_acceptance_of_the_start_copy_releases_one_right_twice
      storage_only_refusal_of_the_start_copy_cannot_reopen_after_a_plain_crash
      list_digest_is_injective the_crash_theorem_applies_to_a_nontrivial_reopen})
  then () else error "Unexpected oracle in the rollback counterexamples"
\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms every_reopened_state_after_any_rollback_is_an_actual_product_run
      source_attestation.every_reopened_product_state_after_any_rollback_keeps_the_reservation_contract})
  then () else error "Unexpected oracle in the rollback reachability theorem"
\<close>

end
