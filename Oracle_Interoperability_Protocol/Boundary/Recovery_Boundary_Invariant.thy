theory Recovery_Boundary_Invariant
  imports Recovery_Boundary_Semantics
begin

section \<open>Every crash point recovers the committed uninterrupted run\<close>

definition replies_follow_effects where
  "replies_follow_effects step \<longleftrightarrow>
    (\<forall>c a c' b R. fst (step c a R) \<noteq> R \<longrightarrow> fst (step c a R) = fst (step c' b R) \<longrightarrow>
       snd (step c a R) = snd (step c' b R))"

definition staged_well_formed where
  "staged_well_formed step digest p \<longleftrightarrow>
    (\<exists>rb. head_for_record digest rb = staged_base p \<and>
       step (fst (staged_entry p)) (snd (staged_entry p)) (image_records rb) =
         (image_records (staged_record p), staged_reply p) \<and>
       image_records (staged_record p) \<noteq> image_records rb \<and>
       image_parent (staged_record p) = Some (head_digest (staged_base p)) \<and>
       image_sequence (staged_record p) = Suc (head_sequence (staged_base p)))"

definition slot_well_formed where
  "slot_well_formed step digest R0 word h k \<longleftrightarrow>
    k < length word \<and>
    (\<exists>rb r. head_for_record digest r = h \<and> image_parent r = Some (digest rb) \<and>
       step (fst (word ! k)) (snd (word ! k)) (image_records rb) =
         (image_records r, snd (run_word_transcript step word R0) ! k) \<and>
       image_records r \<noteq> image_records rb)"

definition released_matches where
  "released_matches step R0 word released \<longleftrightarrow>
    (\<forall>k r. (k, r) \<in> set released \<longrightarrow> k < length word \<and> r = snd (run_word_transcript step word R0) ! k)"

definition committed_run_invariant where
  "committed_run_invariant step digest R0 \<sigma> \<longleftrightarrow>
    (\<forall>h R. sys_endpoint \<sigma> = Some (h, R) \<longrightarrow> content_at digest h R) \<and>
    (\<forall>p \<in> set (sys_staged \<sigma>). staged_well_formed step digest p) \<and>
    content_at digest (witness_control (sys_witness \<sigma>)) (run_product_action_word step (ghost_word \<sigma>) R0) \<and>
    (replies_follow_effects step \<longrightarrow> released_matches step R0 (ghost_word \<sigma>) (sys_released \<sigma>)) \<and>
    (\<forall>h k. ghost_slot \<sigma> h = Some k \<longrightarrow> slot_well_formed step digest R0 (ghost_word \<sigma>) h k) \<and>
    (head_sequence (witness_control (sys_witness \<sigma>)) \<noteq> 0 \<longrightarrow>
       ghost_slot \<sigma> (witness_control (sys_witness \<sigma>)) \<noteq> None)"

lemma committed_run_invariant_intro:
  assumes "\<forall>h R. sys_endpoint \<sigma> = Some (h, R) \<longrightarrow> content_at digest h R"
    "\<forall>p \<in> set (sys_staged \<sigma>). staged_well_formed step digest p"
    "content_at digest (witness_control (sys_witness \<sigma>)) (run_product_action_word step (ghost_word \<sigma>) R0)"
    "replies_follow_effects step \<longrightarrow> released_matches step R0 (ghost_word \<sigma>) (sys_released \<sigma>)"
    "\<forall>h k. ghost_slot \<sigma> h = Some k \<longrightarrow> slot_well_formed step digest R0 (ghost_word \<sigma>) h k"
    "head_sequence (witness_control (sys_witness \<sigma>)) \<noteq> 0 \<longrightarrow>
       ghost_slot \<sigma> (witness_control (sys_witness \<sigma>)) \<noteq> None"
  shows "committed_run_invariant step digest R0 \<sigma>"
  using assms unfolding committed_run_invariant_def by blast

lemma slot_well_formed_intro:
  assumes "k < length word" "head_for_record digest r = h" "image_parent r = Some (digest rb)"
    "step (fst (word ! k)) (snd (word ! k)) (image_records rb) = (image_records r, snd (run_word_transcript step word R0) ! k)"
    "image_records r \<noteq> image_records rb"
  shows "slot_well_formed step digest R0 word h k"
  unfolding slot_well_formed_def using assms by blast

lemma slot_well_formed_extend:
  assumes "slot_well_formed step digest R0 word h k"
  shows "slot_well_formed step digest R0 (word @ suffix) h k"
proof -
  obtain rb r where k: "k < length word" and r: "head_for_record digest r = h" "image_parent r = Some (digest rb)"
      "step (fst (word ! k)) (snd (word ! k)) (image_records rb) = (image_records r, snd (run_word_transcript step word R0) ! k)"
      "image_records r \<noteq> image_records rb"
    using assms unfolding slot_well_formed_def by blast
  have same: "(word @ suffix) ! k = word ! k" using k by (simp add: nth_append)
  have reply: "snd (run_word_transcript step (word @ suffix) R0) ! k = snd (run_word_transcript step word R0) ! k"
    using k by (rule transcript_prefix)
  show ?thesis
  proof (rule slot_well_formed_intro[where rb = rb and r = r])
    show "k < length (word @ suffix)" using k by simp
    show "head_for_record digest r = h" by (rule r(1))
    show "image_parent r = Some (digest rb)" by (rule r(2))
    show "step (fst ((word @ suffix) ! k)) (snd ((word @ suffix) ! k)) (image_records rb) =
        (image_records r, snd (run_word_transcript step (word @ suffix) R0) ! k)"
      unfolding same reply by (rule r(3))
    show "image_records r \<noteq> image_records rb" by (rule r(4))
  qed
qed

lemma released_matches_extend:
  assumes "released_matches step R0 word released"
  shows "released_matches step R0 (word @ suffix) released"
  unfolding released_matches_def
proof (intro allI impI)
  fix k r
  assume "(k, r) \<in> set released"
  then have "k < length word" "r = snd (run_word_transcript step word R0) ! k"
    using assms unfolding released_matches_def by blast+
  then show "k < length (word @ suffix) \<and> r = snd (run_word_transcript step (word @ suffix) R0) ! k"
    by (simp add: transcript_prefix)
qed

lemma released_matches_snoc:
  assumes "released_matches step R0 word released"
    and "k < length word" and "r = snd (run_word_transcript step word R0) ! k"
  shows "released_matches step R0 word (released @ [(k, r)])"
  using assms unfolding released_matches_def by auto

lemma request_keeps_the_committed_run:
  assumes digest: "inj digest" and inv: "committed_run_invariant step digest R0 \<sigma>"
  shows "committed_run_invariant step digest R0 (request_effect step profile witness_fresh c a \<sigma>)"
proof (cases "sys_endpoint \<sigma>")
  case None
  then show ?thesis using inv by (simp add: request_effect_def)
next
  case (Some endpoint)
  then obtain base R where endpoint: "sys_endpoint \<sigma> = Some (base, R)" by (cases endpoint) auto
  have base_content: "content_at digest base R" using inv endpoint by (simp add: committed_run_invariant_def)
  then obtain rb where rb: "head_for_record digest rb = base" "image_records rb = R" by (auto simp: content_at_def)
  show ?thesis
  proof (cases "fst (step c a R) = R")
    case False
    let ?p = "\<lparr>staged_entry = (c, a), staged_record = staged_commit profile base (fst (step c a R)),
        staged_reply = snd (step c a R), staged_base = base\<rparr>"
    have formed: "staged_well_formed step digest ?p"
      unfolding staged_well_formed_def using rb False by (auto simp: staged_commit_def intro!: exI[of _ rb])
    have "request_effect step profile witness_fresh c a \<sigma> = \<sigma>\<lparr>sys_staged := sys_staged \<sigma> @ [?p]\<rparr>"
      using endpoint False by (simp add: request_effect_def stage_step_def)
    then show ?thesis using inv formed by (simp add: committed_run_invariant_def)
  next
    case read: True
    show ?thesis
    proof (cases "witness_fresh \<sigma> base")
      case False
      then show ?thesis using inv endpoint read by (simp add: request_effect_def)
    next
      case fresh: True
      let ?W = "ghost_word \<sigma>"
      have witness_content: "content_at digest (witness_control (sys_witness \<sigma>)) (run_product_action_word step ?W R0)"
        using inv by (simp add: committed_run_invariant_def)
      have at_base: "witness_control (sys_witness \<sigma>) = base" using fresh by (simp add: witness_fresh_def)
      have current: "R = run_product_action_word step ?W R0"
        using content_at_unique[OF digest] base_content witness_content at_base by metis
      have effect: "request_effect step profile witness_fresh c a \<sigma> =
          \<sigma>\<lparr>sys_released := sys_released \<sigma> @ [(length ?W, snd (step c a R))], ghost_word := ?W @ [(c, a)]\<rparr>"
        using endpoint read fresh by (simp add: request_effect_def)
      have word: "run_product_action_word step (?W @ [(c, a)]) R0 = R"
        using read current by (simp add: product_word_snoc)
      have reply: "snd (run_word_transcript step (?W @ [(c, a)]) R0) ! length ?W = snd (step c a R)"
        using current by (simp add: transcript_snoc_last)
      have released: "replies_follow_effects step \<longrightarrow>
          released_matches step R0 (?W @ [(c, a)]) (sys_released \<sigma> @ [(length ?W, snd (step c a R))])"
      proof
        assume rfe: "replies_follow_effects step"
        then have old: "released_matches step R0 ?W (sys_released \<sigma>)" using inv by (simp add: committed_run_invariant_def)
        have extended: "released_matches step R0 (?W @ [(c, a)]) (sys_released \<sigma>)"
          using old by (rule released_matches_extend)
        show "released_matches step R0 (?W @ [(c, a)]) (sys_released \<sigma> @ [(length ?W, snd (step c a R))])"
          using extended by (rule released_matches_snoc) (simp, rule reply[symmetric])
      qed
      have slots: "\<forall>h k. ghost_slot \<sigma> h = Some k \<longrightarrow> slot_well_formed step digest R0 (?W @ [(c, a)]) h k"
      proof (intro allI impI)
        fix h k
        assume "ghost_slot \<sigma> h = Some k"
        then have "slot_well_formed step digest R0 ?W h k" using inv unfolding committed_run_invariant_def by blast
        then show "slot_well_formed step digest R0 (?W @ [(c, a)]) h k" by (rule slot_well_formed_extend)
      qed
      show ?thesis
        unfolding effect using inv word base_content at_base released slots
        by (simp add: committed_run_invariant_def)
    qed
  qed
qed

lemma select_keeps_the_committed_run:
  assumes digest: "inj digest" and inv: "committed_run_invariant step digest R0 \<sigma>"
  shows "committed_run_invariant step digest R0 (select_effect digest i \<sigma>)"
proof -
  let ?p = "sys_staged \<sigma> ! i"
  let ?h = "head_for_record digest (staged_record ?p)"
  let ?w = "sys_witness \<sigma>"
  let ?W = "ghost_word \<sigma>"
  let ?w' = "?w\<lparr>witness_version := Suc (witness_version ?w), witness_control := ?h\<rparr>"
  show ?thesis
  proof (cases "i < length (sys_staged \<sigma>) \<and> committed_head (sys_disk \<sigma>) = Some ?h \<and>
      witness_control ?w = staged_base ?p \<and> flushed_records (sys_disk \<sigma>) ?h = Some (staged_record ?p)")
    case False
    then have "select_effect digest i \<sigma> = \<sigma>"
      by (auto simp: select_effect_def selection_proposal_def Let_def)
    then show ?thesis using inv by simp
  next
    case True
    then have i: "i < length (sys_staged \<sigma>)" and base: "witness_control ?w = staged_base ?p" by auto
    have effect: "select_effect digest i \<sigma> = \<sigma>\<lparr>sys_witness := ?w', sys_endpoint := advance_endpoint ?p ?h (sys_endpoint \<sigma>),
        ghost_word := ?W @ [staged_entry ?p], ghost_slot := (ghost_slot \<sigma>)(?h := Some (length ?W)),
        ghost_cuts := ghost_cuts \<sigma> @ [?w']\<rparr>"
      using True by (simp add: select_effect_def selection_proposal_def Let_def)
    have staged: "staged_well_formed step digest ?p" using inv i by (simp add: committed_run_invariant_def)
    then obtain rb where rb: "head_for_record digest rb = staged_base ?p"
        "step (fst (staged_entry ?p)) (snd (staged_entry ?p)) (image_records rb) =
           (image_records (staged_record ?p), staged_reply ?p)"
        "image_records (staged_record ?p) \<noteq> image_records rb"
        "image_parent (staged_record ?p) = Some (head_digest (staged_base ?p))"
      unfolding staged_well_formed_def by blast
    have witness_content: "content_at digest (witness_control ?w) (run_product_action_word step ?W R0)"
      using inv by (simp add: committed_run_invariant_def)
    have rb_content: "content_at digest (witness_control ?w) (image_records rb)"
      using base rb(1) content_at_record[of digest rb] by simp
    have base_state: "image_records rb = run_product_action_word step ?W R0"
      using content_at_unique[OF digest rb_content witness_content] .
    have new_state: "run_product_action_word step (?W @ [staged_entry ?p]) R0 = image_records (staged_record ?p)"
      using rb(2) base_state by (simp add: product_word_snoc)
    have new_reply: "snd (run_word_transcript step (?W @ [staged_entry ?p]) R0) ! length ?W = staged_reply ?p"
      using rb(2) base_state by (simp add: transcript_snoc_last)
    have parent: "image_parent (staged_record ?p) = Some (digest rb)"
      using rb(1)[symmetric] rb(4) by (simp add: head_for_record_def)
    have new_slot: "slot_well_formed step digest R0 (?W @ [staged_entry ?p]) ?h (length ?W)"
    proof (rule slot_well_formed_intro[where rb = rb and r = "staged_record ?p"])
      show "length ?W < length (?W @ [staged_entry ?p])" by simp
      show "head_for_record digest (staged_record ?p) = ?h" by (rule refl)
      show "image_parent (staged_record ?p) = Some (digest rb)" by (rule parent)
      show "step (fst ((?W @ [staged_entry ?p]) ! length ?W)) (snd ((?W @ [staged_entry ?p]) ! length ?W)) (image_records rb) =
          (image_records (staged_record ?p), snd (run_word_transcript step (?W @ [staged_entry ?p]) R0) ! length ?W)"
        unfolding nth_append_length new_reply by (rule rb(2))
      show "image_records (staged_record ?p) \<noteq> image_records rb" by (rule rb(3))
    qed
    have endpoint: "\<forall>h' R'. advance_endpoint ?p ?h (sys_endpoint \<sigma>) = Some (h', R') \<longrightarrow> content_at digest h' R'"
      using inv by (auto simp: committed_run_invariant_def advance_endpoint_def split: option.splits if_splits)
    have slots: "\<forall>h' k. ((ghost_slot \<sigma>)(?h := Some (length ?W))) h' = Some k \<longrightarrow>
        slot_well_formed step digest R0 (?W @ [staged_entry ?p]) h' k"
    proof (intro allI impI)
      fix h' k
      assume found: "((ghost_slot \<sigma>)(?h := Some (length ?W))) h' = Some k"
      show "slot_well_formed step digest R0 (?W @ [staged_entry ?p]) h' k"
      proof (cases "h' = ?h")
        case True
        then show ?thesis using found new_slot by simp
      next
        case False
        then have "ghost_slot \<sigma> h' = Some k" using found by simp
        then have "slot_well_formed step digest R0 ?W h' k" using inv unfolding committed_run_invariant_def by blast
        then show ?thesis by (rule slot_well_formed_extend)
      qed
    qed
    have released: "replies_follow_effects step \<longrightarrow>
        released_matches step R0 (?W @ [staged_entry ?p]) (sys_released \<sigma>)"
    proof
      assume rfe: "replies_follow_effects step"
      then have "released_matches step R0 ?W (sys_released \<sigma>)" using inv by (simp add: committed_run_invariant_def)
      then show "released_matches step R0 (?W @ [staged_entry ?p]) (sys_released \<sigma>)" by (rule released_matches_extend)
    qed
    have staged_all: "\<forall>p \<in> set (sys_staged \<sigma>). staged_well_formed step digest p"
      using inv unfolding committed_run_invariant_def by blast
    show ?thesis
      unfolding effect
      apply (rule committed_run_invariant_intro)
      using endpoint apply simp
      using staged_all apply simp
      using new_state apply simp
      using released apply simp
      using slots apply (simp del: fun_upd_apply)
      apply simp
      done
  qed
qed

lemma issue_keeps_the_committed_run:
  assumes digest: "inj digest" and inv: "committed_run_invariant step digest R0 \<sigma>"
  shows "committed_run_invariant step digest R0 (issue_effect digest i \<sigma>)"
proof -
  let ?p = "sys_staged \<sigma> ! i"
  let ?h = "head_for_record digest (staged_record ?p)"
  let ?W = "ghost_word \<sigma>"
  show ?thesis
  proof (cases "i < length (sys_staged \<sigma>) \<and> committed_head (sys_disk \<sigma>) = Some ?h \<and>
      flushed_records (sys_disk \<sigma>) ?h = Some (staged_record ?p) \<and> witness_control (sys_witness \<sigma>) = ?h")
    case False
    then have "issue_effect digest i \<sigma> = \<sigma>" by (auto simp: issue_effect_def Let_def)
    then show ?thesis using inv by simp
  next
    case True
    then have i: "i < length (sys_staged \<sigma>)" and at: "witness_control (sys_witness \<sigma>) = ?h" by auto
    have effect: "issue_effect digest i \<sigma> =
        \<sigma>\<lparr>sys_released := sys_released \<sigma> @ [(the (ghost_slot \<sigma> ?h), staged_reply ?p)]\<rparr>"
      using True by (simp add: issue_effect_def Let_def)
    have staged: "staged_well_formed step digest ?p" using inv i by (simp add: committed_run_invariant_def)
    then obtain rb where rb: "head_for_record digest rb = staged_base ?p"
        "step (fst (staged_entry ?p)) (snd (staged_entry ?p)) (image_records rb) =
           (image_records (staged_record ?p), staged_reply ?p)"
        "image_records (staged_record ?p) \<noteq> image_records rb"
        "image_parent (staged_record ?p) = Some (head_digest (staged_base ?p))"
        "image_sequence (staged_record ?p) = Suc (head_sequence (staged_base ?p))"
      unfolding staged_well_formed_def by blast
    have sequence: "head_sequence ?h \<noteq> 0" using rb(5) by (simp add: head_for_record_def)
    obtain k where slot: "ghost_slot \<sigma> ?h = Some k"
      using inv at sequence by (auto simp: committed_run_invariant_def)
    have formed: "slot_well_formed step digest R0 ?W ?h k" using inv slot unfolding committed_run_invariant_def by blast
    then obtain rb' r where k: "k < length ?W" and r: "head_for_record digest r = ?h"
        "image_parent r = Some (digest rb')"
        "step (fst (?W ! k)) (snd (?W ! k)) (image_records rb') = (image_records r, snd (run_word_transcript step ?W R0) ! k)"
        "image_records r \<noteq> image_records rb'"
      unfolding slot_well_formed_def by blast
    have same_record: "r = staged_record ?p"
      by (rule addressed_records_are_unique[OF digest]) (simp add: r(1))
    have parent: "image_parent (staged_record ?p) = Some (digest rb)"
      using rb(1)[symmetric] rb(4) by (simp add: head_for_record_def)
    have same_base: "rb' = rb"
    proof (rule digest[THEN injD])
      show "digest rb' = digest rb" using r(2) same_record parent by simp
    qed
    have released: "replies_follow_effects step \<longrightarrow>
        released_matches step R0 ?W (sys_released \<sigma> @ [(the (ghost_slot \<sigma> ?h), staged_reply ?p)])"
    proof
      assume rfe: "replies_follow_effects step"
      have old: "released_matches step R0 ?W (sys_released \<sigma>)" using inv rfe by (simp add: committed_run_invariant_def)
      have other: "step (fst (?W ! k)) (snd (?W ! k)) (image_records rb) =
          (image_records (staged_record ?p), snd (run_word_transcript step ?W R0) ! k)"
        using r(3) same_record same_base by simp
      have moved: "fst (step (fst (staged_entry ?p)) (snd (staged_entry ?p)) (image_records rb)) \<noteq> image_records rb"
        using rb(2,3) by simp
      have effects: "fst (step (fst (staged_entry ?p)) (snd (staged_entry ?p)) (image_records rb)) =
          fst (step (fst (?W ! k)) (snd (?W ! k)) (image_records rb))"
        using rb(2) other by simp
      have replies: "snd (step (fst (staged_entry ?p)) (snd (staged_entry ?p)) (image_records rb)) =
          snd (step (fst (?W ! k)) (snd (?W ! k)) (image_records rb))"
        using rfe moved effects unfolding replies_follow_effects_def by blast
      have reply_k: "staged_reply ?p = snd (run_word_transcript step ?W R0) ! k"
        using rb(2) other replies by simp
      have the_slot: "the (ghost_slot \<sigma> ?h) = k" using slot by simp
      show "released_matches step R0 ?W (sys_released \<sigma> @ [(the (ghost_slot \<sigma> ?h), staged_reply ?p)])"
        unfolding the_slot by (rule released_matches_snoc[OF old k reply_k])
    qed
    show ?thesis unfolding effect using inv released by (simp add: committed_run_invariant_def)
  qed
qed

lemma reopen_keeps_the_committed_run:
  assumes inv: "committed_run_invariant step digest R0 \<sigma>"
  shows "committed_run_invariant step digest R0 (reopen_effect digest profile attachment \<sigma>)"
proof -
  have "\<forall>h R. witnessed_reopen digest profile attachment (sys_disk \<sigma>) (sys_witness \<sigma>) = Some (h, R) \<longrightarrow>
      content_at digest h R"
    by (auto dest!: witnessed_reopen_returns_the_witnessed_record simp: content_at_def)
  then show ?thesis using inv by (simp add: reopen_effect_def committed_run_invariant_def)
qed

lemma boundary_step_keeps_the_committed_run:
  assumes digest: "inj digest" and inv: "committed_run_invariant step digest R0 \<sigma>"
    and honest: "\<not> is_witness_rollback e"
  shows "committed_run_invariant step digest R0 (boundary_step step digest profile e \<sigma>)"
proof (cases e)
  case (Ask c a)
  then show ?thesis using request_keeps_the_committed_run[OF digest inv] by simp
next
  case (Flush_Record i)
  then show ?thesis using inv by (simp add: flush_effect_def committed_run_invariant_def)
next
  case (Publish_Head i)
  then show ?thesis using inv by (simp add: publish_effect_def committed_run_invariant_def Let_def)
next
  case (Select_Head i)
  then show ?thesis using select_keeps_the_committed_run[OF digest inv] by simp
next
  case (Issue_Reply i)
  then show ?thesis using issue_keeps_the_committed_run[OF digest inv] by simp
next
  case Repair_Head
  then show ?thesis using inv by (simp add: repair_effect_def committed_run_invariant_def)
next
  case Crash_Endpoint
  then show ?thesis using inv by (simp add: committed_run_invariant_def)
next
  case (Reopen_Endpoint attachment)
  then show ?thesis using reopen_keeps_the_committed_run[OF inv] by simp
next
  case (Roll_Back_Disk k)
  then show ?thesis using inv by (simp add: roll_back_disk_effect_def committed_run_invariant_def)
next
  case (Roll_Back_Witness k)
  then show ?thesis using honest by simp
qed

lemma fold_keeps_the_committed_run:
  assumes digest: "inj digest" and inv: "committed_run_invariant step digest R0 \<sigma>"
    and honest: "\<forall>e \<in> set events. \<not> is_witness_rollback e"
  shows "committed_run_invariant step digest R0 (fold (boundary_step step digest profile) events \<sigma>)"
  using inv honest
proof (induction events arbitrary: \<sigma>)
  case Nil
  then show ?case by simp
next
  case (Cons e rest)
  have next_state: "committed_run_invariant step digest R0 (boundary_step step digest profile e \<sigma>)"
    using boundary_step_keeps_the_committed_run[OF digest Cons.prems(1)] Cons.prems(2) by simp
  show ?case using Cons.IH[OF next_state] Cons.prems(2) by simp
qed

lemma genesis_has_the_committed_run:
  "committed_run_invariant step digest R0 (genesis_system digest profile R0)"
proof -
  have "content_at digest (head_for_record digest (genesis_record profile R0)) R0"
    using content_at_record[of digest "genesis_record profile R0"] by (simp add: genesis_record_def)
  then show ?thesis
    by (simp add: committed_run_invariant_def genesis_system_def genesis_cut_def released_matches_def
        head_for_record_def genesis_record_def)
qed

theorem every_crash_point_recovers_the_committed_uninterrupted_run:
  assumes run: "\<sigma> = fold (boundary_step step digest profile) events (genesis_system digest profile R0)"
    and honest_witness: "\<forall>e \<in> set events. \<not> is_witness_rollback e"
    and digest: "inj digest"
  shows "witnessed_reopen digest profile attachment (sys_disk \<sigma>) (sys_witness \<sigma>) = Some (h, R) \<Longrightarrow>
      R = run_product_action_word step (ghost_word \<sigma>) R0"
    and "sys_endpoint \<sigma> = Some (h, R) \<Longrightarrow> h = witness_control (sys_witness \<sigma>) \<Longrightarrow>
      R = run_product_action_word step (ghost_word \<sigma>) R0"
    and "replies_follow_effects step \<Longrightarrow> (k, r) \<in> set (sys_released \<sigma>) \<Longrightarrow>
      k < length (ghost_word \<sigma>) \<and> r = snd (run_word_transcript step (ghost_word \<sigma>) R0) ! k"
proof -
  have inv: "committed_run_invariant step digest R0 \<sigma>"
    unfolding run by (rule fold_keeps_the_committed_run[OF digest genesis_has_the_committed_run honest_witness])
  have witness: "content_at digest (witness_control (sys_witness \<sigma>)) (run_product_action_word step (ghost_word \<sigma>) R0)"
    using inv by (simp add: committed_run_invariant_def)
  show "R = run_product_action_word step (ghost_word \<sigma>) R0"
    if "witnessed_reopen digest profile attachment (sys_disk \<sigma>) (sys_witness \<sigma>) = Some (h, R)"
  proof -
    have "h = witness_control (sys_witness \<sigma>)" "content_at digest h R"
      using witnessed_reopen_returns_the_witnessed_record[OF that] by (auto simp: content_at_def)
    then show ?thesis using content_at_unique[OF digest] witness by metis
  qed
  show "R = run_product_action_word step (ghost_word \<sigma>) R0"
    if "sys_endpoint \<sigma> = Some (h, R)" "h = witness_control (sys_witness \<sigma>)"
  proof -
    have "content_at digest h R" using inv that(1) by (simp add: committed_run_invariant_def)
    then show ?thesis using content_at_unique[OF digest] witness that(2) by metis
  qed
  show "k < length (ghost_word \<sigma>) \<and> r = snd (run_word_transcript step (ghost_word \<sigma>) R0) ! k"
    if "replies_follow_effects step" "(k, r) \<in> set (sys_released \<sigma>)"
    using inv that by (simp add: committed_run_invariant_def released_matches_def)
qed

corollary the_recorded_state_premise_is_a_consequence:
  assumes run: "\<sigma> = fold (boundary_step step digest profile) events (genesis_system digest profile R0)"
    and honest_witness: "\<forall>e \<in> set events. \<not> is_witness_rollback e"
    and digest: "inj digest"
    and at_witness: "head_for_record digest stored = witness_control (sys_witness \<sigma>)"
  shows "image_records stored = capture_retained_product (reopen_retained_product connection
      (run_product_action_word step (ghost_word \<sigma>) R0))"
proof -
  have inv: "committed_run_invariant step digest R0 \<sigma>"
    unfolding run by (rule fold_keeps_the_committed_run[OF digest genesis_has_the_committed_run honest_witness])
  have witness: "content_at digest (witness_control (sys_witness \<sigma>)) (run_product_action_word step (ghost_word \<sigma>) R0)"
    using inv by (simp add: committed_run_invariant_def)
  have "content_at digest (witness_control (sys_witness \<sigma>)) (image_records stored)"
    using at_witness content_at_record[of digest stored] by simp
  then have "image_records stored = run_product_action_word step (ghost_word \<sigma>) R0"
    using content_at_unique[OF digest] witness by metis
  then show ?thesis by (simp add: product_round_trip_preserves_the_durable_projection)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms every_crash_point_recovers_the_committed_uninterrupted_run
      the_recorded_state_premise_is_a_consequence})
  then () else error "Unexpected oracle in the committed run invariant"
\<close>

end
