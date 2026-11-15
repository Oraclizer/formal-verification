theory Request_Progress
  imports REOS_Open_Scheduler.Interference_Bounds DOSP_Progress.Recovery_Progress
begin

section \<open>A finite cohort inside an open queue\<close>

definition ordinary_ids :: "scheduler_state \<Rightarrow> nat set"
where "ordinary_ids s = set (map packet_identity (ordinary_queue s))"

definition coherent_ordinary_queue :: "scheduler_state \<Rightarrow> bool"
where
  "coherent_ordinary_queue s \<longleftrightarrow>
    ordinary_shape s \<and> distinct (map packet_identity (ordinary_queue s)) \<and>
    ordinary_ids s \<subseteq> dedup_ids s \<and> dom (ordinary_receipts s) \<subseteq> dedup_ids s \<and>
    ordinary_ids s \<inter> dom (ordinary_receipts s) = {}"

definition tracked_prefix :: "nat set \<Rightarrow> packet list \<Rightarrow> bool"
where
  "tracked_prefix keys ps \<longleftrightarrow>
    (\<exists>front outside. ps = front @ outside \<and>
      set (map packet_identity front) \<subseteq> keys \<and> set (map packet_identity outside) \<inter> keys = {})"

definition cohort_pending :: "nat set \<Rightarrow> scheduler_state \<Rightarrow> nat set"
where "cohort_pending keys s = ordinary_ids s \<inter> keys"

definition cohort_done :: "nat set \<Rightarrow> scheduler_state \<Rightarrow> nat set"
where "cohort_done keys s = dom (ordinary_receipts s) \<inter> keys"

definition cohort_finished ::
  "nat set \<Rightarrow> (scheduler_state,scheduler_action,scheduler_result) transition \<Rightarrow> nat set"
where "cohort_finished keys e = {q \<in> keys. served_ordinary q e}"

lemma scheduler_ordinarily_coherent:
  assumes step: "scheduler_step s action outcome t" and inv: "coherent_ordinary_queue s"
  shows "coherent_ordinary_queue t"
  using step
proof (cases rule: ordinary_queue_update)
  case same
  with inv show ?thesis
    by (auto simp: ordinary_ids_def ordinary_shape_def coherent_ordinary_queue_def)
next
  case (push p)
  with inv show ?thesis
    by (auto simp: ordinary_ids_def ordinary_shape_def coherent_ordinary_queue_def)
next
  case (pop p ps)
  have shape: "ordinary_shape t" using step inv
    by (auto simp: coherent_ordinary_queue_def intro: ordinary_shape_preserved)
  from pop inv have "packet_identity p \<notin> ordinary_ids t"
    by (simp add: coherent_ordinary_queue_def ordinary_ids_def)
  moreover have receipt_domain:
    "dom (ordinary_receipts t) = insert (packet_identity p) (dom (ordinary_receipts s))"
    using pop(5) by (auto simp: dom_def)
  moreover from pop have src_ids: "ordinary_ids s = insert (packet_identity p) (ordinary_ids t)"
    by (simp add: ordinary_ids_def)
  ultimately show ?thesis using inv pop shape
    by (auto simp: coherent_ordinary_queue_def ordinary_ids_def)
qed

lemma admitted_keys_persist:
  assumes "scheduler_step s action outcome t" "keys \<subseteq> dedup_ids s"
  shows "keys \<subseteq> dedup_ids t"
  using assms by (cases rule: ordinary_queue_update) auto

lemma tracked_prefix_append:
  assumes "tracked_prefix keys ps" "packet_identity p \<notin> keys"
  shows "tracked_prefix keys (ps @ [p])"
proof -
  from assms(1) obtain front out where parts:
    "ps = front @ out" "set (map packet_identity front) \<subseteq> keys"
    "set (map packet_identity out) \<inter> keys = {}"
    by (auto simp: tracked_prefix_def)
  show ?thesis unfolding tracked_prefix_def
    apply (rule exI[of _ front])
    apply (rule exI[of _ "out @ [p]"])
    using parts assms(2) by auto
qed

lemma tracked_prefix_pop:
  assumes "tracked_prefix keys (p # ps)"
  shows "tracked_prefix keys ps"
proof -
  from assms obtain front out where
    headq: "p # ps = front @ out" and inside: "set (map packet_identity front) \<subseteq> keys"
    and outside: "set (map packet_identity out) \<inter> keys = {}"
    by (auto simp: tracked_prefix_def)
  show ?thesis
  proof (cases front)
    case Nil
    from Nil headq have out_eq: "out = p # ps" by simp
    then have subset: "set (map packet_identity ps) \<subseteq> set (map packet_identity out)" by auto
    from subset outside have tail_out: "set (map packet_identity ps) \<inter> keys = {}" by blast
    show ?thesis unfolding tracked_prefix_def
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ ps])
      using tail_out by simp
  next
    case (Cons h rest)
    show ?thesis unfolding tracked_prefix_def
      apply (rule exI[of _ rest])
      apply (rule exI[of _ out])
      using Cons headq inside outside by auto
  qed
qed

lemma prefix_preserved_across_scheduler:
  assumes step: "scheduler_step s action outcome t" and cut: "tracked_prefix keys (ordinary_queue s)"
    and old_keys: "keys \<subseteq> dedup_ids s"
  shows "tracked_prefix keys (ordinary_queue t)"
  using step cut old_keys by (cases rule: ordinary_queue_update)
    (auto intro: tracked_prefix_append tracked_prefix_pop)

lemma tracked_head_exists:
  assumes "tracked_prefix keys (ordinary_queue s)" "cohort_pending keys s \<noteq> {}"
  obtains p ps where "ordinary_queue s = p # ps" "packet_identity p \<in> keys"
proof -
  from assms(1) obtain front out where
    splitq: "ordinary_queue s = front @ out" and inside: "set (map packet_identity front) \<subseteq> keys"
    and outside: "set (map packet_identity out) \<inter> keys = {}"
    by (auto simp: tracked_prefix_def)
  from assms(2) splitq outside have "front \<noteq> []"
    by (auto simp: cohort_pending_def ordinary_ids_def)
  then obtain p rest where front: "front = p # rest" by (cases front) auto
  from splitq front inside show thesis by (intro that[of p "rest @ out"]) auto
qed

lemma cut_accounts_for_scheduler_step:
  assumes happens: "step_occurs scheduler_step e"
    and inv: "coherent_ordinary_queue (source_state e)"
    and keys_seen: "keys \<subseteq> dedup_ids (source_state e)"
  shows "accounts_for (cohort_pending keys) (cohort_done keys) (\<lambda>_. {}) (cohort_finished keys) e"
proof -
  let ?s = "source_state e"
  let ?t = "target_state e"
  from happens have step:
    "scheduler_step ?s (step_action e) (step_outcome e) ?t"
    by (simp add: step_occurs_def)
  have common: "finite (cohort_pending keys ?s)"
    "cohort_pending keys ?s \<inter> cohort_done keys ?s = {}"
    using inv by (auto simp: cohort_pending_def cohort_done_def ordinary_ids_def coherent_ordinary_queue_def)
  show ?thesis
    using step
  proof (cases rule: ordinary_queue_update)
    case same
    have nofinish: "cohort_finished keys e = {}"
    proof (rule ccontr)
      assume "cohort_finished keys e \<noteq> {}"
      then obtain q where "served_ordinary q e" by (auto simp: cohort_finished_def)
      with step have "scheduler_step ?s Honest_Service (Internal (Served_Ordinary q)) ?t"
        by (simp add: served_ordinary_def)
      then obtain p ps where "ordinary_queue ?s = p # ps" "ordinary_queue ?t = ps"
        by (elim ordinary_service_records_the_head_packet)
      with same(1) show False by simp
    qed
    with same common show ?thesis
      by (simp add: accounts_for_def cohort_pending_def cohort_done_def ordinary_ids_def)
  next
    case (push p)
    with keys_seen have untracked: "packet_identity p \<notin> keys" by auto
    from push untracked common show ?thesis
      by (auto simp: accounts_for_def cohort_finished_def served_ordinary_def
        cohort_pending_def cohort_done_def ordinary_ids_def)
  next
    case (pop p ps)
    with inv have fresh_tail: "packet_identity p \<notin> set (map packet_identity ps)"
      by (simp add: coherent_ordinary_queue_def)
    from pop have completed_step:
      "dom (ordinary_receipts ?t) = insert (packet_identity p) (dom (ordinary_receipts ?s))"
      by (auto simp: dom_def)
    from pop common fresh_tail completed_step show ?thesis
      by (auto simp: accounts_for_def cohort_finished_def served_ordinary_def
        cohort_pending_def cohort_done_def ordinary_ids_def)
  qed
qed

section \<open>Discharge of the supplied progress theorem\<close>

lemma ordinary_state_along_run:
  assumes occurs: "\<And>i. step_occurs scheduler_step (events i)"
    and links: "\<And>i. target_state (events i) = source_state (events (Suc i))"
    and init: "P (source_state (events 0))"
    and preserves: "\<And>e. step_occurs scheduler_step e \<Longrightarrow> P (source_state e) \<Longrightarrow> P (target_state e)"
  shows "P (source_state (events n))"
proof (induction n)
  case 0
  show ?case by (rule init)
next
  case (Suc n)
  from preserves[OF occurs[of n] Suc.IH] links[of n] show ?case by simp
qed

theorem initial_ordinary_cohort_completes:
  assumes run: "infinite_run scheduler_step initial carrier events"
    and init: "coherent_ordinary_queue (source_state (events 0))"
    and fixed: "keys = ordinary_ids (source_state (events 0))"
    and competition: "finite {i. spends_priority (events i)}"
    and opportunities: "\<And>i. \<exists>j\<ge>i. step_action (events j) = Honest_Service"
  shows "\<exists>n. \<forall>i\<ge>n. cohort_pending keys (source_state (events i)) = {} \<and>
    (\<forall>j\<le>i. cohort_pending keys (source_state (events j)) \<union> cohort_done keys (source_state (events j))
      \<subseteq> cohort_done keys (source_state (events i)))"
proof -
  let ?initial = "source_state (events 0)"
  let ?s = "\<lambda>i. source_state (events i)"
  have occurs: "\<And>i. step_occurs scheduler_step (events i)"
    and linked: "\<And>i. target_state (events i) = ?s (Suc i)"
    using run by (simp_all add: infinite_run_def)
  have from_step: "\<And>e. step_occurs scheduler_step e \<Longrightarrow>
    scheduler_step (source_state e) (step_action e) (step_outcome e) (target_state e)"
    by (simp add: step_occurs_def)
  have coh: "\<And>i. coherent_ordinary_queue (?s i)"
  proof (rule ordinary_state_along_run[where events=events and P=coherent_ordinary_queue, OF occurs linked init])
    fix e
    assume e: "step_occurs scheduler_step e" and prior: "coherent_ordinary_queue (source_state e)"
    show "coherent_ordinary_queue (target_state e)"
      by (rule scheduler_ordinarily_coherent[OF from_step[OF e] prior])
  qed
  have included_initially: "keys \<subseteq> dedup_ids ?initial" using fixed init
    by (simp add: coherent_ordinary_queue_def)
  have included: "\<And>i. keys \<subseteq> dedup_ids (?s i)"
  proof (rule ordinary_state_along_run[where events=events and P="\<lambda>s. keys \<subseteq> dedup_ids s",
        OF occurs linked included_initially])
    fix e
    assume e: "step_occurs scheduler_step e" and prior: "keys \<subseteq> dedup_ids (source_state e)"
    show "keys \<subseteq> dedup_ids (target_state e)" by (rule admitted_keys_persist[OF from_step[OF e] prior])
  qed
  have initially_front: "tracked_prefix keys (ordinary_queue ?initial)"
    unfolding tracked_prefix_def
    apply (rule exI[of _ "ordinary_queue ?initial"])
    apply (rule exI[of _ "[]"])
    by (simp add: fixed ordinary_ids_def)
  have fronts: "\<And>i. tracked_prefix keys (ordinary_queue (?s i))"
  proof -
    fix i
    show "tracked_prefix keys (ordinary_queue (?s i))"
    proof (induction i)
      case 0
      show ?case by (rule initially_front)
    next
      case (Suc i)
      from prefix_preserved_across_scheduler[OF from_step[OF occurs[of i]] Suc.IH included[of i]]
        linked[of i] show ?case by simp
    qed
  qed
  have balance: "\<And>i. accounts_for (cohort_pending keys) (cohort_done keys) (\<lambda>_. {}) (cohort_finished keys) (events i)"
    by (rule cut_accounts_for_scheduler_step[OF occurs coh included])
  have opportunity: "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> spends_priority (events j)) \<Longrightarrow>
        cohort_pending keys (?s i) \<noteq> {} \<Longrightarrow>
        \<exists>j\<ge>i. cohort_finished keys (events j) \<noteq> {}"
  proof -
    fix i
    assume quiet: "\<And>j. i \<le> j \<Longrightarrow> \<not> spends_priority (events j)"
      and work: "cohort_pending keys (?s i) \<noteq> {}"
    show "\<exists>j\<ge>i. cohort_finished keys (events j) \<noteq> {}"
    proof (rule ccontr)
      assume no_completion: "\<not> (\<exists>j\<ge>i. cohort_finished keys (events j) \<noteq> {})"
      have remains: "\<And>j. i \<le> j \<Longrightarrow> cohort_pending keys (?s j) = cohort_pending keys (?s i)"
      proof -
        fix j assume le: "i \<le> j"
        then show "cohort_pending keys (?s j) = cohort_pending keys (?s i)"
        proof (induction j)
          case 0
          then show ?case by simp
        next
          case (Suc j)
          show ?case
          proof (cases "i \<le> j")
            case True
            with no_completion have "cohort_finished keys (events j) = {}" by blast
            with balance[of j] linked[of j] have
              "cohort_pending keys (?s (Suc j)) = cohort_pending keys (?s j)"
              by (simp add: accounts_for_def)
            also have "\<dots> = cohort_pending keys (?s i)" by (rule Suc.IH[OF True])
            finally show ?thesis .
          next
            case False
            with Suc.prems have "i = Suc j" by simp
            then show ?thesis by simp
          qed
        qed
      qed
      from opportunities[of i] obtain j where ij: "i \<le> j"
        and tick: "step_action (events j) = Honest_Service" by blast
      from remains[OF ij] work have nonempty: "cohort_pending keys (?s j) \<noteq> {}" by simp
      from tracked_head_exists[OF fronts[of j] nonempty] obtain p ps where
        headq: "ordinary_queue (?s j) = p # ps" and in_cut: "packet_identity p \<in> keys" .
      have waiting: "waiting (packet_identity p) (?s j)" by (simp add: waiting_def headq)
      from coh[of j] have shape: "ordinary_shape (?s j)" by (simp add: coherent_ordinary_queue_def)
      from honest_turn_with_waiting_work_produces_service[OF shape waiting] obtain u r where
        honest: "scheduler_step (?s j) Honest_Service (Internal r) u"
        and useful: "(\<exists>q'. r = Served_Ordinary q') \<or> (\<exists>q' k. r = Served_Regulation q' k)"
        by blast
      from honest from_step[OF occurs[of j]] tick have result: "step_outcome (events j) = Internal r"
        by (simp add: scheduler_step_def)
      from useful result quiet[OF ij] obtain q' where ord: "r = Served_Ordinary q'"
        by (auto simp: spends_priority_def)
      with honest have service: "scheduler_step (?s j) Honest_Service (Internal (Served_Ordinary q')) u" by simp
      from service obtain selected rest where first: "ordinary_queue (?s j) = selected # rest"
        and ident: "q' = packet_identity selected" by (elim ordinary_service_records_the_head_packet)
      from headq first ident have equal_id: "q' = packet_identity p" by simp
      with result ord tick in_cut have "cohort_finished keys (events j) \<noteq> {}"
        by (auto simp: cohort_finished_def served_ordinary_def)
      with ij no_completion show False by blast
    qed
  qed
  show ?thesis
  proof (rule Recovery_Progress.eventual_completion_under_finite_interference[
        where admitted="\<lambda>_. {}" and interfering=spends_priority, OF run balance])
    show "\<And>i. (\<lambda>_. {}) (events i) \<noteq> {} \<Longrightarrow> spends_priority (events i)" by simp
    show "finite {i. spends_priority (events i)}" by (rule competition)
    show "\<And>i. (\<And>j. j \<ge> i \<Longrightarrow> \<not> spends_priority (events j)) \<Longrightarrow>
      cohort_pending keys (source_state (events i)) \<noteq> {} \<Longrightarrow>
      \<exists>j\<ge>i. cohort_finished keys (events j) \<noteq> {}" by (rule opportunity)
  qed
qed

section \<open>The admitted packet is the one recorded as served\<close>

lemma responsibility_for_packet_preserved:
  assumes step: "scheduler_step s action outcome t" and inv: "coherent_ordinary_queue s"
    and present: "p \<in> set (ordinary_queue s) \<or> ordinary_receipts s (packet_identity p) = Some p"
  shows "p \<in> set (ordinary_queue t) \<or> ordinary_receipts t (packet_identity p) = Some p"
  using step present inv
  by (cases rule: ordinary_queue_update)
    (auto simp: coherent_ordinary_queue_def ordinary_ids_def dom_def)

lemma receipt_requires_an_ordinary_service:
  assumes run: "infinite_run scheduler_step initial carrier events"
    and blank: "ordinary_receipts (source_state (events 0)) q = None"
    and final_value: "ordinary_receipts (source_state (events n)) q = Some p"
  shows "\<exists>j<n. served_ordinary q (events j) \<and> ordinary_receipts (target_state (events j)) q = Some p"
  using final_value
proof (induction n)
  case 0
  with blank show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "ordinary_receipts (source_state (events n)) q = Some p")
    case True
    from Suc.IH[OF this] obtain j where "j < n" "served_ordinary q (events j)"
      "ordinary_receipts (target_state (events j)) q = Some p" by blast
    then show ?thesis by (intro exI[of _ j]) simp
  next
    case False
    from run have link: "target_state (events n) = source_state (events (Suc n))"
      by (simp add: infinite_run_def)
    from run have "step_occurs scheduler_step (events n)" by (simp add: infinite_run_def)
    then have step: "scheduler_step (source_state (events n)) (step_action (events n))
        (step_outcome (events n)) (target_state (events n))" by (simp only: step_occurs_def)
    from step link Suc.prems False have "served_ordinary q (events n)"
      by (cases rule: ordinary_queue_update) (auto simp: served_ordinary_def split: if_splits)
    with link Suc.prems show ?thesis by (intro exI[of _ n]) simp
  qed
qed

theorem queued_packet_is_served_under_finite_interference:
  assumes run: "infinite_run scheduler_step initial carrier events"
    and initial_coherence: "coherent_ordinary_queue (source_state (events 0))"
    and initial_packet: "p \<in> set (ordinary_queue (source_state (events 0)))"
    and finite_interference: "finite {i. spends_priority (events i)}"
    and opportunities: "\<And>i. \<exists>j\<ge>i. step_action (events j) = Honest_Service"
  shows "\<exists>j. served_ordinary (packet_identity p) (events j) \<and>
    ordinary_receipts (target_state (events j)) (packet_identity p) = Some p"
proof -
  let ?s = "\<lambda>i. source_state (events i)"
  let ?keys = "ordinary_ids (?s 0)"
  from initial_coherence initial_packet have blank: "ordinary_receipts (?s 0) (packet_identity p) = None"
    by (auto simp: coherent_ordinary_queue_def ordinary_ids_def dom_def)
  from initial_ordinary_cohort_completes[OF run initial_coherence refl finite_interference opportunities]
  obtain n where all_covered: "cohort_pending ?keys (?s 0) \<subseteq> cohort_done ?keys (?s n)"
    by fastforce
  have occurs: "\<And>i. step_occurs scheduler_step (events i)"
    and linked: "\<And>i. target_state (events i) = ?s (Suc i)"
    using run by (simp_all add: infinite_run_def)
  have current: "\<And>i. coherent_ordinary_queue (?s i) \<and>
      (p \<in> set (ordinary_queue (?s i)) \<or> ordinary_receipts (?s i) (packet_identity p) = Some p)"
  proof -
    fix i
    show "coherent_ordinary_queue (?s i) \<and>
        (p \<in> set (ordinary_queue (?s i)) \<or> ordinary_receipts (?s i) (packet_identity p) = Some p)"
    proof (induction i)
      case 0
      show ?case using initial_packet initial_coherence by simp
    next
      case (Suc i)
      from occurs[of i] have s:
        "scheduler_step (?s i) (step_action (events i)) (step_outcome (events i)) (target_state (events i))"
        by (simp add: step_occurs_def)
      from Suc.IH have prior_queue: "coherent_ordinary_queue (?s i)"
        and prior_packet: "p \<in> set (ordinary_queue (?s i)) \<or>
          ordinary_receipts (?s i) (packet_identity p) = Some p"
        by simp_all
      have after_queue: "coherent_ordinary_queue (target_state (events i))"
        by (rule scheduler_ordinarily_coherent[OF s prior_queue])
      have "p \<in> set (ordinary_queue (target_state (events i))) \<or>
          ordinary_receipts (target_state (events i)) (packet_identity p) = Some p"
        by (rule responsibility_for_packet_preserved[OF s prior_queue prior_packet])
      with linked[of i] after_queue show ?case by simp
    qed
  qed
  from initial_packet have key: "packet_identity p \<in> ?keys" by (auto simp: ordinary_ids_def)
  with all_covered have completion_entry: "packet_identity p \<in> dom (ordinary_receipts (?s n))"
    by (auto simp: cohort_pending_def cohort_done_def)
  with current[of n] have gone: "p \<notin> set (ordinary_queue (?s n))"
    by (auto simp: coherent_ordinary_queue_def ordinary_ids_def)
  with current[of n] have exact_receipt: "ordinary_receipts (?s n) (packet_identity p) = Some p" by blast
  from receipt_requires_an_ordinary_service[OF run blank exact_receipt] show ?thesis by blast
qed

theorem admitted_packet_is_served_under_finite_interference:
  assumes origin: "coherent_ordinary_queue before"
    and accepted: "scheduler_step before (Submit p) (Accepted (packet_identity p)) admitted_state"
    and ordinary: "ordinary_body (packet_contents p)"
    and run: "infinite_run scheduler_step {admitted_state} carrier events"
    and finite_interference: "finite {i. spends_priority (events i)}"
    and opportunities: "\<And>i. \<exists>j\<ge>i. step_action (events j) = Honest_Service"
  shows "\<exists>j. served_ordinary (packet_identity p) (events j) \<and>
    ordinary_receipts (target_state (events j)) (packet_identity p) = Some p"
proof -
  from run have initial: "source_state (events 0) = admitted_state" by (simp add: infinite_run_def)
  from scheduler_ordinarily_coherent[OF accepted origin] initial have coherent:
    "coherent_ordinary_queue (source_state (events 0))" by simp
  from admitted_packet(6)[OF accepted] initial ordinary have queued:
    "p \<in> set (ordinary_queue (source_state (events 0)))" by (simp add: enqueue_packet_def Let_def)
  show ?thesis by (rule queued_packet_is_served_under_finite_interference[OF run coherent queued
        finite_interference opportunities])
qed

end
