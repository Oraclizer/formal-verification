theory Scoped_Ordinary
  imports Scoped_Machine
begin

type_synonym machine_event = "(scoped_machine, machine_action, machine_reply) transition"

definition fifo_observation :: "scheduler_state \<Rightarrow> packet list \<times> (nat \<Rightarrow> packet option) \<times> nat set" where
  "fifo_observation s = (ordinary_queue s, ordinary_receipts s, dedup_ids s)"

fun ordinary_commit_id :: "machine_reply \<Rightarrow> nat option" where
  "ordinary_commit_id (Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Ordinary q))))) = Some q"
| "ordinary_commit_id _ = None"

definition priority_commit :: "machine_reply \<Rightarrow> bool" where
  "priority_commit reply \<longleftrightarrow>
    (\<exists>q k. reply = Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Regulation q k)))))"

fun raw_ordinary_effect :: "scheduler_action \<Rightarrow> scheduler_result \<Rightarrow> nat option" where
  "raw_ordinary_effect Honest_Service (Internal (Served_Ordinary q)) = Some q"
| "raw_ordinary_effect _ _ = None"

lemma scoped_acceptance_uses_normal_admission:
  assumes "scoped_submit inputs s p = (Accepted q,t)"
  shows "scheduler_step s (Submit p) (Accepted q) t"
  using assms by (auto simp: scoped_submit_def scheduler_step_def split: prod.splits transition_result.splits if_splits)

lemma committed_service_is_internal:
  assumes "committed_service obs"
  obtains effect where "obs = Compared_Attempt (Service_Result (Internal effect))"
  using assms by (auto simp: committed_service_replies)

lemma scoped_ordinary_step_has_a_raw_fifo_witness:
  assumes step: "machine_step E d action reply t"
  obtains u v act out where
    "fifo_observation u = fifo_observation (scheduler_at d)"
    "fifo_observation v = fifo_observation (scheduler_at t)"
    "scheduler_step u act out v"
    "ordinary_commit_id reply = raw_ordinary_effect act out"
proof -
  let ?s = "scheduler_at d"
  let ?s' = "scheduler_at t"
  have stutter: "fifo_observation ?s' = fifo_observation ?s \<Longrightarrow>
    ordinary_commit_id reply = None \<Longrightarrow> thesis"
  proof -
    assume unchanged: "fifo_observation ?s' = fifo_observation ?s"
      and silent: "ordinary_commit_id reply = None"
    have frame: "scheduler_step ?s Unproductive_Turn (Operational_Failure No_Effective_Opportunity) ?s"
      by (simp add: scheduler_step_def)
    show thesis
      by (rule that[OF _ unchanged[symmetric] frame]) (simp_all add: silent)
  qed
  show thesis
  proof (cases action)
    case (Receive_Packet p)
    obtain r s where got: "scoped_submit (authority_facts E) ?s p = (r,s)"
      by (cases "scoped_submit (authority_facts E) ?s p") blast
    show thesis
    proof (cases r)
      case (Accepted q)
      from step Receive_Packet got Accepted obtain
        "reply = Admission (Accepted q)"
        "t = (write_scheduler d s)\<lparr>admitted_at := (admitted_at d)(q \<mapsto> p)\<rparr>"
        by (auto simp: machine_step_def)
      then have "reply = Admission (Accepted q)" "?s' = s" by simp_all
      moreover from scoped_acceptance_uses_normal_admission got Accepted
        have "scheduler_step ?s (Submit p) (Accepted q) s" by blast
      ultimately show thesis by (intro that[of ?s s "Submit p" "Accepted q"]) simp_all
    qed (use step Receive_Packet got in \<open>auto intro!: stutter simp: machine_step_def\<close>)
  next
    case (Attempt_At expected turn p)
    from step Attempt_At obtain obs where reply: "reply = Observed_Service obs"
      by (auto simp: machine_step_def split: prod.splits if_splits)
    show thesis
    proof (cases "committed_service obs")
      case False
      with step Attempt_At reply have "t = d" by (auto intro: service_attempt_without_a_commit_is_a_read)
      moreover from False reply have "ordinary_commit_id reply = None"
        by (cases reply rule: ordinary_commit_id.cases) auto
      ultimately show thesis by (intro stutter) simp_all
    next
      case True
      from committed_service_is_internal[OF this] obtain effect where
        obs: "obs = Compared_Attempt (Service_Result (Internal effect))" .
      from step Attempt_At reply have execution:
        "machine_step E d (Attempt_At expected turn p) (Observed_Service obs) t" by simp
      from service_trace_consumes_checked_compare(1)[OF execution True] obs have call:
        "observe_sequence (authority_facts E) (active_signer E) (order_at d) (retained_answer d)
            expected (committed_cut d) turn p = (Compared_Attempt (Service_Result (Internal effect)),?s')" by simp
      from compare_commit_uses_the_exact_current_order(4)[OF call] obtain u where
        run: "scheduler_step (authorized_view (authority_facts E) ?s) Honest_Service (Internal effect) u"
        and projection: "fifo_observation ?s' = fifo_observation u"
        by (elim scoped_commit_runs_the_approved_view) (simp add: fifo_observation_def)
      have outcome: "ordinary_commit_id reply = raw_ordinary_effect Honest_Service (Internal effect)"
        using obs reply by (cases effect) simp_all
      show thesis using run projection outcome
        by (intro that[of "authorized_view (authority_facts E) ?s" u Honest_Service "Internal effect"])
           (simp_all add: fifo_observation_def authorized_view_def)
    qed
  qed (use step in \<open>auto intro!: stutter simp: machine_step_def fifo_observation_def
       retire_stale_def Let_def split: prod.splits option.splits if_splits transition_result.splits rollback_internal.splits\<close>)
qed

lemma fifo_observation_preserves_lane_predicates:
  assumes "fifo_observation u = fifo_observation s"
  shows "coherent_ordinary_queue u = coherent_ordinary_queue s"
    "cohort_pending keys u = cohort_pending keys s" "cohort_done keys u = cohort_done keys s"
    "ordinary_queue u = ordinary_queue s" "ordinary_receipts u = ordinary_receipts s"
    "dedup_ids u = dedup_ids s" "earlier_ordinary q u = earlier_ordinary q s" "waiting q u = waiting q s"
  using assms unfolding fifo_observation_def coherent_ordinary_queue_def ordinary_ids_def ordinary_shape_def
    cohort_pending_def cohort_done_def earlier_ordinary_def waiting_def by simp_all

lemma scoped_fifo_maintains_coherence:
  assumes step: "machine_step E d action reply t" and inv: "coherent_ordinary_queue (scheduler_at d)"
  shows "coherent_ordinary_queue (scheduler_at t)"
proof -
  obtain u v act out where
    current: "fifo_observation u = fifo_observation (scheduler_at d)"
    and after: "fifo_observation v = fifo_observation (scheduler_at t)"
    and raw: "scheduler_step u act out v"
    by (rule scoped_ordinary_step_has_a_raw_fifo_witness[OF step]) (rule that; assumption)
  from fifo_observation_preserves_lane_predicates(1)[OF current] inv
  have "coherent_ordinary_queue u" by simp
  from scheduler_ordinarily_coherent[OF raw this] fifo_observation_preserves_lane_predicates(1)[OF after]
  show ?thesis by simp
qed

lemma scoped_fifo_preserves_the_tracked_cut:
  assumes step: "machine_step E d action reply t"
    and seen: "keys \<subseteq> dedup_ids (scheduler_at d)"
    and front: "tracked_prefix keys (ordinary_queue (scheduler_at d))"
  shows "keys \<subseteq> dedup_ids (scheduler_at t)"
    and "tracked_prefix keys (ordinary_queue (scheduler_at t))"
proof -
  obtain u v act out where
    current: "fifo_observation u = fifo_observation (scheduler_at d)"
    and after: "fifo_observation v = fifo_observation (scheduler_at t)"
    and raw: "scheduler_step u act out v"
    by (rule scoped_ordinary_step_has_a_raw_fifo_witness[OF step]) (rule that; assumption)
  from fifo_observation_preserves_lane_predicates(4,6)[OF current] seen front
  have "tracked_prefix keys (ordinary_queue u)" "keys \<subseteq> dedup_ids u" by simp_all
  from admitted_keys_persist[OF raw this(2)]
    prefix_preserved_across_scheduler[OF raw this(1,2)] fifo_observation_preserves_lane_predicates(4,6)[OF after]
  show "keys \<subseteq> dedup_ids (scheduler_at t)" "tracked_prefix keys (ordinary_queue (scheduler_at t))"
    by simp_all
qed

lemma raw_service_id:
  "raw_ordinary_effect act out = Some q \<longleftrightarrow> act = Honest_Service \<and> out = Internal (Served_Ordinary q)"
proof (cases act)
  case Honest_Service
  then show ?thesis
  proof (cases out)
    case (Internal eff)
    with Honest_Service show ?thesis by (cases eff) simp_all
  qed simp_all
qed simp_all

definition finished_in_scope :: "nat set \<Rightarrow> machine_event \<Rightarrow> nat set" where
  "finished_in_scope keys e = {q \<in> keys. ordinary_commit_id (step_outcome e) = Some q}"

lemma scoped_cut_accounts_for_the_actual_fifo:
  assumes step: "step_occurs (machine_step E) e"
    and inv: "coherent_ordinary_queue (scheduler_at (source_state e))"
    and seen: "keys \<subseteq> dedup_ids (scheduler_at (source_state e))"
  shows "accounts_for (\<lambda>d. cohort_pending keys (scheduler_at d)) (\<lambda>d. cohort_done keys (scheduler_at d))
      (\<lambda>_. {}) (finished_in_scope keys) e"
proof -
  from step have real: "machine_step E (source_state e) (step_action e) (step_outcome e) (target_state e)"
    by (simp add: step_occurs_def)
  obtain u v act out where
    current: "fifo_observation u = fifo_observation (scheduler_at (source_state e))"
    and after: "fifo_observation v = fifo_observation (scheduler_at (target_state e))"
    and raw: "scheduler_step u act out v"
    and outcome: "ordinary_commit_id (step_outcome e) = raw_ordinary_effect act out"
    by (rule scoped_ordinary_step_has_a_raw_fifo_witness[OF real]) (rule that; assumption)
  let ?projection = "\<lparr>source_state = u, step_action = act, step_outcome = out, target_state = v\<rparr>"
  from raw have occurs: "step_occurs scheduler_step ?projection" by (simp add: step_occurs_def)
  from inv seen fifo_observation_preserves_lane_predicates(1,6)[OF current]
  have consistent: "coherent_ordinary_queue (source_state ?projection)"
    "keys \<subseteq> dedup_ids (source_state ?projection)" by simp_all
  have finish: "cohort_finished keys ?projection = finished_in_scope keys e"
    using outcome by (simp add: cohort_finished_def finished_in_scope_def served_ordinary_def raw_service_id)
  from cut_accounts_for_scheduler_step[OF occurs consistent] finish
    fifo_observation_preserves_lane_predicates(2,3)[OF current]
    fifo_observation_preserves_lane_predicates(2,3)[OF after]
  show ?thesis by (simp add: accounts_for_def)
qed

lemma scoped_execution_writes_the_packet_that_was_served:
  assumes step: "machine_step E d action reply t"
    and out: "ordinary_commit_id reply = Some q"
  obtains p rest where "ordinary_queue (scheduler_at d) = p # rest"
    "packet_identity p = q" "ordinary_body (packet_contents p)"
    "ordinary_queue (scheduler_at t) = rest" "ordinary_receipts (scheduler_at t) q = Some p"
proof -
  obtain u v act outcome where
    current: "fifo_observation u = fifo_observation (scheduler_at d)"
    and after: "fifo_observation v = fifo_observation (scheduler_at t)"
    and raw: "scheduler_step u act outcome v"
    and id: "ordinary_commit_id reply = raw_ordinary_effect act outcome"
    by (rule scoped_ordinary_step_has_a_raw_fifo_witness[OF step]) (rule that; assumption)
  from id out have "raw_ordinary_effect act outcome = Some q" by simp
  from iffD1[OF raw_service_id this] raw have "scheduler_step u Honest_Service (Internal (Served_Ordinary q)) v"
    by simp
  then obtain p rest where
    "ordinary_queue u = p # rest" "packet_identity p = q" "ordinary_body (packet_contents p)"
    "ordinary_queue v = rest" "ordinary_receipts v q = Some p"
    by (elim ordinary_service_records_the_head_packet) auto
  with fifo_observation_preserves_lane_predicates(4,5)[OF current]
    fifo_observation_preserves_lane_predicates(4,5)[OF after]
  show thesis by (intro that[of p rest]) auto
qed

definition receives_fresh_choice :: "machine_evidence \<Rightarrow> service_turn list \<Rightarrow> machine_event \<Rightarrow> bool" where
  "receives_fresh_choice E offered e \<longleftrightarrow>
    (let d = source_state e in
     \<exists>turn p. choose_current_order (authority_facts E) (active_signer E) (order_at d) (scheduler_at d) offered = Some (turn,p)
       \<and> step_action e = Attempt_At (committed_cut d) turn p \<and> retained_answer d turn = None
       \<and> (turn,p) \<in> certified_order_pairs E \<and> \<not> conflicting_receipt d turn p)"

lemma fresh_offered_choice_causes_a_service:
  assumes run: "step_occurs (machine_step E) e"
    and available: "receives_fresh_choice E offered e"
    and shape: "ordinary_shape (scheduler_at (source_state e))"
    and waiting: "waiting q (scheduler_at (source_state e))"
  shows "ordinary_commit_id (step_outcome e) \<noteq> None \<or> priority_commit (step_outcome e)"
proof -
  let ?d = "source_state e"
  let ?s = "scheduler_at ?d"
  from available obtain turn p where
    chosen: "choose_current_order (authority_facts E) (active_signer E) (order_at ?d) ?s offered = Some (turn,p)"
    and at: "step_action e = Attempt_At (committed_cut ?d) turn p"
    and new: "retained_answer ?d turn = None"
    and signed: "(turn,p) \<in> certified_order_pairs E"
    and clear: "\<not> conflicting_receipt ?d turn p"
    by (auto simp: receives_fresh_choice_def Let_def)
  from chosen have plan: "planned (authorized_view (authority_facts E) ?s) = Some p"
    and order: "matches_plan_order (active_signer E) (order_at ?d) ?s p turn"
    by (auto simp: choose_current_order_def find_Some_iff split: option.splits)
  obtain s eff where committed:
    "scoped_service (authority_facts E) (active_signer E) (signed_packets_by_turn (order_at ?d)) ?s turn p = (Internal eff,s)"
    and actual: "(\<exists>i. eff = Served_Ordinary i) \<or> (\<exists>i k. eff = Served_Regulation i k)"
    by (rule a_chosen_current_order_produces_a_real_service[OF plan order shape waiting]) (rule that; assumption)
  from committed actual at new signed clear run have
    "step_outcome e = Observed_Service (Compared_Attempt (Service_Result (Internal eff)))"
    by (simp add: step_occurs_def machine_step_def observe_sequence_def try_service_at_def)
  with actual show ?thesis by (auto simp: priority_commit_def)
qed

lemma scoped_responsibility_survives:
  assumes step: "machine_step E d action reply t"
    and coherent: "coherent_ordinary_queue (scheduler_at d)"
    and known: "p \<in> set (ordinary_queue (scheduler_at d)) \<or>
       ordinary_receipts (scheduler_at d) (packet_identity p) = Some p"
  shows "p \<in> set (ordinary_queue (scheduler_at t)) \<or>
       ordinary_receipts (scheduler_at t) (packet_identity p) = Some p"
proof -
  obtain u v act out where
    current: "fifo_observation u = fifo_observation (scheduler_at d)"
    and after: "fifo_observation v = fifo_observation (scheduler_at t)"
    and raw: "scheduler_step u act out v"
    by (rule scoped_ordinary_step_has_a_raw_fifo_witness[OF step]) (rule that; assumption)
  from coherent known fifo_observation_preserves_lane_predicates(1,4,5)[OF current]
  have "coherent_ordinary_queue u"
    "p \<in> set (ordinary_queue u) \<or> ordinary_receipts u (packet_identity p) = Some p" by simp_all
  from responsibility_for_packet_preserved[OF raw this]
    fifo_observation_preserves_lane_predicates(4,5)[OF after] show ?thesis by simp
qed

lemma new_scoped_receipt_requires_an_actual_commit:
  assumes step: "machine_step E d action reply t"
    and absent: "ordinary_receipts (scheduler_at d) q \<noteq> Some p"
    and stored: "ordinary_receipts (scheduler_at t) q = Some p"
  shows "ordinary_commit_id reply = Some q"
proof -
  obtain u v act out where
    current: "fifo_observation u = fifo_observation (scheduler_at d)"
    and after: "fifo_observation v = fifo_observation (scheduler_at t)"
    and raw: "scheduler_step u act out v"
    and result: "ordinary_commit_id reply = raw_ordinary_effect act out"
    by (rule scoped_ordinary_step_has_a_raw_fifo_witness[OF step]) (rule that; assumption)
  from absent stored fifo_observation_preserves_lane_predicates(5)[OF current]
    fifo_observation_preserves_lane_predicates(5)[OF after]
  have old: "ordinary_receipts u q \<noteq> Some p" and new: "ordinary_receipts v q = Some p" by simp_all
  from raw show ?thesis
  proof (cases rule: ordinary_queue_update)
    case (pop served ps)
    from fun_cong[OF pop(5), of q] old new have "packet_identity served = q"
      by (cases "packet_identity served = q") simp_all
    with pop result show ?thesis by simp
  qed (use old new in simp_all)
qed

theorem an_exact_ordinary_packet_completes_in_the_scoped_run:
  assumes trace: "infinite_run (machine_step E) initial carrier events"
    and shaped: "coherent_ordinary_queue (scheduler_at (source_state (events 0)))"
    and pending: "p \<in> set (ordinary_queue (scheduler_at (source_state (events 0))))"
    and finite_priority: "finite {i. priority_commit (step_outcome (events i))}"
    and available: "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> ordinary_queue (scheduler_at (source_state (events j))) \<noteq> [])
      \<Longrightarrow> \<exists>j\<ge>i. receives_fresh_choice E (offered j) (events j)"
  shows "\<exists>j. ordinary_commit_id (step_outcome (events j)) = Some (packet_identity p)
      \<and> ordinary_receipts (scheduler_at (target_state (events j))) (packet_identity p) = Some p"
proof -
  let ?d = "\<lambda>i. source_state (events i)"
  let ?s = "\<lambda>i. scheduler_at (?d i)"
  let ?K = "ordinary_ids (?s 0)"
  let ?P = "\<lambda>d. cohort_pending ?K (scheduler_at d)"
  let ?C = "\<lambda>d. cohort_done ?K (scheduler_at d)"
  let ?F = "finished_in_scope ?K"
  let ?I = "\<lambda>e. priority_commit (step_outcome e)"
  let ?q = "packet_identity p"
  have linked: "\<And>i. target_state (events i) = ?d (Suc i)"
    and occurs: "\<And>i. step_occurs (machine_step E) (events i)"
    using trace by (simp_all add: infinite_run_def)
  then have step: "\<And>i. machine_step E (?d i) (step_action (events i)) (step_outcome (events i)) (?d (Suc i))"
    by (simp add: step_occurs_def)
  have inv: "coherent_ordinary_queue (?s i) \<and>
      ?K \<subseteq> dedup_ids (?s i) \<and> tracked_prefix ?K (ordinary_queue (?s i))" for i
  proof (induction i)
    case 0
    have "tracked_prefix ?K (ordinary_queue (?s 0))"
      unfolding tracked_prefix_def
      by (intro exI[of _ "ordinary_queue (?s 0)"] exI[of _ "[]"]) (simp add: ordinary_ids_def)
    with shaped show ?case by (auto simp: coherent_ordinary_queue_def)
  next
    case (Suc i)
    from Suc.IH scoped_fifo_maintains_coherence[OF step[of i]]
      scoped_fifo_preserves_the_tracked_cut[OF step[of i]]
    show ?case by blast
  qed
  have balance: "\<And>i. accounts_for ?P ?C (\<lambda>_. {}) ?F (events i)"
    by (rule scoped_cut_accounts_for_the_actual_fifo[OF occurs]) (use inv in auto)
  have postquiet: "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> ?I (events j)) \<Longrightarrow>
      ?P (?d i) \<noteq> {} \<Longrightarrow> \<exists>j\<ge>i. ?F (events j) \<noteq> {}"
  proof -
    fix i
    assume quiet: "\<And>j. i \<le> j \<Longrightarrow> \<not> ?I (events j)" and work: "?P (?d i) \<noteq> {}"
    show "\<exists>j\<ge>i. ?F (events j) \<noteq> {}"
    proof (rule ccontr)
      assume none: "\<not> (\<exists>j\<ge>i. ?F (events j) \<noteq> {})"
      have unchanged: "i \<le> j \<Longrightarrow> ?P (?d j) = ?P (?d i)" for j
      proof (induction j)
        case 0
        then show ?case by simp
      next
        case (Suc j)
        then show ?case
        proof (cases "i \<le> j")
          case True
          then have "?F (events j) = {}" using none by blast
          with balance[of j] linked[of j] Suc.IH[OF True] show ?thesis
            by (simp add: accounts_for_def)
        next
          case False
          with Suc.prems show ?thesis by (simp add: le_Suc_eq)
        qed
      qed
      have not_empty: "\<And>j. i \<le> j \<Longrightarrow> ordinary_queue (?s j) \<noteq> []"
      proof -
        fix j assume ij: "i \<le> j"
        from unchanged[OF ij] work have "?P (?d j) \<noteq> {}" by simp
        then show "ordinary_queue (?s j) \<noteq> []" by (auto simp: cohort_pending_def ordinary_ids_def)
      qed
      from available[OF not_empty] obtain j where ij: "i \<le> j"
        and choice: "receives_fresh_choice E (offered j) (events j)" by blast
      from inv[of j] unchanged[OF ij] work have front: "tracked_prefix ?K (ordinary_queue (?s j))"
        and left: "cohort_pending ?K (?s j) \<noteq> {}" and shape: "ordinary_shape (?s j)"
        by (auto simp: coherent_ordinary_queue_def)
      from tracked_head_exists[OF front left] obtain h rest where
        head: "ordinary_queue (?s j) = h # rest" and member: "packet_identity h \<in> ?K" .
      have waiting: "waiting (packet_identity h) (?s j)" by (simp add: waiting_def head)
      from fresh_offered_choice_causes_a_service[OF occurs[of j] choice shape waiting] quiet[OF ij]
      obtain q where effect: "ordinary_commit_id (step_outcome (events j)) = Some q" by fastforce
      obtain served rest' where first: "ordinary_queue (?s j) = served # rest'"
        and ident: "packet_identity served = q"
        by (rule scoped_execution_writes_the_packet_that_was_served[OF step[of j] effect]) (rule that; assumption)
      from first head ident member have "q \<in> ?K" by simp
      with effect ij none show False by (auto simp: finished_in_scope_def)
    qed
  qed
  from eventual_completion_under_finite_interference[OF trace balance _ finite_priority postquiet]
  obtain n where complete: "\<And>i. n \<le> i \<Longrightarrow>
    ?P (?d i) = {} \<and> (\<forall>j\<le>i. ?P (?d j) \<union> ?C (?d j) \<subseteq> ?C (?d i))"
    by auto
  have both: "p \<in> set (ordinary_queue (?s i)) \<or> ordinary_receipts (?s i) ?q = Some p" for i
  proof (induction i)
    case 0
    with pending show ?case by simp
  next
    case (Suc i)
    from inv[of i] have "coherent_ordinary_queue (?s i)" by simp
    then show ?case by (rule scoped_responsibility_survives[OF step[of i] _ Suc.IH])
  qed
  from pending have "?q \<in> ?P (?d 0)" by (auto simp: cohort_pending_def ordinary_ids_def)
  with complete[of n] both[of n] have received: "ordinary_receipts (?s n) ?q = Some p"
    by (auto simp: cohort_pending_def ordinary_ids_def)
  have blank: "ordinary_receipts (?s 0) ?q \<noteq> Some p"
    using pending shaped by (auto simp: coherent_ordinary_queue_def ordinary_ids_def dom_def)
  have witness: "ordinary_receipts (?s i) ?q = Some p \<Longrightarrow>
    \<exists>j<i. ordinary_commit_id (step_outcome (events j)) = Some ?q \<and>
      ordinary_receipts (scheduler_at (target_state (events j))) ?q = Some p" for i
  proof (induction i)
    case 0
    with blank show ?case by simp
  next
    case (Suc i)
    show ?case
    proof (cases "ordinary_receipts (?s i) ?q = Some p")
      case True
      from Suc.IH[OF True] obtain j where "j < i"
        "ordinary_commit_id (step_outcome (events j)) = Some ?q"
        "ordinary_receipts (scheduler_at (target_state (events j))) ?q = Some p" by blast
      then show ?thesis by (intro exI[of _ j]) simp
    next
      case False
      from new_scoped_receipt_requires_an_actual_commit[OF step[of i] False Suc.prems]
        linked[of i] Suc.prems show ?thesis by (intro exI[of _ i]) simp
    qed
  qed
  from witness[OF received] show ?thesis by blast
qed

end
