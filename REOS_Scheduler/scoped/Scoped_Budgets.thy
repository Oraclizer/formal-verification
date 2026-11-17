theory Scoped_Budgets
  imports Scoped_Counting
begin

definition case_credit :: "scheduler_state \<Rightarrow> nat \<Rightarrow> nat" where
  "case_credit s k = (severity_limit s k - severity_now s k) + case_remaining (rollback_context s) k"

definition case_credits :: "nat set \<Rightarrow> scoped_machine \<Rightarrow> nat" where
  "case_credits K d = (\<Sum>k\<in>K. case_credit (scheduler_at d) k)"

definition budgeted_priority :: "nat set \<Rightarrow> machine_event \<Rightarrow> bool" where
  "budgeted_priority K e \<longleftrightarrow>
    (used_priority_slot e \<longrightarrow>
      (\<exists>expected turn p. step_action e = Attempt_At expected turn p \<and>
       regulatory_case (packet_contents p) \<in> K \<and>
       ((\<exists>k level. packet_contents p = Raise_Level k level) \<or>
        (\<exists>r a pf. packet_contents p = Execute_Governed_Rollback r a pf))))"

lemma a_verified_import_does_not_refill_rollback_credit:
  "case_remaining (snd (import_verified s expected current evidence)) = case_remaining s"
  by (cases evidence) (auto simp: commit_internal_def Let_def
      split: prod.splits transition_result.splits option.splits if_splits)

lemma a_nonpriority_step_preserves_case_credit:
  assumes step: "machine_step E d action reply t" and quiet: "\<not> priority_commit reply"
  shows "case_credit (scheduler_at t) k = case_credit (scheduler_at d) k"
  using step quiet
proof (cases action)
  case (Attempt_At expected turn p)
  from step Attempt_At obtain obs where reply: "reply = Observed_Service obs"
    by (auto simp: machine_step_def split: prod.splits if_splits)
  from step Attempt_At reply have actual:
    "machine_step E d (Attempt_At expected turn p) (Observed_Service obs) t" by simp
  show ?thesis
  proof (cases "committed_service obs")
    case False
    with service_attempt_without_a_commit_is_a_read[OF actual] show ?thesis by simp
  next
    case True
    with quiet reply obtain q where obs:
      "obs = Compared_Attempt (Service_Result (Internal (Served_Ordinary q)))"
      by (auto simp: priority_commit_def committed_service_replies)
    from service_trace_consumes_checked_compare(1)[OF actual True] obs have called:
      "observe_sequence (authority_facts E) (active_signer E) (order_at d) (retained_answer d)
       expected (committed_cut d) turn p =
        (Compared_Attempt (Service_Result (Internal (Served_Ordinary q))),scheduler_at t)"
      by simp
    from scoped_ordinary_effect[OF compare_commit_uses_the_exact_current_order(4)[OF called]] obtain rest where
      "scheduler_at t = (scheduler_at d)\<lparr>ordinary_queue := rest,
        ordinary_receipts := (ordinary_receipts (scheduler_at d))(q \<mapsto> p)\<rparr>" by blast
    then show ?thesis by (simp add: case_credit_def)
  qed
next
  case (Receive_Packet p)
  with step show ?thesis
    by (auto simp: machine_step_def case_credit_def scoped_submit_def admit_def enqueue_packet_def Let_def
        split: prod.splits transition_result.splits if_splits)
next
  case (Import_At expected binding)
  let ?s = "rollback_context (scheduler_at d)"
  let ?cut = "store_cut (committed_cut d)"
  obtain current certified where evidence: "source_at_cut E ?cut binding = (current,certified)"
    by (cases "source_at_cut E ?cut binding") blast
  obtain answer r where result: "import_verified ?s binding current certified = (answer,r)"
    by (cases "import_verified ?s binding current certified") blast
  from a_verified_import_does_not_refill_rollback_credit[of ?s binding current certified] result
  have remaining: "case_remaining r = case_remaining ?s" by simp
  from step Import_At evidence result remaining show ?thesis
    by (cases answer) (auto simp: machine_step_def case_credit_def split: if_splits)
qed (auto simp: machine_step_def case_credit_def checked_advance_def retire_stale_def Let_def
      split: prod.splits option.splits transition_result.splits if_splits rollback_internal.splits)

lemma raises_spend_at_least_one_case_credit:
  assumes service: "scoped_service I signer verified s turn p = (Internal (Served_Regulation q k),t)"
    and body: "packet_contents p = Raise_Level k level"
  shows "case_credit t k + 1 \<le> case_credit s k"
    and "\<And>j. j \<noteq> k \<Longrightarrow> case_credit t j = case_credit s j"
proof -
  let ?v = "authorized_view I s"
  from scoped_regulatory_effect[OF service] obtain u where effect:
    "regulatory_effect ?v p = Some u"
    and result: "t = u\<lparr>regulatory_queue := remove1 p (regulatory_queue s),
        regulation_receipts := (regulation_receipts ?v)(q \<mapsto> p)\<rparr>" by blast
  from effect body have level: "severity_now s k < level" "level \<le> severity_limit s k"
    and u: "u = ?v\<lparr>severity_now := (severity_now s)(k := level)\<rparr>"
    by (auto simp: regulatory_effect_def authorized_view_def split: if_splits)
  from result u have updated: "severity_now t = (severity_now s)(k := level)"
    "severity_limit t = severity_limit s" "rollback_context t = rollback_context s"
    by (simp_all add: authorized_view_def)
  show "case_credit t k + 1 \<le> case_credit s k"
    using level updated by (simp add: case_credit_def)
  fix j assume "j \<noteq> k"
  then show "case_credit t j = case_credit s j" using updated by (simp add: case_credit_def)
qed

lemma a_governed_rollback_spends_exactly_one_case_credit:
  assumes obs: "observe_sequence I signer orders retained expected current turn p =
       (Compared_Attempt (Service_Result (Internal (Served_Regulation q k))),t)"
    and body: "packet_contents p = Execute_Governed_Rollback r a pf"
  shows "case_credit t k + 1 = case_credit (observed_scheduler current) k"
    and "\<And>j. j \<noteq> k \<Longrightarrow> case_credit t j = case_credit (observed_scheduler current) j"
proof -
  let ?s = "observed_scheduler current"
  let ?v = "authorized_view I ?s"
  note service = compare_commit_uses_the_exact_current_order(4)[OF obs]
  from scoped_regulatory_effect[OF service] obtain u where
    effort: "regulatory_effect ?v p = Some u"
    and result: "t = u\<lparr>regulatory_queue := remove1 p (regulatory_queue ?s),
        regulation_receipts := (regulation_receipts ?v)(q \<mapsto> p)\<rparr>" by blast
  from effort result body have levels: "severity_now t = severity_now ?s \<and> severity_limit t = severity_limit ?s"
    by (auto simp: regulatory_effect_def authorized_view_def split: prod.splits transition_result.splits if_splits)
  from committed_rollback_consumes_authority_frame_and_budget(5)[OF obs body] levels
  show "case_credit t k + 1 = case_credit ?s k" by (simp add: case_credit_def add.assoc)
  fix j assume j: "j \<noteq> k"
  from a_scoped_governed_commit_uses_the_same_checked_rollback(3,5)[OF service body] obtain
    key: "k = request_case r" and step:
      "rollback_step (rollback_context ?s) (Execute_Rollback r a pf) (Accepted q) (rollback_context t)" by blast
  from successful_rollback_spends_unit(2)[OF step, of j] j key levels
  show "case_credit t j = case_credit ?s j" by (simp add: case_credit_def)
qed

lemma one_budgeted_priority_slot_spends_a_registered_case_credit:
  assumes event: "step_occurs (machine_step E) e" and covered: "budgeted_priority K e"
    and used: "used_priority_slot e"
  obtains k where "k \<in> K"
    "case_credit (scheduler_at (target_state e)) k + 1 \<le> case_credit (scheduler_at (source_state e)) k"
    "\<And>j. j \<noteq> k \<Longrightarrow>
      case_credit (scheduler_at (target_state e)) j = case_credit (scheduler_at (source_state e)) j"
proof -
  let ?d = "source_state e"
  let ?s = "scheduler_at ?d"
  let ?t = "target_state e"
  from covered used obtain expected turn p where
    act: "step_action e = Attempt_At expected turn p"
    and member: "regulatory_case (packet_contents p) \<in> K"
    and cases: "(\<exists>k level. packet_contents p = Raise_Level k level) \<or>
        (\<exists>r a pf. packet_contents p = Execute_Governed_Rollback r a pf)"
    by (auto simp: budgeted_priority_def)
  from used obtain q k where
    out: "step_outcome e = Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Regulation q k))))"
    by (auto simp: used_priority_slot_def priority_commit_def)
  from event act out have step:
    "machine_step E ?d (Attempt_At expected turn p)
     (Observed_Service (Compared_Attempt (Service_Result (Internal (Served_Regulation q k))))) ?t"
    by (simp add: step_occurs_def)
  from service_trace_consumes_checked_compare(1)[OF step] have obs:
    "observe_sequence (authority_facts E) (active_signer E) (order_at ?d) (retained_answer ?d)
     expected (committed_cut ?d) turn p =
      (Compared_Attempt (Service_Result (Internal (Served_Regulation q k))),scheduler_at ?t)"
    by simp
  note service = compare_commit_uses_the_exact_current_order(4)[OF obs]
  from scoped_regulatory_effect[OF service] obtain u where key: "k = regulatory_case (packet_contents p)" by blast
  from member key have authenticated_case: "k \<in> K" by simp
  from cases show thesis
  proof
    assume "\<exists>k' level. packet_contents p = Raise_Level k' level"
    with key obtain level where body: "packet_contents p = Raise_Level k level" by auto
    from raises_spend_at_least_one_case_credit[OF service body]
      show thesis by (rule that[OF authenticated_case])
  next
    assume "\<exists>r a pf. packet_contents p = Execute_Governed_Rollback r a pf"
    then obtain r a pf where body: "packet_contents p = Execute_Governed_Rollback r a pf" by blast
    from a_governed_rollback_spends_exactly_one_case_credit[OF obs body]
      show thesis by (intro that[OF authenticated_case]) simp_all
  qed
qed

lemma budgeted_step_spends_at_most_available_credits:
  assumes finite: "finite K" and occurs: "step_occurs (machine_step E) e"
    and budgeted: "budgeted_priority K e"
  shows "case_credits K (target_state e) + (if used_priority_slot e then 1 else 0)
    \<le> case_credits K (source_state e)"
proof (cases "used_priority_slot e")
  case False
  with a_nonpriority_step_preserves_case_credit occurs have pointwise:
    "case_credit (scheduler_at (target_state e)) k = case_credit (scheduler_at (source_state e)) k" for k
    by (auto simp: used_priority_slot_def step_occurs_def)
  with False show ?thesis by (simp add: case_credits_def)
next
  case True
  from one_budgeted_priority_slot_spends_a_registered_case_credit[OF occurs budgeted True]
  obtain k where k: "k \<in> K"
    and used: "case_credit (scheduler_at (target_state e)) k + 1 \<le> case_credit (scheduler_at (source_state e)) k"
    and rest: "\<And>j. j \<noteq> k \<Longrightarrow> case_credit (scheduler_at (target_state e)) j = case_credit (scheduler_at (source_state e)) j"
    by metis
  from rest have eq: "(\<Sum>j\<in>K - {k}. case_credit (scheduler_at (target_state e)) j) =
       (\<Sum>j\<in>K - {k}. case_credit (scheduler_at (source_state e)) j)" by (intro sum.cong) auto
  from True used eq show ?thesis
    by (subst (1 2) case_credits_def, subst (1 2) sum.remove[OF finite k]) simp
qed

theorem fixed_case_capacity_bounds_scoped_raises_and_rollbacks:
  assumes finite: "finite K" and prefix: "finite_trace (machine_step E) carrier d events t"
    and closed: "\<And>e. e \<in> set events \<Longrightarrow> budgeted_priority K e"
  shows "case_credits K t + length (filter used_priority_slot events) \<le> case_credits K d"
  using prefix closed
proof (induction events arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  from Cons.prems have source: "source_state e = d" and happened: "step_occurs (machine_step E) e"
    and tail: "finite_trace (machine_step E) carrier (target_state e) es t" by simp_all
  from Cons.prems have budget: "budgeted_priority K e" by simp
  from budgeted_step_spends_at_most_available_credits[OF finite happened budget] source have expense:
    "case_credits K (target_state e) + (if used_priority_slot e then 1 else 0) \<le> case_credits K d" by simp
  have suffix:
    "case_credits K t + length (filter used_priority_slot es) \<le> case_credits K (target_state e)"
    by (rule Cons.IH[OF tail]) (use Cons.prems(2) in simp)
  from expense suffix show ?case by (cases "used_priority_slot e") auto
qed

corollary registered_case_budget_is_consumed_by_exact_request_progress:
  assumes finite: "finite K" and trace: "finite_trace (machine_step E) carrier d events t"
    and covered: "\<And>e. e \<in> set events \<Longrightarrow> budgeted_priority K e"
    and coherent: "coherent_ordinary_queue (scheduler_at d)"
    and pending: "p \<in> set (ordinary_queue (scheduler_at d))"
    and slots: "earlier_ordinary (packet_identity p) (scheduler_at d) + case_credits K d <
      length (filter used_service_slot events)"
  shows "\<exists>e \<in> set events. ordinary_commit_id (step_outcome e) = Some (packet_identity p)
    \<and> ordinary_receipts (scheduler_at (target_state e)) (packet_identity p) = Some p"
proof -
  from fixed_case_capacity_bounds_scoped_raises_and_rollbacks[OF finite trace covered]
  have "length (filter used_priority_slot events) \<le> case_credits K d" by simp
  from scoped_request_is_served_by_its_fifo_rank_plus_actual_interference[OF trace coherent pending this slots]
  show ?thesis .
qed

end
