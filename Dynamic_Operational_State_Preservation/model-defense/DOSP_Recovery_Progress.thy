theory DOSP_Recovery_Progress
  imports DOSP_Source_Defense
begin

context integrated_dosp_authority
begin

lemma offered_recovery_uses_a_native_step_or_refuses_without_effect:
  assumes "offered_recovery_step sources head offers grants governance s action reply t"
  shows "recovery_step grants governance s action reply t \<or>
    (replica_repair action \<and> reply = transition_result.Operational_Failure Evidence_Unavailable \<and> t = s)"
  using assms by (auto simp: offered_recovery_step_def receipt_repair_step_def
    split: if_splits option.splits prod.splits)

definition accounting_event :: "nat repair_event \<Rightarrow> nat repair_event" where
  "accounting_event e =
    (if replica_repair (step_action e) \<and> step_outcome e = transition_result.Operational_Failure Evidence_Unavailable
       \<and> source_state e = target_state e
     then e\<lparr>step_action := Wait_For_Source, step_outcome := transition_result.Internal ()\<rparr> else e)"

lemma accounting_keeps_states_and_work_changes [simp]:
  "source_state (accounting_event e) = source_state e"
  "target_state (accounting_event e) = target_state e"
  "affects_recovery (accounting_event e) = affects_recovery e"
  "finished_result (step_outcome (accounting_event e)) = finished_result (step_outcome e)"
  "admitted_result (step_outcome (accounting_event e)) = admitted_result (step_outcome e)"
  by (auto simp: accounting_event_def affects_recovery_def split: if_splits)

lemma offered_events_project_to_native_work_accounting:
  assumes occurrence: "step_occurs (offered_recovery_step sources head offers grants governance) e"
  shows "step_occurs (recovery_step grants governance) (accounting_event e)"
proof -
  have native_or_refused:
    "recovery_step grants governance (source_state e) (step_action e) (step_outcome e) (target_state e)
      \<or> (replica_repair (step_action e) \<and>
        step_outcome e = transition_result.Operational_Failure Evidence_Unavailable \<and>
        target_state e = source_state e)"
    using occurrence[unfolded step_occurs_def] by (rule offered_recovery_uses_a_native_step_or_refuses_without_effect)
  show ?thesis
  proof (cases "replica_repair (step_action e) \<and>
      step_outcome e = transition_result.Operational_Failure Evidence_Unavailable \<and> source_state e = target_state e")
    case True
    then show ?thesis
      by (simp add: accounting_event_def step_occurs_def recovery_step.Idle)
  next
    case False
    then show ?thesis using native_or_refused by (auto simp: accounting_event_def step_occurs_def)
  qed
qed

definition authenticated_recovery_run where
  "authenticated_recovery_run sources heads offers grants governance initial events \<longleftrightarrow>
    source_state (events 0) \<in> initial \<and>
    (\<forall>i. source_state (events i) \<in> recovery_carrier \<and>
      step_occurs (offered_recovery_step (sources i) (heads i) (offers i) grants governance) (events i) \<and>
      target_state (events i) = source_state (events (Suc i)))"

definition recovery_interference where
  "recovery_interference heads events i \<longleftrightarrow>
    affects_recovery (events i) \<or> heads (Suc i) \<noteq> heads i"

definition authorized_repair_is_ready where
  "authorized_repair_is_ready sources head offers governance s action \<longleftrightarrow>
    (case action of
       Apply_Repair job seq \<Rightarrow> (\<exists>d. verified_job_ready sources head offers s job d seq)
     | Governance_Resync approval job seq \<Rightarrow>
         approval \<in> governance \<and> rollback_incomplete s \<and> source_ready s \<and> seq = primary_sequence s \<and>
         (\<exists>d. work_owner s job = Some d \<and> d \<in> active_domains s) \<and>
         (\<exists>authority receipt. select_current_publication sources head offers (route_epoch s) = Some (authority,receipt) \<and>
           primary_receipt_matches authority receipt s)
     | _ \<Rightarrow> False)"

lemma a_scheduled_authorized_repair_completes_a_job:
  assumes ready: "authorized_repair_is_ready sources head offers governance s action"
    and step: "offered_recovery_step sources head offers grants governance s action reply t"
  shows "\<exists>job d seq. reply = transition_result.Accepted (Installed job d seq)"
proof (cases action)
  case (Apply_Repair job seq)
  then obtain d where "verified_job_ready sources head offers s job d seq"
    using ready by (auto simp: authorized_repair_is_ready_def)
  from a_ready_chosen_installation_actually_finishes_its_job[OF this step[unfolded Apply_Repair]]
  show ?thesis by blast
next
  case (Governance_Resync approval job seq)
  then obtain authority receipt where selected: "select_current_publication sources head offers (route_epoch s) = Some (authority, receipt)"
    and matches: "primary_receipt_matches authority receipt s"
    using ready by (auto simp: authorized_repair_is_ready_def)
  have native: "recovery_step grants governance s (Governance_Resync approval job seq) reply t"
    using step selected matches by (simp add: Governance_Resync offered_recovery_step_def receipt_repair_step_def)
  from native show ?thesis by (cases rule: recovery_step.cases) auto
qed (use ready in \<open>simp_all add: authorized_repair_is_ready_def\<close>)

theorem authenticated_recovery_finishes_under_finite_interference:
  assumes run: "authenticated_recovery_run sources heads offers grants governance initial events"
    and finite: "finite {i. recovery_interference heads events i}"
    and scheduled:
      "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> recovery_interference heads events j) \<Longrightarrow>
       pending_ids (source_state (events i)) \<noteq> {} \<Longrightarrow>
       \<exists>j\<ge>i. authorized_repair_is_ready (sources j) (heads j) (offers j) governance
         (source_state (events j)) (step_action (events j))"
  shows "\<exists>n. \<forall>i\<ge>n.
    pending_ids (source_state (events i)) = {} \<and>
    (\<forall>d\<in>active_domains (source_state (events i)).
      replica (source_state (events i)) d = primary_record (source_state (events i))) \<and>
    (\<forall>j\<le>i. pending_ids (source_state (events j)) \<union> completion_log (source_state (events j))
      \<subseteq> completion_log (source_state (events i)))"
proof -
  have accounting_run:
    "infinite_run (recovery_step grants governance) initial recovery_carrier (accounting_event \<circ> events)"
    using run by (auto simp: infinite_run_def authenticated_recovery_run_def
      intro: offered_events_project_to_native_work_accounting)
  have affects_subset: "{i. affects_recovery (events i)} \<subseteq> {i. recovery_interference heads events i}"
    by (auto simp: recovery_interference_def)
  have finite_work: "finite {i. affects_recovery (events i)}"
    by (rule finite_subset[OF affects_subset finite])
  have all_quiet:
    "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> affects_recovery (events j)) \<Longrightarrow>
     pending_ids (source_state (events i)) \<noteq> {} \<Longrightarrow>
     \<exists>j\<ge>i. \<exists>job d seq. step_outcome (accounting_event (events j)) = transition_result.Accepted (Installed job d seq)"
  proof -
    fix i
    assume quiet: "\<And>j. i \<le> j \<Longrightarrow> \<not> affects_recovery (events j)"
    assume pending: "pending_ids (source_state (events i)) \<noteq> {}"
    obtain cutoff where cutoff: "\<And>j. cutoff \<le> j \<Longrightarrow> \<not> recovery_interference heads events j"
    proof -
      let ?S = "{i. recovery_interference heads events i}"
      obtain b where "\<And>j. j \<in> ?S \<Longrightarrow> j \<le> b"
        using finite by (metis finite_nat_set_iff_bounded_le)
      then have "\<And>j. Suc b \<le> j \<Longrightarrow> \<not> recovery_interference heads events j" by force
      then show thesis by (rule that)
    qed
    let ?limit = "max i cutoff"
    show "\<exists>j\<ge>i. \<exists>job d seq. step_outcome (accounting_event (events j)) = transition_result.Accepted (Installed job d seq)"
    proof (cases "\<exists>j\<ge>i. \<exists>job d seq. step_outcome (events j) = transition_result.Accepted (Installed job d seq)")
      case True
      then obtain j job d seq where later: "i \<le> j"
        and installed: "step_outcome (events j) = transition_result.Accepted (Installed job d seq)" by blast
      have "step_outcome (accounting_event (events j)) = transition_result.Accepted (Installed job d seq)"
        using installed by (simp add: accounting_event_def)
      then show ?thesis using later by (intro exI[of _ j] conjI exI[of _ job] exI[of _ d] exI[of _ seq]) assumption+
    next
      case False
      have persisted: "pending_ids (source_state (events k)) = pending_ids (source_state (events i))"
        if "i \<le> k" for k
      using that
      proof (induction k rule: dec_induct)
        case base
        then show ?case by simp
      next
        case (step k)
        have occurs: "step_occurs (recovery_step grants governance) (accounting_event (events k))"
          and carrier: "source_state (accounting_event (events k)) \<in> recovery_carrier"
          and adjacent: "target_state (accounting_event (events k)) = source_state (events (Suc k))"
          using accounting_run by (auto simp: infinite_run_def)
        have no_entrance: "admitted_result (step_outcome (accounting_event (events k))) = {}"
          using quiet[OF step.hyps(1)] by (auto simp: affects_recovery_def)
        have not_installed: "\<And>job d seq. step_outcome (events k) \<noteq> transition_result.Accepted (Installed job d seq)"
          using False step.hyps(1) by blast
        have no_completion: "finished_result (step_outcome (accounting_event (events k))) = {}"
          unfolding accounting_keeps_states_and_work_changes(4)
        proof (cases "step_outcome (events k)")
          case (Accepted result)
          then show "finished_result (step_outcome (events k)) = {}"
            using not_installed by (cases result) auto
        qed simp_all
        note booked = recovery_work_accounting[OF occurs carrier]
        show ?case using booked no_entrance no_completion step.IH adjacent
          by (simp add: accounts_for_def)
      qed
      have quiet_tail: "\<And>j. ?limit \<le> j \<Longrightarrow> \<not> recovery_interference heads events j"
        using cutoff by simp
      have pending_tail: "pending_ids (source_state (events ?limit)) \<noteq> {}"
        using pending persisted[of ?limit] by simp
      obtain j where j: "?limit \<le> j"
        and ready: "authorized_repair_is_ready (sources j) (heads j) (offers j) governance
          (source_state (events j)) (step_action (events j))"
        using scheduled[OF quiet_tail pending_tail] by blast
      have observed: "step_occurs (offered_recovery_step (sources j) (heads j) (offers j) grants governance) (events j)"
        using run by (simp add: authenticated_recovery_run_def)
      have occurs:
        "offered_recovery_step (sources j) (heads j) (offers j) grants governance
          (source_state (events j)) (step_action (events j)) (step_outcome (events j)) (target_state (events j))"
        using observed by (simp only: step_occurs_def)
      obtain job d seq where installed: "step_outcome (events j) = transition_result.Accepted (Installed job d seq)"
        using a_scheduled_authorized_repair_completes_a_job[OF ready occurs] by blast
      then have "step_outcome (accounting_event (events j)) = transition_result.Accepted (Installed job d seq)"
        by (simp add: accounting_event_def)
      then show ?thesis using j by (intro exI[of _ j] conjI exI[of _ job] exI[of _ d] exI[of _ seq]) auto
    qed
  qed
  have past_cutoff:
    "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> affects_recovery ((accounting_event \<circ> events) j)) \<Longrightarrow>
      pending_ids (source_state ((accounting_event \<circ> events) i)) \<noteq> {} \<Longrightarrow>
      \<exists>j\<ge>i. \<exists>job d seq. step_outcome ((accounting_event \<circ> events) j) = transition_result.Accepted (Installed job d seq)"
    using all_quiet by simp
  show ?thesis using recovery_finishes_under_finite_interference[OF accounting_run _ past_cutoff]
    finite_work by simp
qed

end

end
