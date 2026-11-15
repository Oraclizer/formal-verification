theory Rollback_Contracts
  imports Rollback_Model
begin

section \<open>Authorization and selective effects\<close>

lemma accepted_rollback:
  assumes "rollback_step s (Execute_Rollback r approval role_proof) (Accepted i) t"
  obtains h where
    "i = request_id r"
    "authorization_failure s r approval role_proof = None"
    "journal s (undo_entry r) = Some h"
    "restoration_failure s r h = None"
    "t = restore s r h"
  using assms by (auto simp: rollback_step_def execute_rollback_def split: option.splits)

theorem rollback_authority_contract:
  assumes step: "rollback_step s (Execute_Rollback r approval role_proof) (Accepted i) t"
  obtains g p h where
    "grant_at s (authority_epoch s) (requester r) = Some g"
    "rules_at s (request_case r) (policy_epoch s (request_case r)) = Some p"
    "journal s (undo_entry r) = Some h"
    "r \<in> authenticated_intents s"
    "grant_role g = requested_role r"
    "request_case r \<in> grant_cases g"
    "request_case r = entry_case h"
    "request_authority_epoch r = authority_epoch s"
    "request_policy_epoch r = policy_epoch s (request_case r)"
    "request_window r = case_window p"
    "fst (case_window p) \<le> consensus_time s"
    "consensus_time s < snd (case_window p)"
    "footprint r \<noteq> {}"
    "\<forall>c \<in> footprint r. inside_scope (request_scope r) c"
    "footprint r \<subseteq> grant_cells g \<inter> policy_cells p (requested_role r) \<inter> entry_cells h"
    "request_scope r = Wide \<longrightarrow> requested_role r \<in> wide_roles p \<and>
      matches_certificate s r Governance_Ratification Governance approval"
    "role_proof_ok s r (requested_role r) role_proof"
proof -
  from accepted_rollback[OF step] obtain h where auth:
    "authorization_failure s r approval role_proof = None" and
    journal: "journal s (undo_entry r) = Some h" and
    restoration: "restoration_failure s r h = None" by blast
  from auth obtain g p where
    "grant_at s (authority_epoch s) (requester r) = Some g"
    "rules_at s (request_case r) (policy_epoch s (request_case r)) = Some p"
    "r \<in> authenticated_intents s"
    "grant_role g = requested_role r"
    "request_case r \<in> grant_cases g"
    "request_authority_epoch r = authority_epoch s"
    "request_policy_epoch r = policy_epoch s (request_case r)"
    "request_window r = case_window p"
    "fst (case_window p) \<le> consensus_time s"
    "consensus_time s < snd (case_window p)"
    "footprint r \<noteq> {}"
    "\<forall>c \<in> footprint r. inside_scope (request_scope r) c"
    "footprint r \<subseteq> grant_cells g \<inter> policy_cells p (requested_role r)"
    "request_scope r = Wide \<longrightarrow> requested_role r \<in> wide_roles p \<and>
      matches_certificate s r Governance_Ratification Governance approval"
    "role_proof_ok s r (requested_role r) role_proof"
    unfolding authorization_failure_def
    by (auto split: option.splits if_splits)
  moreover from restoration have
    "request_case r = entry_case h" "footprint r \<subseteq> entry_cells h"
    by (auto simp: restoration_failure_def split: if_splits)
  ultimately show thesis using journal that by blast
qed

theorem broad_rollback_requires_ratification:
  assumes "request_scope r = Wide"
    and "\<not> matches_certificate s r Governance_Ratification Governance approval"
  shows "\<not> rollback_step s (Execute_Rollback r approval role_proof) (Accepted i) t"
  using assms rollback_authority_contract by blast

corollary no_unilateral_regulatory_wide_rollback:
  assumes "request_scope r = Wide" "requested_role r = Regulator"
  shows "\<not> rollback_step s (Execute_Rollback r None role_proof) (Accepted i) t"
  using assms(1) by (rule broad_rollback_requires_ratification)
     (simp add: matches_certificate_def)

theorem stale_authority_rejected:
  assumes "request_authority_epoch r \<noteq> authority_epoch s"
  shows "rollback_step s (Execute_Rollback r approval role_proof) (Rejected Stale_Authority) s"
  using assms by (simp add: rollback_step_def execute_rollback_def authorization_failure_def)

theorem unauthenticated_intent_rejected:
  assumes "request_authority_epoch r = authority_epoch s"
    and "request_policy_epoch r = policy_epoch s (request_case r)"
    and "r \<notin> authenticated_intents s"
  shows "rollback_step s (Execute_Rollback r approval role_proof) (Rejected Unauthenticated_Intent) s"
  using assms by (simp add: rollback_step_def execute_rollback_def authorization_failure_def)

theorem rejected_transition_unchanged:
  assumes "rollback_step s action (Rejected why) t"
  shows "t = s"
  using assms by (cases action)
    (auto simp: rollback_step_def execute_rollback_def split: option.splits if_splits)

theorem selective_restoration:
  assumes step: "rollback_step s (Execute_Rollback r approval role_proof) (Accepted i) t"
  obtains h where
    "journal s (undo_entry r) = Some h"
    "\<forall>c \<in> footprint r. cell_value t c = previous_value h c"
    "preserves_outside cell_value (footprint r) s t"
    "replica_value t = replica_value s"
    "authenticated_intents t = authenticated_intents s"
    "grant_at t = grant_at s"
    "rules_at t = rules_at s"
    "policy_epoch t = policy_epoch s"
    "authority_epoch t = authority_epoch s"
    "verified_certificates t = verified_certificates s"
    "terminal_records t = terminal_records s"
    "\<forall>j. j \<noteq> request_id r \<longrightarrow> journal t j = journal s j"
proof -
  from accepted_rollback[OF step] obtain h where
    h: "journal s (undo_entry r) = Some h" and t: "t = restore s r h" by blast
  have frame: "preserves_outside cell_value (footprint r) s t"
    using update_cells_frame[of "footprint r" "cell_value s" "previous_value h"]
    by (simp add: t restore_def preserves_outside_def)
  show ?thesis
    by (rule that[OF h _ frame]) (auto simp: t restore_def update_cells_def)
qed

section \<open>Irreversible outcomes and recovery\<close>

lemma immutable_terminal_effect:
  assumes step: "rollback_step s action outcome t"
    and old_record: "terminal_records s i = Some p"
  shows "terminal_records t i = Some p \<and>
    (\<forall>c \<in> terminal_cells p. cell_value t c = cell_value s c)"
proof (cases action)
  case (Execute_Rollback r a pf)
  with step have rb_exec: "rollback_step s (Execute_Rollback r a pf) outcome t" by simp
  have covered: "\<And>c. c \<in> terminal_cells p \<Longrightarrow> c \<in> protected s"
    using old_record by (auto simp: protected_def)
  show ?thesis
  proof (cases outcome)
    case (Accepted n)
    from rb_exec Accepted have ok: "rollback_step s (Execute_Rollback r a pf) (Accepted n) t" by simp
    from accepted_rollback[OF ok] obtain h where
      successful: "restoration_failure s r h = None" and target_eq: "t = restore s r h" by blast
    from successful have disjoint: "footprint r \<inter> protected s = {}"
      by (auto simp: restoration_failure_def split: if_splits)
    have outside: "\<And>c. c \<in> terminal_cells p \<Longrightarrow> c \<notin> footprint r"
      using disjoint covered by blast
    show ?thesis using old_record outside by (auto simp: target_eq restore_def update_cells_def)
  next
    case (Rejected why)
    with rb_exec have "rollback_step s (Execute_Rollback r a pf) (Rejected why) t" by simp
    then have "t = s" by (rule rejected_transition_unchanged)
    then show ?thesis using old_record by simp
  next
    case (Operational_Failure e)
    with rb_exec show ?thesis
      by (auto simp: rollback_step_def execute_rollback_def split: option.splits)
  next
    case (Internal e)
    with rb_exec show ?thesis
      by (auto simp: rollback_step_def execute_rollback_def split: option.splits)
  qed
next
  case (Record_Abort k)
  from step Record_Abort old_record show ?thesis
    by (auto simp: rollback_step_def split: option.splits if_splits)
next
  case (Record_Finality k)
  have covered: "\<And>c. c \<in> terminal_cells p \<Longrightarrow> c \<in> protected s"
    using old_record by (auto simp: protected_def)
  from step Record_Finality old_record show ?thesis
    by (auto simp: rollback_step_def preserve_protected_def update_cells_def
          split: option.splits if_splits dest: covered)
next
  case (Repair_From_Record k replica)
  from step Repair_From_Record old_record show ?thesis
    by (auto simp: rollback_step_def split: option.splits)
next
  case (Advance_Context time authority case_id policy)
  from step Advance_Context old_record show ?thesis
    by (auto simp: rollback_step_def split: if_splits)
qed

theorem abort_records_only_the_authenticated_pending_effect:
  assumes "rollback_step s (Record_Abort i) (Internal (Recorded_Abort i)) t"
  obtains h where "i \<in> abort_receipts s" "journal s i = Some h"
    "entry_stage h = External_Pending"
    "terminal_records s i = None" "finality_receipts s i = None"
    "journal t i = Some (h\<lparr>entry_stage := Aborted_Compensable\<rparr>)"
    "cell_value t = cell_value s" "replica_value t = replica_value s"
    "terminal_records t = terminal_records s"
    "\<And>j. j \<noteq> i \<Longrightarrow> journal t j = journal s j"
  using assms by (auto simp: rollback_step_def split: option.splits if_splits)

theorem aborted_effect_cannot_be_finalized:
  assumes "journal s i = Some h" "entry_stage h = Aborted_Compensable"
    and "finality_receipts s i = Some p"
  shows "rollback_step s (Record_Finality i) (Rejected Invalid_Context) s"
  using assms by (simp add: rollback_step_def finality_applicable_def)

lemma finality_installs_recorded_value:
  assumes "rollback_step s (Record_Finality i) (Internal (Recorded_Finality i)) t"
  obtains p where "finality_receipts s i = Some p" "terminal_records t i = Some p"
    "\<forall>c \<in> terminal_cells p. cell_value t c = terminal_value p c"
  using assms by (auto simp: rollback_step_def update_cells_def split: option.splits if_splits)

theorem new_receipt_agrees_with_existing_record_on_overlap:
  assumes step: "rollback_step s (Record_Finality j) (Internal (Recorded_Finality j)) t"
    and incoming: "finality_receipts s j = Some q"
    and installed: "terminal_records s i = Some p"
    and cell: "c \<in> terminal_cells p \<inter> terminal_cells q"
  shows "terminal_value q c = terminal_value p c"
proof -
  from step incoming have gate: "preserve_protected s (terminal_cells q) (terminal_value q)"
    by (auto simp: rollback_step_def split: if_splits)
  from gate installed cell show ?thesis unfolding preserve_protected_def by blast
qed

theorem finality_repair_matches_record:
  assumes "rollback_step s (Repair_From_Record i replica) (Internal (Repaired_From_Record i replica)) t"
  obtains p where "terminal_records s i = Some p"
    "\<forall>c \<in> terminal_cells p. replica_value t replica c = terminal_value p c"
    "preserves_outside (\<lambda>x. replica_value x replica) (terminal_cells p) s t"
    "cell_value t = cell_value s" "terminal_records t = terminal_records s"
  using assms by (auto simp: rollback_step_def update_cells_def preserves_outside_def split: option.splits)

theorem finalized_effect_survives_trace:
  assumes "finite_trace rollback_step carrier s events t" "terminal_records s i = Some p"
  shows "terminal_records t i = Some p \<and>
    (\<forall>c \<in> terminal_cells p. cell_value t c = cell_value s c)"
  using assms
proof (induction events arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  then have source: "source_state e = s" and tail:
    "finite_trace rollback_step carrier (target_state e) es t"
    and step: "rollback_step s (step_action e) (step_outcome e) (target_state e)"
    by (auto simp: step_occurs_def)
  from immutable_terminal_effect[OF step Cons.prems(2)] have
    prior_record: "terminal_records (target_state e) i = Some p" and
    old: "\<forall>c \<in> terminal_cells p. cell_value (target_state e) c = cell_value s c"
    by blast+
  from Cons.IH[OF tail prior_record] old show ?case by auto
qed

corollary no_literal_finalized_inverse:
  assumes "terminal_records s i = Some p" "c \<in> terminal_cells p"
    and "expected_prior \<noteq> cell_value s c"
  shows "\<not> (\<exists>t. finite_trace rollback_step carrier s events t \<and>
    cell_value t c = expected_prior)"
  using assms finalized_effect_survives_trace by metis

theorem installed_finality_value_survives_trace:
  assumes install: "rollback_step s (Record_Finality i) (Internal (Recorded_Finality i)) t"
    and tail: "finite_trace rollback_step carrier t events u"
  obtains p where "finality_receipts s i = Some p" "terminal_records u i = Some p"
    "\<forall>c \<in> terminal_cells p. cell_value u c = terminal_value p c"
proof -
  from finality_installs_recorded_value[OF install] obtain p where
    stored_receipt: "finality_receipts s i = Some p" and final_record: "terminal_records t i = Some p" and
    protected_values: "\<forall>c \<in> terminal_cells p. cell_value t c = terminal_value p c" by blast
  from finalized_effect_survives_trace[OF tail final_record] protected_values have
    "terminal_records u i = Some p"
    "\<forall>c \<in> terminal_cells p. cell_value u c = terminal_value p c" by auto
  from stored_receipt this show thesis by (rule that)
qed

theorem pending_and_finality_require_fence:
  assumes step: "rollback_step s (Execute_Rollback r approval role_proof) (Accepted i) t"
  obtains h where "journal s (undo_entry r) = Some h"
    "entry_stage h = Ordinary_Reversible \<or> entry_stage h = Aborted_Compensable"
    "footprint r \<inter> protected s = {}"
    "footprint r \<inter> other_unsettled_cells s (undo_entry r) = {}"
proof -
  from accepted_rollback[OF step] obtain h where
    entry: "journal s (undo_entry r) = Some h" and clear: "restoration_failure s r h = None"
    by blast
  from clear have stage: "entry_stage h = Ordinary_Reversible \<or> entry_stage h = Aborted_Compensable"
    by (cases "entry_stage h") (auto simp: restoration_failure_def split: if_splits)
  from clear have "footprint r \<inter> protected s = {}"
    and "footprint r \<inter> other_unsettled_cells s (undo_entry r) = {}"
    by (auto simp: restoration_failure_def split: if_splits)
  with entry stage show thesis by (rule that)
qed

corollary rollback_cannot_cross_unsettled_effect:
  assumes "i \<noteq> undo_entry r" "journal s i = Some h"
    and "entry_stage h = External_Pending \<or> entry_stage h = Irreversible"
    and "c \<in> entry_cells h" "c \<in> footprint r"
  shows "\<not> rollback_step s (Execute_Rollback r approval role_proof) (Accepted txn) t"
  using assms pending_and_finality_require_fence
  unfolding other_unsettled_cells_def by blast

section \<open>Case-local bound on rollback of rollback\<close>

definition accepted_case_step :: "nat \<Rightarrow> (rollback_state \<times> rollback_state) set"
where
  "accepted_case_step k = {(t,s). \<exists>r approval role_proof i.
      request_case r = k \<and> rollback_step s (Execute_Rollback r approval role_proof) (Accepted i) t}"

lemma successful_rollback_spends_unit:
  assumes step: "rollback_step s (Execute_Rollback r approval role_proof) (Accepted i) t"
  shows "case_remaining t (request_case r) + 1 = case_remaining s (request_case r)"
    and "\<And>k. k \<noteq> request_case r \<Longrightarrow> case_remaining t k = case_remaining s k"
proof -
  from accepted_rollback[OF step] obtain h where
    fail: "restoration_failure s r h = None" and t: "t = restore s r h" by blast
  from fail have "case_remaining s (request_case r) > 0"
    by (auto simp: restoration_failure_def split: if_splits)
  then show "case_remaining t (request_case r) + 1 = case_remaining s (request_case r)"
    by (simp add: t restore_def)
  fix k
  assume "k \<noteq> request_case r"
  then show "case_remaining t k = case_remaining s k" by (simp add: t restore_def)
qed

theorem rollback_cycle_well_founded:
  "wf (accepted_case_step k)"
proof (rule wf_subset[OF wf_rank_decreases[of "\<lambda>s. case_remaining s k"]])
  show "accepted_case_step k \<subseteq> {(t,s). rank_decreases (\<lambda>s. case_remaining s k) s t}"
  proof
    fix pair
    assume "pair \<in> accepted_case_step k"
    then obtain t s r a p i where pair: "pair = (t,s)" and key: "request_case r = k"
      and accepted: "rollback_step s (Execute_Rollback r a p) (Accepted i) t"
      by (auto simp: accepted_case_step_def)
    have "case_remaining t k + 1 = case_remaining s k"
      using successful_rollback_spends_unit(1)[OF accepted] key by simp
    then have "case_remaining t k < case_remaining s k" by linarith
    then show "pair \<in> {(t,s). rank_decreases (\<lambda>s. case_remaining s k) s t}"
      by (simp add: pair rank_decreases_def)
  qed
qed

fun rollback_charge :: "nat \<Rightarrow> rollback_action \<Rightarrow> rollback_result \<Rightarrow> nat"
where
  "rollback_charge k (Execute_Rollback r a p) (Accepted i) = (if request_case r = k then 1 else 0)"
| "rollback_charge k action result = 0"

lemma step_conserves_case_budget:
  assumes step: "rollback_step s action result t"
  shows "case_remaining t k + rollback_charge k action result = case_remaining s k"
proof (cases "\<exists>r a p i. action = Execute_Rollback r a p \<and> result = Accepted i")
  case True
  then obtain r a p i where act: "action = Execute_Rollback r a p"
    and res: "result = Accepted i" by blast
  have accepted: "rollback_step s (Execute_Rollback r a p) (Accepted i) t"
    using step act res by simp
  show ?thesis
  proof (cases "request_case r = k")
    case True
    then show ?thesis using successful_rollback_spends_unit(1)[OF accepted] by (simp add: act res)
  next
    case False
    then show ?thesis using successful_rollback_spends_unit(2)[OF accepted, of k] by (simp add: act res)
  qed
next
  case False
  then show ?thesis using step
    by (cases action; cases result)
      (auto simp: rollback_step_def execute_rollback_def split: option.splits if_splits)
qed

theorem trace_rollback_budget:
  assumes "finite_trace rollback_step carrier s events t"
  shows "case_remaining t k + sum_list (map (\<lambda>e. rollback_charge k (step_action e) (step_outcome e)) events)
    = case_remaining s k"
  using assms
proof (induction events arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  then have rest: "finite_trace rollback_step carrier (target_state e) es t"
    and consumes: "rollback_step s (step_action e) (step_outcome e) (target_state e)"
    by (auto simp: step_occurs_def)
  have "case_remaining t k +
      sum_list (map (\<lambda>e. rollback_charge k (step_action e) (step_outcome e)) (e # es)) =
      (case_remaining t k +
        sum_list (map (\<lambda>e. rollback_charge k (step_action e) (step_outcome e)) es)) +
          rollback_charge k (step_action e) (step_outcome e)"
    by (simp add: ac_simps)
  also have "\<dots> = case_remaining (target_state e) k + rollback_charge k (step_action e) (step_outcome e)"
    using Cons.IH[OF rest] by simp
  also have "\<dots> = case_remaining s k" by (rule step_conserves_case_budget[OF consumes])
  finally show ?case .
qed

end
