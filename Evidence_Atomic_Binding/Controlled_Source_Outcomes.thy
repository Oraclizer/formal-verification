(* SPDX-License-Identifier: BSD-3-Clause *)
theory Controlled_Source_Outcomes
  imports Source_Effect_Boundary
begin

section \<open>A Source Endpoint That Controls Its Own Outcome\<close>

text \<open>This is a conditional source API contract. Finalization and reversal
  below are operations of the authoritative source itself. A destination,
  relayer, timeout or local acknowledgment cannot invoke their semantic
  authority merely by constructing a command. The physical source API,
  authentication, persistence and exclusive control of the resource remain
  UNVERIFIED. No new consensus network or completed runtime is asserted.

  The endpoint embeds the preceding source boundary and executes its actual
  Apply, Fence and Query functions. A reversed effect retains its original
  immutable key, payload and debit history. Reversal adds one return record
  and restores available source units. Consequently the original gross
  allocation equation is not silently reused after a return: the equation
  here is available units plus historical debits equals genesis allocation
  plus recorded returns. The original history and immutable-map invariants
  are preserved.\<close>

datatype controlled_source_outcome =
    Controlled_Finalized transfer_binding
  | Controlled_Reversed transfer_binding

fun controlled_outcome_binding :: "controlled_source_outcome \<Rightarrow> transfer_binding" where
  "controlled_outcome_binding (Controlled_Finalized b)=b"
| "controlled_outcome_binding (Controlled_Reversed b)=b"

fun controlled_outcome_statement :: "controlled_source_outcome \<Rightarrow> source_statement" where
  "controlled_outcome_statement (Controlled_Finalized b)=
    \<lparr>statement_binding=b,statement_status=Finalized\<rparr>"
| "controlled_outcome_statement (Controlled_Reversed b)=
    \<lparr>statement_binding=b,statement_status=Reversed\<rparr>"

record controlled_source_state =
  controlled_endpoint :: source_boundary_state
  controlled_outcomes :: "source_key \<Rightarrow> controlled_source_outcome option"
  controlled_returns :: "transfer_binding list"

datatype controlled_source_command =
    Controlled_Boundary source_boundary_command
  | Controlled_Finalize transfer_binding
  | Controlled_Reverse transfer_binding
  | Controlled_Query_Outcome transfer_binding

datatype controlled_source_reply =
    Controlled_Boundary_Reply source_boundary_reply
  | Controlled_Outcome_Reply source_statement
  | Controlled_Outcome_Unknown
  | Controlled_Outcome_Rejected

definition initial_controlled_source :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  controlled_source_state" where
  "initial_controlled_source balances =
    \<lparr>controlled_endpoint=initial_source_boundary balances,
      controlled_outcomes=(\<lambda>_.None),controlled_returns=[]\<rparr>"

definition controlled_source_fact :: "controlled_source_state \<Rightarrow> source_key \<Rightarrow>
  source_statement option" where
  "controlled_source_fact s key=
    map_option controlled_outcome_statement (controlled_outcomes s key)"

definition controlled_pending_effect :: "transfer_binding \<Rightarrow> controlled_source_state \<Rightarrow>
  bool" where
  "controlled_pending_effect b s \<longleftrightarrow>
    boundary_has_effect b (controlled_endpoint s) \<and>
    controlled_outcomes s (binding_key b)=None"

definition controlled_record_finalized :: "transfer_binding \<Rightarrow> controlled_source_state \<Rightarrow>
  controlled_source_state" where
  "controlled_record_finalized b s =
    s\<lparr>controlled_outcomes:=(controlled_outcomes s)
      (binding_key b:=Some (Controlled_Finalized b))\<rparr>"

definition controlled_record_reversed :: "transfer_binding \<Rightarrow> controlled_source_state \<Rightarrow>
  controlled_source_state" where
  "controlled_record_reversed b s =
    s\<lparr>controlled_outcomes:=(controlled_outcomes s)
        (binding_key b:=Some (Controlled_Reversed b)),
      controlled_returns:=controlled_returns s@[b],
      controlled_endpoint:=(controlled_endpoint s)\<lparr>boundary_units:=
        (boundary_units (controlled_endpoint s))(source_account_of b:=
          boundary_units (controlled_endpoint s) (source_account_of b)+binding_amount b)\<rparr>\<rparr>"

definition controlled_finalize :: "transfer_binding \<Rightarrow> controlled_source_state \<Rightarrow>
  controlled_source_state \<times> controlled_source_reply" where
  "controlled_finalize b s =
    (case controlled_outcomes s (binding_key b) of
       None \<Rightarrow>
         if boundary_has_effect b (controlled_endpoint s)
         then (controlled_record_finalized b s,
           Controlled_Outcome_Reply (controlled_outcome_statement (Controlled_Finalized b)))
         else (s,Controlled_Outcome_Rejected)
     | Some (Controlled_Finalized old) \<Rightarrow>
         if old=b then (s,Controlled_Outcome_Reply
           (controlled_outcome_statement (Controlled_Finalized b)))
         else (s,Controlled_Outcome_Rejected)
     | Some (Controlled_Reversed old) \<Rightarrow> (s,Controlled_Outcome_Rejected))"

definition controlled_reverse :: "transfer_binding \<Rightarrow> controlled_source_state \<Rightarrow>
  controlled_source_state \<times> controlled_source_reply" where
  "controlled_reverse b s =
    (case controlled_outcomes s (binding_key b) of
       None \<Rightarrow>
         if boundary_has_effect b (controlled_endpoint s)
         then (controlled_record_reversed b s,
           Controlled_Outcome_Reply (controlled_outcome_statement (Controlled_Reversed b)))
         else (s,Controlled_Outcome_Rejected)
     | Some (Controlled_Finalized old) \<Rightarrow> (s,Controlled_Outcome_Rejected)
     | Some (Controlled_Reversed old) \<Rightarrow>
         if old=b then (s,Controlled_Outcome_Reply
           (controlled_outcome_statement (Controlled_Reversed b)))
         else (s,Controlled_Outcome_Rejected))"

fun controlled_boundary_allowed :: "source_boundary_command \<Rightarrow> controlled_source_state \<Rightarrow>
  bool" where
  "controlled_boundary_allowed (Boundary_Apply b) s =
    (case controlled_outcomes s (binding_key b) of
       Some (Controlled_Reversed old) \<Rightarrow> False | _ \<Rightarrow> True)"
| "controlled_boundary_allowed (Boundary_Fence b) s=True"
| "controlled_boundary_allowed (Boundary_Query b) s=True"

definition controlled_boundary :: "source_boundary_command \<Rightarrow> controlled_source_state \<Rightarrow>
  controlled_source_state \<times> controlled_source_reply" where
  "controlled_boundary command s =
    (if controlled_boundary_allowed command s
     then (let result=boundary_step command (controlled_endpoint s)
       in (s\<lparr>controlled_endpoint:=fst result\<rparr>,Controlled_Boundary_Reply (snd result)))
     else (s,Controlled_Outcome_Rejected))"

fun controlled_source_step :: "controlled_source_command \<Rightarrow> controlled_source_state \<Rightarrow>
  controlled_source_state \<times> controlled_source_reply" where
  "controlled_source_step (Controlled_Boundary command) s=controlled_boundary command s"
| "controlled_source_step (Controlled_Finalize b) s=controlled_finalize b s"
| "controlled_source_step (Controlled_Reverse b) s=controlled_reverse b s"
| "controlled_source_step (Controlled_Query_Outcome b) s=
    (s,case controlled_outcomes s (binding_key b) of
       None \<Rightarrow> Controlled_Outcome_Unknown
     | Some outcome \<Rightarrow>
         if controlled_outcome_binding outcome=b
         then Controlled_Outcome_Reply (controlled_outcome_statement outcome)
         else Controlled_Outcome_Rejected)"

fun run_controlled_source :: "controlled_source_command list \<Rightarrow> controlled_source_state \<Rightarrow>
  controlled_source_state" where
  "run_controlled_source [] s=s"
| "run_controlled_source (command#rest) s=
    run_controlled_source rest (fst (controlled_source_step command s))"

lemma controlled_run_append:
  "run_controlled_source (prefix@suffix) s=
    run_controlled_source suffix (run_controlled_source prefix s)"
  by (induction prefix arbitrary:s) auto

section \<open>Source Provenance and Net Resources\<close>

definition controlled_provenance :: "controlled_source_state \<Rightarrow> bool" where
  "controlled_provenance s \<longleftrightarrow>
    (\<forall>key outcome. controlled_outcomes s key=Some outcome \<longrightarrow>
      boundary_records (controlled_endpoint s) key=
        Some (Boundary_Effect (controlled_outcome_binding outcome)) \<and>
      binding_key (controlled_outcome_binding outcome)=key)"

definition controlled_return_history :: "controlled_source_state \<Rightarrow> bool" where
  "controlled_return_history s \<longleftrightarrow>
    distinct (map binding_key (controlled_returns s)) \<and>
    (\<forall>b\<in>set (controlled_returns s).
      controlled_outcomes s (binding_key b)=Some (Controlled_Reversed b)) \<and>
    (\<forall>key b. controlled_outcomes s key=Some (Controlled_Reversed b) \<longrightarrow>
      b\<in>set (controlled_returns s) \<and> binding_key b=key)"

definition controlled_returned :: "source_account \<Rightarrow> controlled_source_state \<Rightarrow> nat"
  where
  "controlled_returned account s =
    sum_list (map binding_amount
      (filter (\<lambda>b. source_account_of b=account) (controlled_returns s)))"

definition controlled_net_allocation :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  controlled_source_state \<Rightarrow> bool" where
  "controlled_net_allocation balances s \<longleftrightarrow>
    boundary_allocation (\<lambda>account. balances account+controlled_returned account s)
      (controlled_endpoint s)"

definition controlled_source_invariant :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  controlled_source_state \<Rightarrow> bool" where
  "controlled_source_invariant balances s \<longleftrightarrow>
    boundary_history_consistent (controlled_endpoint s) \<and>
    controlled_provenance s \<and> controlled_return_history s \<and>
    controlled_net_allocation balances s"

lemma controlled_initial_invariant:
  "controlled_source_invariant balances (initial_controlled_source balances)"
  by (simp add: controlled_source_invariant_def initial_controlled_source_def
    controlled_provenance_def controlled_return_history_def controlled_net_allocation_def
    controlled_returned_def boundary_initial_history boundary_initial_allocation)

lemma controlled_boundary_preserves_provenance:
  assumes "controlled_provenance s"
  shows "controlled_provenance
    (s\<lparr>controlled_endpoint:=fst (boundary_step command (controlled_endpoint s))\<rparr>)"
  using assms boundary_existing_record_survives_step
  unfolding controlled_provenance_def by auto

lemma controlled_boundary_preserves_net_allocation:
  assumes "controlled_net_allocation balances s"
  shows "controlled_net_allocation balances
    (s\<lparr>controlled_endpoint:=fst (boundary_step command (controlled_endpoint s))\<rparr>)"
proof -
  have before: "boundary_allocation
    (\<lambda>account. balances account+controlled_returned account s) (controlled_endpoint s)"
    using assms by (simp add: controlled_net_allocation_def)
  have after: "boundary_allocation
    (\<lambda>account. balances account+controlled_returned account s)
    (fst (boundary_step command (controlled_endpoint s)))"
    by (rule boundary_step_preserves_allocation[OF before])
  show ?thesis using after
    by (simp add: controlled_net_allocation_def controlled_returned_def)
qed

lemma controlled_boundary_preserves_invariant:
  assumes "controlled_source_invariant balances s"
  shows "controlled_source_invariant balances (fst (controlled_boundary command s))"
  using assms boundary_step_preserves_history
    controlled_boundary_preserves_provenance controlled_boundary_preserves_net_allocation
  by (auto simp: controlled_boundary_def Let_def controlled_source_invariant_def
    controlled_return_history_def)

lemma controlled_pending_key_has_no_return:
  assumes "controlled_return_history s" "controlled_outcomes s (binding_key b)=None"
  shows "binding_key b\<notin>set (map binding_key (controlled_returns s))"
  using assms by (auto simp: controlled_return_history_def)

lemma controlled_finalize_preserves_provenance:
  assumes "controlled_provenance s" "controlled_pending_effect b s"
  shows "controlled_provenance (controlled_record_finalized b s)"
  using assms
  by (auto simp: controlled_provenance_def controlled_pending_effect_def
    boundary_has_effect_def controlled_record_finalized_def)

lemma controlled_reverse_preserves_provenance:
  assumes "controlled_provenance s" "controlled_pending_effect b s"
  shows "controlled_provenance (controlled_record_reversed b s)"
  using assms
  by (auto simp: controlled_provenance_def controlled_pending_effect_def
    boundary_has_effect_def controlled_record_reversed_def)

lemma controlled_finalize_preserves_return_history:
  assumes "controlled_return_history s" "controlled_outcomes s (binding_key b)=None"
  shows "controlled_return_history (controlled_record_finalized b s)"
  using assms controlled_pending_key_has_no_return[OF assms]
  by (auto simp: controlled_return_history_def controlled_record_finalized_def)

lemma controlled_reverse_preserves_return_history:
  assumes "controlled_return_history s" "controlled_outcomes s (binding_key b)=None"
  shows "controlled_return_history (controlled_record_reversed b s)"
  using assms controlled_pending_key_has_no_return[OF assms]
  by (auto simp: controlled_return_history_def controlled_record_reversed_def)

lemma controlled_finalize_preserves_net_allocation:
  "controlled_net_allocation balances s \<Longrightarrow>
    controlled_net_allocation balances (controlled_record_finalized b s)"
  by (simp add: controlled_net_allocation_def controlled_returned_def controlled_record_finalized_def)

lemma controlled_net_allocation_at_account:
  assumes "controlled_net_allocation balances s"
  shows "boundary_units (controlled_endpoint s) account+
    boundary_debited account (controlled_endpoint s)=
    balances account+controlled_returned account s"
  using assms unfolding controlled_net_allocation_def boundary_allocation_def by blast

lemma controlled_reverse_preserves_net_allocation:
  assumes "controlled_net_allocation balances s"
  shows "controlled_net_allocation balances (controlled_record_reversed b s)"
proof (unfold controlled_net_allocation_def boundary_allocation_def, intro allI)
  fix account
  have old: "boundary_units (controlled_endpoint s) account+
    boundary_debited account (controlled_endpoint s)=
    balances account+controlled_returned account s"
    by (rule controlled_net_allocation_at_account[OF assms])
  have units: "boundary_units (controlled_endpoint (controlled_record_reversed b s)) account=
    boundary_units (controlled_endpoint s) account+
      (if account=source_account_of b then binding_amount b else 0)"
    by (auto simp: controlled_record_reversed_def)
  have debit: "boundary_debited account (controlled_endpoint (controlled_record_reversed b s))=
    boundary_debited account (controlled_endpoint s)"
    by (simp add: controlled_record_reversed_def boundary_debited_def)
  have returned: "controlled_returned account (controlled_record_reversed b s)=
    controlled_returned account s+
      (if account=source_account_of b then binding_amount b else 0)"
    by (auto simp: controlled_record_reversed_def controlled_returned_def)
  show "boundary_units (controlled_endpoint (controlled_record_reversed b s)) account+
    boundary_debited account (controlled_endpoint (controlled_record_reversed b s))=
    balances account+controlled_returned account (controlled_record_reversed b s)"
  proof -
    have "boundary_units (controlled_endpoint (controlled_record_reversed b s)) account+
      boundary_debited account (controlled_endpoint (controlled_record_reversed b s))=
      (boundary_units (controlled_endpoint s) account+
        boundary_debited account (controlled_endpoint s))+
        (if account=source_account_of b then binding_amount b else 0)"
      by (simp only: units debit; simp add: add.assoc add.left_commute add.commute)
    also have "...=(balances account+controlled_returned account s)+
      (if account=source_account_of b then binding_amount b else 0)"
      by (simp only: old)
    also have "...=balances account+
      controlled_returned account (controlled_record_reversed b s)"
      by (simp only: returned; simp add: add.assoc)
    finally show ?thesis .
  qed
qed

lemma controlled_record_finalized_preserves_invariant:
  assumes "controlled_source_invariant balances s" "controlled_pending_effect b s"
  shows "controlled_source_invariant balances (controlled_record_finalized b s)"
  using assms controlled_finalize_preserves_provenance
    controlled_finalize_preserves_return_history controlled_finalize_preserves_net_allocation
  by (auto simp: controlled_source_invariant_def controlled_pending_effect_def
    controlled_record_finalized_def)

lemma controlled_record_reversed_preserves_invariant:
  assumes "controlled_source_invariant balances s" "controlled_pending_effect b s"
  shows "controlled_source_invariant balances (controlled_record_reversed b s)"
  using assms controlled_reverse_preserves_provenance
    controlled_reverse_preserves_return_history controlled_reverse_preserves_net_allocation
  by (auto simp: controlled_source_invariant_def controlled_pending_effect_def
    controlled_record_reversed_def boundary_history_consistent_def)

theorem controlled_step_preserves_invariant:
  assumes "controlled_source_invariant balances s"
  shows "controlled_source_invariant balances (fst (controlled_source_step command s))"
  using assms
  by (cases command)
     (auto simp: controlled_finalize_def controlled_reverse_def controlled_pending_effect_def
       intro: controlled_boundary_preserves_invariant
         controlled_record_finalized_preserves_invariant controlled_record_reversed_preserves_invariant
       split: option.splits controlled_source_outcome.splits)

theorem controlled_run_preserves_invariant:
  "controlled_source_invariant balances s \<Longrightarrow>
    controlled_source_invariant balances (run_controlled_source commands s)"
  by (induction commands arbitrary:s) (auto intro: controlled_step_preserves_invariant)

theorem controlled_all_finite_executions:
  "controlled_source_invariant balances
    (run_controlled_source commands (initial_controlled_source balances))"
  by (rule controlled_run_preserves_invariant[OF controlled_initial_invariant])

lemma controlled_provenance_at_key:
  assumes "controlled_provenance s" "controlled_outcomes s key=Some outcome"
  shows "boundary_records (controlled_endpoint s) key=
      Some (Boundary_Effect (controlled_outcome_binding outcome)) \<and>
    binding_key (controlled_outcome_binding outcome)=key"
  using assms unfolding controlled_provenance_def by blast

theorem controlled_terminal_outcome_has_exact_source_effect:
  assumes "controlled_source_invariant balances s"
    "controlled_outcomes s key=Some outcome"
  shows "boundary_evidence_matches (controlled_outcome_binding outcome)
      (Boundary_Effect_Witness (controlled_outcome_binding outcome)) (controlled_endpoint s) \<and>
    controlled_outcome_binding outcome\<in>set (boundary_effects (controlled_endpoint s)) \<and>
    binding_key (controlled_outcome_binding outcome)=key"
proof -
  have history: "boundary_history_consistent (controlled_endpoint s)"
    and provenance: "controlled_provenance s"
    using assms(1) unfolding controlled_source_invariant_def by blast+
  have linked: "boundary_records (controlled_endpoint s) key=
      Some (Boundary_Effect (controlled_outcome_binding outcome)) \<and>
    binding_key (controlled_outcome_binding outcome)=key"
    by (rule controlled_provenance_at_key[OF provenance assms(2)])
  have recorded: "boundary_records (controlled_endpoint s) key=
    Some (Boundary_Effect (controlled_outcome_binding outcome))"
    using linked by blast
  have member: "controlled_outcome_binding outcome\<in>set
    (boundary_effects (controlled_endpoint s))"
    using boundary_recorded_effect_has_history[OF history recorded] by blast
  have effect: "boundary_has_effect (controlled_outcome_binding outcome) (controlled_endpoint s)"
    using linked by (simp add: boundary_has_effect_def)
  show ?thesis using effect member linked by (simp add: boundary_evidence_exact)
qed

theorem controlled_return_restores_exact_amount_and_preserves_history:
  assumes "controlled_pending_effect b s"
  shows "boundary_units (controlled_endpoint (fst (controlled_reverse b s))) (source_account_of b)=
      boundary_units (controlled_endpoint s) (source_account_of b)+binding_amount b \<and>
    boundary_records (controlled_endpoint (fst (controlled_reverse b s)))=
      boundary_records (controlled_endpoint s) \<and>
    boundary_effects (controlled_endpoint (fst (controlled_reverse b s)))=
      boundary_effects (controlled_endpoint s)"
  using assms by (simp add: controlled_pending_effect_def controlled_reverse_def
    controlled_record_reversed_def)

theorem controlled_net_resource_equation:
  assumes "controlled_source_invariant balances s"
  shows "boundary_units (controlled_endpoint s) account+
      boundary_debited account (controlled_endpoint s)=
    balances account+controlled_returned account s"
proof (rule controlled_net_allocation_at_account)
  show "controlled_net_allocation balances s"
    using assms unfolding controlled_source_invariant_def by blast
qed

theorem controlled_without_returns_recovers_original_allocation:
  assumes "controlled_source_invariant balances s" "controlled_returns s=[]"
  shows "boundary_allocation balances (controlled_endpoint s)"
  using assms
  by (simp add: controlled_source_invariant_def controlled_net_allocation_def controlled_returned_def)

theorem controlled_each_key_is_returned_at_most_once:
  "distinct (map binding_key (controlled_returns
    (run_controlled_source commands (initial_controlled_source balances))))"
  using controlled_all_finite_executions[of balances commands]
  unfolding controlled_source_invariant_def controlled_return_history_def by blast

section \<open>Immutable Source Outcomes\<close>

theorem controlled_outcome_survives_step:
  assumes "controlled_outcomes s key=Some outcome"
  shows "controlled_outcomes (fst (controlled_source_step command s)) key=Some outcome"
  using assms
  by (cases command)
     (auto simp: controlled_boundary_def controlled_finalize_def controlled_reverse_def
       controlled_record_finalized_def controlled_record_reversed_def Let_def
       split: option.splits controlled_source_outcome.splits)

theorem controlled_outcome_survives_continuation:
  "controlled_outcomes s key=Some outcome \<Longrightarrow>
    controlled_outcomes (run_controlled_source commands s) key=Some outcome"
  by (induction commands arbitrary:s) (auto intro: controlled_outcome_survives_step)

theorem controlled_fact_survives_continuation:
  assumes "controlled_source_fact s key=Some statement"
  shows "controlled_source_fact (run_controlled_source commands s) key=Some statement"
  using assms controlled_outcome_survives_continuation[of s key]
  by (auto simp: controlled_source_fact_def split: option.splits)

lemma controlled_outcome_is_terminal:
  "statement_status (controlled_outcome_statement outcome)\<noteq>Observed"
  by (cases outcome) simp_all

theorem controlled_fact_is_terminal:
  "controlled_source_fact s key=Some statement \<Longrightarrow>
    statement_status statement\<noteq>Observed"
  by (auto simp: controlled_source_fact_def controlled_outcome_is_terminal
    split: option.splits)

theorem controlled_reversal_rejects_late_finalize_and_apply:
  assumes "controlled_outcomes s key=Some (Controlled_Reversed b)"
    "binding_key other=key"
  shows "controlled_finalize other (run_controlled_source commands s)=
      (run_controlled_source commands s,Controlled_Outcome_Rejected) \<and>
    controlled_boundary (Boundary_Apply other) (run_controlled_source commands s)=
      (run_controlled_source commands s,Controlled_Outcome_Rejected)"
  using controlled_outcome_survives_continuation[OF assms(1), of commands] assms(2)
  by (simp add: controlled_finalize_def controlled_boundary_def)

theorem controlled_finalization_rejects_late_reverse:
  assumes "controlled_outcomes s key=Some (Controlled_Finalized b)" "binding_key other=key"
  shows "controlled_reverse other (run_controlled_source commands s)=
    (run_controlled_source commands s,Controlled_Outcome_Rejected)"
  using controlled_outcome_survives_continuation[OF assms(1), of commands] assms(2)
  by (simp add: controlled_reverse_def)

theorem controlled_reversal_retry_returns_nothing_again:
  assumes "controlled_outcomes s (binding_key b)=Some (Controlled_Reversed b)"
  shows "fst (controlled_reverse b s)=s"
  using assms by (simp add: controlled_reverse_def)

theorem controlled_same_key_different_terminal_binding_rejected:
  assumes "controlled_outcomes s key=Some outcome"
    "binding_key b=key" "b\<noteq>controlled_outcome_binding outcome"
  shows "controlled_finalize b s=(s,Controlled_Outcome_Rejected) \<and>
    controlled_reverse b s=(s,Controlled_Outcome_Rejected)"
  using assms by (cases outcome) (auto simp: controlled_finalize_def controlled_reverse_def)

theorem controlled_unknown_source_effect_cannot_finalize_or_reverse:
  assumes "\<not>boundary_has_effect b (controlled_endpoint s)"
    "controlled_outcomes s (binding_key b)=None"
  shows "controlled_finalize b s=(s,Controlled_Outcome_Rejected) \<and>
    controlled_reverse b s=(s,Controlled_Outcome_Rejected)"
  using assms by (simp add: controlled_finalize_def controlled_reverse_def)

theorem controlled_original_fence_is_not_a_reversal_fact:
  assumes "boundary_has_no_effect b (controlled_endpoint s)"
    "controlled_outcomes s (binding_key b)=None"
  shows "controlled_source_fact s (binding_key b)=None \<and>
    controlled_finalize b s=(s,Controlled_Outcome_Rejected) \<and>
    controlled_reverse b s=(s,Controlled_Outcome_Rejected)"
  using assms
  by (simp add: controlled_source_fact_def controlled_finalize_def controlled_reverse_def
    boundary_has_no_effect_def boundary_has_effect_def)

lemma controlled_statement_preserves_binding:
  "statement_binding (controlled_outcome_statement outcome)=controlled_outcome_binding outcome"
  by (cases outcome) simp_all

theorem controlled_successful_outcome_reply_is_recorded:
  assumes "snd (controlled_source_step command s)=Controlled_Outcome_Reply statement"
  shows "controlled_source_fact (fst (controlled_source_step command s))
    (binding_key (statement_binding statement))=Some statement"
  using assms
  by (cases command)
     (auto simp: controlled_boundary_def controlled_finalize_def controlled_reverse_def
       controlled_record_finalized_def controlled_record_reversed_def controlled_source_fact_def
       controlled_statement_preserves_binding Let_def
       split: option.splits controlled_source_outcome.splits if_splits)

section \<open>Supplying Stable Facts Without an Oracle Premise\<close>

definition controlled_produced_fact :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  controlled_source_command list \<Rightarrow> source_statement \<Rightarrow> bool" where
  "controlled_produced_fact balances commands statement \<longleftrightarrow>
    (\<exists>prefix suffix. commands=prefix@suffix \<and>
      controlled_source_fact (run_controlled_source prefix (initial_controlled_source balances))
        (binding_key (statement_binding statement))=Some statement)"

definition controlled_stable_source :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  controlled_source_command list \<Rightarrow> source_key \<Rightarrow> source_statement option" where
  "controlled_stable_source balances commands=
    controlled_source_fact (run_controlled_source commands (initial_controlled_source balances))"

lemma controlled_current_fact_is_produced:
  assumes "controlled_source_fact (run_controlled_source commands (initial_controlled_source balances))
    (binding_key (statement_binding statement))=Some statement"
  shows "controlled_produced_fact balances commands statement"
  using assms unfolding controlled_produced_fact_def
  by (intro exI[where x=commands] exI[where x="[]"]) simp

theorem controlled_actual_reply_produces_source_fact:
  assumes "snd (controlled_source_step command
    (run_controlled_source prefix (initial_controlled_source balances)))=
    Controlled_Outcome_Reply statement"
  shows "controlled_produced_fact balances (prefix@[command]) statement"
  by (rule controlled_current_fact_is_produced)
     (use controlled_successful_outcome_reply_is_recorded[OF assms]
       in \<open>simp add: controlled_run_append\<close>)

theorem controlled_producer_supplies_stable_fact:
  assumes "controlled_produced_fact balances commands statement"
  shows "controlled_stable_source balances commands
    (binding_key (statement_binding statement))=Some statement"
proof -
  obtain prefix suffix where decomposition: "commands=prefix@suffix"
    and recorded: "controlled_source_fact
      (run_controlled_source prefix (initial_controlled_source balances))
      (binding_key (statement_binding statement))=Some statement"
    using assms unfolding controlled_produced_fact_def by blast
  have persistent: "controlled_source_fact
    (run_controlled_source suffix
      (run_controlled_source prefix (initial_controlled_source balances)))
    (binding_key (statement_binding statement))=Some statement"
    by (rule controlled_fact_survives_continuation
      [where s="run_controlled_source prefix (initial_controlled_source balances)"
        and key="binding_key (statement_binding statement)"
        and statement=statement and commands=suffix])
       (rule recorded)
  show ?thesis using persistent
    by (simp only: controlled_stable_source_def decomposition controlled_run_append)
qed

theorem controlled_producer_supplies_stable_fact_unique_premise:
  assumes "controlled_produced_fact balances commands statement"
    "statement_status statement\<noteq>Observed"
  shows "controlled_stable_source balances commands
    (binding_key (statement_binding statement))=Some statement"
  by (rule controlled_producer_supplies_stable_fact[OF assms(1)])

theorem controlled_historical_facts_for_one_source_do_not_conflict:
  assumes "controlled_produced_fact balances commands first"
    "controlled_produced_fact balances commands second"
    "binding_key (statement_binding first)=binding_key (statement_binding second)"
  shows "first=second"
proof -
  have first_lookup: "controlled_stable_source balances commands
    (binding_key (statement_binding first))=Some first"
    by (rule controlled_producer_supplies_stable_fact
      [where balances=balances and commands=commands and statement=first])
       (rule assms(1))
  have second_lookup: "controlled_stable_source balances commands
    (binding_key (statement_binding second))=Some second"
    by (rule controlled_producer_supplies_stable_fact
      [where balances=balances and commands=commands and statement=second])
       (rule assms(2))
  show ?thesis using first_lookup second_lookup assms(3) by (metis option.inject)
qed

theorem controlled_produced_fact_has_exact_binding_and_debit:
  assumes fact: "controlled_produced_fact balances commands statement"
  shows "statement_binding statement\<in>set (boundary_effects (controlled_endpoint
      (run_controlled_source commands (initial_controlled_source balances)))) \<and>
    statement_status statement\<noteq>Observed"
proof -
  let ?s="run_controlled_source commands (initial_controlled_source balances)"
  have stable: "controlled_source_fact ?s (binding_key (statement_binding statement))=Some statement"
    using controlled_producer_supplies_stable_fact[OF fact]
    unfolding controlled_stable_source_def .
  then obtain outcome where outcome:
    "controlled_outcomes ?s (binding_key (statement_binding statement))=Some outcome"
    "controlled_outcome_statement outcome=statement"
    by (auto simp: controlled_source_fact_def split: option.splits)
  have provenance: "controlled_outcome_binding outcome\<in>set
    (boundary_effects (controlled_endpoint ?s))"
    using controlled_terminal_outcome_has_exact_source_effect
      [OF controlled_all_finite_executions outcome(1)] by blast
  show ?thesis using provenance outcome(2) controlled_fact_is_terminal[OF stable]
    by (cases outcome) auto
qed

text \<open>For a fixed actual finite source execution, produced_fact is computed
  from its prefix states and stable_source is its final outcome map. The
  preceding theorem supplies the parent's stable_fact_unique premise without
  assuming a source-truth oracle or the desired no-future-effect conclusion.
  Longer executions preserve every previously produced fact.

  Authentication must still show that an accepted certificate states one of
  these produced facts for the same authoritative source execution and
  immutable source identity. Signature soundness, truthful attestation and
  authenticated epoch membership are separate obligations. In particular,
  different possible executions from one initial state must not be combined
  into one truth predicate: one may select Finalized and another Reversed.
  Independent endpoints agree only when their evidence belongs to the same
  actual source history or compatible prefixes of it.\<close>

section \<open>The Missing Primitive and Concrete Branches\<close>

theorem controlled_pending_effect_alone_has_no_terminal_fact:
  "controlled_pending_effect b s \<Longrightarrow>
    controlled_source_fact s (binding_key b)=None"
  by (simp add: controlled_pending_effect_def controlled_source_fact_def)

theorem controlled_pending_effect_has_two_distinct_legal_continuations:
  assumes "controlled_pending_effect b s"
  shows "controlled_source_fact (fst (controlled_finalize b s)) (binding_key b)=
      Some \<lparr>statement_binding=b,statement_status=Finalized\<rparr> \<and>
    controlled_source_fact (fst (controlled_reverse b s)) (binding_key b)=
      Some \<lparr>statement_binding=b,statement_status=Reversed\<rparr>"
  using assms
  by (simp add: controlled_pending_effect_def controlled_finalize_def controlled_reverse_def
    controlled_record_finalized_def controlled_record_reversed_def controlled_source_fact_def)

theorem controlled_no_single_stable_map_for_alternative_outcomes:
  assumes "controlled_pending_effect b s"
  shows "\<not>(\<exists>stable.
    stable (binding_key b)=controlled_source_fact (fst (controlled_finalize b s)) (binding_key b) \<and>
    stable (binding_key b)=controlled_source_fact (fst (controlled_reverse b s)) (binding_key b))"
  using controlled_pending_effect_has_two_distinct_legal_continuations[OF assms] by auto

definition controlled_sample_pending :: controlled_source_state where
  "controlled_sample_pending=fst (controlled_boundary (Boundary_Apply boundary_sample_binding)
    (initial_controlled_source (\<lambda>_.5)))"

lemma controlled_sample_pending_is_pending:
  "controlled_pending_effect boundary_sample_binding controlled_sample_pending"
  by (simp add: controlled_sample_pending_def controlled_pending_effect_def
    controlled_boundary_def initial_controlled_source_def initial_source_boundary_def
    boundary_apply_def boundary_record_effect_def boundary_has_effect_def
    boundary_valid_binding_def boundary_sample_binding_def Let_def)

theorem controlled_both_terminal_branches_are_inhabited:
  "controlled_source_fact (fst (controlled_finalize boundary_sample_binding controlled_sample_pending))
      (binding_key boundary_sample_binding)=
      Some \<lparr>statement_binding=boundary_sample_binding,statement_status=Finalized\<rparr> \<and>
    controlled_source_fact (fst (controlled_reverse boundary_sample_binding controlled_sample_pending))
      (binding_key boundary_sample_binding)=
      Some \<lparr>statement_binding=boundary_sample_binding,statement_status=Reversed\<rparr>"
  by (rule controlled_pending_effect_has_two_distinct_legal_continuations
    [OF controlled_sample_pending_is_pending])

theorem controlled_sample_reverse_restores_three_units:
  "boundary_units (controlled_endpoint
      (fst (controlled_reverse boundary_sample_binding controlled_sample_pending)))
      (source_account_of boundary_sample_binding)=5"
  by (simp add: controlled_sample_pending_def controlled_boundary_def
    initial_controlled_source_def initial_source_boundary_def
    controlled_reverse_def controlled_record_reversed_def
    boundary_apply_def boundary_record_effect_def boundary_has_effect_def
    boundary_valid_binding_def boundary_sample_binding_def source_account_of_def Let_def)

theorem controlled_returned_resources_can_fund_a_new_key:
  "boundary_units (controlled_endpoint (fst (controlled_boundary
      (Boundary_Apply (boundary_sample_binding\<lparr>binding_key:=(0,2),binding_amount:=4\<rparr>))
      (fst (controlled_reverse boundary_sample_binding controlled_sample_pending)))))
      (source_account_of boundary_sample_binding)=1"
  by (simp add: controlled_sample_pending_def controlled_boundary_def
    initial_controlled_source_def initial_source_boundary_def
    controlled_reverse_def controlled_record_reversed_def
    boundary_apply_def boundary_record_effect_def boundary_has_effect_def boundary_valid_binding_def
    boundary_sample_binding_def source_account_of_def Let_def)

text \<open>For an external source that cannot atomically record its own immutable
  outcome and exclude the opposing operation, this controlled profile has
  not been realized. The preceding boundary's lost-command/lost-reply
  indistinguishability remains applicable. An Effect witness records that
  the source executed; it neither chooses finalization nor proves reversal.
  Such a missing primitive leaves the outcome unknown until authenticated
  source evidence arrives. This is a producer obstruction, not a decision
  to exclude any supported asset or external domain.

  The logical reverse here owns restoration of its source allocation.
  A downstream model must map this restoration to its corresponding source
  resource and must not count a second independent refund of the same
  allocation. Secondary propagation failures cannot call reverse after
  a Finalized outcome. A later compensating or regulatory operation needs
  its own lawful identity; it cannot overwrite this key's original outcome.\<close>

end
