(* SPDX-License-Identifier: BSD-3-Clause *)
theory Source_Effect_Boundary
  imports "Preemptive_Lock_Correctness.Reservation_Types"
begin

section \<open>Persistent Source Operations\<close>

text \<open>This theory specifies one logical authoritative source endpoint.
  Its physical implementation, caller authentication, authenticated API
  transport and crash durability are UNVERIFIED. In particular, a caller's
  local log is not the endpoint's persistent record. The model does not
  establish distributed consensus or source-chain finality.

  Source keys and full transfer bindings are the existing parent types.
  A retry, route change or worker replacement does not allocate a new key.
  The first accepted effect or fence binds the entire payload permanently.
  Fencing an unused key records non-effect; fencing an executed key fails.
  A source-effect witness is not a finality certificate or terminal decision.\<close>

datatype source_boundary_record =
    Boundary_Effect transfer_binding
  | Boundary_Fenced transfer_binding

fun boundary_record_binding :: "source_boundary_record \<Rightarrow> transfer_binding" where
  "boundary_record_binding (Boundary_Effect b) = b"
| "boundary_record_binding (Boundary_Fenced b) = b"

record source_boundary_state =
  boundary_records :: "source_key \<Rightarrow> source_boundary_record option"
  boundary_units :: "source_account \<Rightarrow> nat"
  boundary_effects :: "transfer_binding list"

datatype source_boundary_evidence =
    Boundary_Effect_Witness transfer_binding
  | Boundary_No_Effect_Witness transfer_binding

datatype source_boundary_reply =
    Boundary_Unknown
  | Boundary_Rejected
  | Boundary_Acknowledged source_boundary_evidence

datatype source_boundary_command =
    Boundary_Apply transfer_binding
  | Boundary_Fence transfer_binding
  | Boundary_Query transfer_binding

definition initial_source_boundary :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  source_boundary_state" where
  "initial_source_boundary balances =
    \<lparr>boundary_records=(\<lambda>_.None), boundary_units=balances, boundary_effects=[]\<rparr>"

definition boundary_valid_binding :: "transfer_binding \<Rightarrow> bool" where
  "boundary_valid_binding b \<longleftrightarrow>
    binding_operation b=Destination_Credit \<and> 0<binding_amount b"

definition boundary_has_effect :: "transfer_binding \<Rightarrow> source_boundary_state \<Rightarrow> bool"
  where
  "boundary_has_effect b s \<longleftrightarrow>
    boundary_records s (binding_key b)=Some (Boundary_Effect b)"

definition boundary_has_no_effect :: "transfer_binding \<Rightarrow> source_boundary_state \<Rightarrow> bool"
  where
  "boundary_has_no_effect b s \<longleftrightarrow>
    boundary_records s (binding_key b)=Some (Boundary_Fenced b)"

definition boundary_evidence :: "transfer_binding \<Rightarrow> source_boundary_state \<Rightarrow>
  source_boundary_evidence option" where
  "boundary_evidence b s =
    (case boundary_records s (binding_key b) of
       None \<Rightarrow> None
     | Some (Boundary_Effect old) \<Rightarrow>
         if old=b then Some (Boundary_Effect_Witness b) else None
     | Some (Boundary_Fenced old) \<Rightarrow>
         if old=b then Some (Boundary_No_Effect_Witness b) else None)"

definition boundary_evidence_matches :: "transfer_binding \<Rightarrow> source_boundary_evidence
  \<Rightarrow> source_boundary_state \<Rightarrow> bool" where
  "boundary_evidence_matches b evidence s \<longleftrightarrow>
    boundary_evidence b s=Some evidence"

definition boundary_record_effect :: "transfer_binding \<Rightarrow> source_boundary_state \<Rightarrow>
  source_boundary_state" where
  "boundary_record_effect b s =
    s\<lparr>boundary_records := (boundary_records s)(binding_key b:=Some (Boundary_Effect b)),
      boundary_units := (boundary_units s)(source_account_of b:=
        boundary_units s (source_account_of b)-binding_amount b),
      boundary_effects := boundary_effects s@[b]\<rparr>"

definition boundary_record_fence :: "transfer_binding \<Rightarrow> source_boundary_state \<Rightarrow>
  source_boundary_state" where
  "boundary_record_fence b s =
    s\<lparr>boundary_records := (boundary_records s)(binding_key b:=Some (Boundary_Fenced b))\<rparr>"

definition boundary_apply :: "transfer_binding \<Rightarrow> source_boundary_state \<Rightarrow>
  source_boundary_state \<times> source_boundary_reply" where
  "boundary_apply b s =
    (case boundary_records s (binding_key b) of
       None \<Rightarrow>
         if boundary_valid_binding b \<and>
            binding_amount b\<le>boundary_units s (source_account_of b)
         then (boundary_record_effect b s,Boundary_Acknowledged (Boundary_Effect_Witness b))
         else (s,Boundary_Rejected)
     | Some (Boundary_Effect old) \<Rightarrow>
         if old=b then (s,Boundary_Acknowledged (Boundary_Effect_Witness b))
         else (s,Boundary_Rejected)
     | Some (Boundary_Fenced old) \<Rightarrow> (s,Boundary_Rejected))"

definition boundary_fence :: "transfer_binding \<Rightarrow> source_boundary_state \<Rightarrow>
  source_boundary_state \<times> source_boundary_reply" where
  "boundary_fence b s =
    (case boundary_records s (binding_key b) of
       None \<Rightarrow>
         if boundary_valid_binding b
         then (boundary_record_fence b s,Boundary_Acknowledged (Boundary_No_Effect_Witness b))
         else (s,Boundary_Rejected)
     | Some (Boundary_Effect old) \<Rightarrow> (s,Boundary_Rejected)
     | Some (Boundary_Fenced old) \<Rightarrow>
         if old=b then (s,Boundary_Acknowledged (Boundary_No_Effect_Witness b))
         else (s,Boundary_Rejected))"

fun boundary_step :: "source_boundary_command \<Rightarrow> source_boundary_state \<Rightarrow>
  source_boundary_state \<times> source_boundary_reply" where
  "boundary_step (Boundary_Apply b) s = boundary_apply b s"
| "boundary_step (Boundary_Fence b) s = boundary_fence b s"
| "boundary_step (Boundary_Query b) s =
    (s,case boundary_evidence b s of None \<Rightarrow> Boundary_Unknown
       | Some evidence \<Rightarrow> Boundary_Acknowledged evidence)"

fun run_source_boundary :: "source_boundary_command list \<Rightarrow> source_boundary_state \<Rightarrow>
  source_boundary_state" where
  "run_source_boundary [] s=s"
| "run_source_boundary (command#rest) s=
    run_source_boundary rest (fst (boundary_step command s))"

section \<open>Identity, Evidence and Conservation\<close>

definition boundary_history_consistent :: "source_boundary_state \<Rightarrow> bool" where
  "boundary_history_consistent s \<longleftrightarrow>
    distinct (map binding_key (boundary_effects s)) \<and>
    (\<forall>b\<in>set (boundary_effects s).
      boundary_records s (binding_key b)=Some (Boundary_Effect b)) \<and>
    (\<forall>key b. boundary_records s key=Some (Boundary_Effect b) \<longrightarrow>
      b\<in>set (boundary_effects s) \<and> binding_key b=key) \<and>
    (\<forall>key b. boundary_records s key=Some (Boundary_Fenced b) \<longrightarrow>
      binding_key b=key)"

definition boundary_debited :: "source_account \<Rightarrow> source_boundary_state \<Rightarrow> nat"
  where
  "boundary_debited account s =
    sum_list (map binding_amount
      (filter (\<lambda>b. source_account_of b=account) (boundary_effects s)))"

definition boundary_allocation :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  source_boundary_state \<Rightarrow> bool" where
  "boundary_allocation balances s \<longleftrightarrow>
    (\<forall>account. boundary_units s account+boundary_debited account s=balances account)"

lemma boundary_initial_history:
  "boundary_history_consistent (initial_source_boundary balances)"
  by (simp add: boundary_history_consistent_def initial_source_boundary_def)

lemma boundary_initial_allocation:
  "boundary_allocation balances (initial_source_boundary balances)"
  by (simp add: boundary_allocation_def boundary_debited_def initial_source_boundary_def)

lemma boundary_unused_key_is_fresh:
  assumes "boundary_history_consistent s" "boundary_records s (binding_key b)=None"
  shows "binding_key b\<notin>set (map binding_key (boundary_effects s))"
  using assms by (auto simp: boundary_history_consistent_def)

lemma boundary_record_effect_preserves_history:
  assumes "boundary_history_consistent s" "boundary_records s (binding_key b)=None"
  shows "boundary_history_consistent (boundary_record_effect b s)"
  using assms boundary_unused_key_is_fresh[OF assms]
  by (auto simp: boundary_history_consistent_def boundary_record_effect_def)

lemma boundary_record_fence_preserves_history:
  assumes "boundary_history_consistent s" "boundary_records s (binding_key b)=None"
  shows "boundary_history_consistent (boundary_record_fence b s)"
  using assms boundary_unused_key_is_fresh[OF assms]
  by (auto simp: boundary_history_consistent_def boundary_record_fence_def)

lemma boundary_record_effect_preserves_allocation:
  assumes inv: "boundary_allocation balances s"
    and enough: "binding_amount b\<le>boundary_units s (source_account_of b)"
  shows "boundary_allocation balances (boundary_record_effect b s)"
proof (unfold boundary_allocation_def, intro allI)
  fix account
  have old: "boundary_units s account+boundary_debited account s=balances account"
    using inv unfolding boundary_allocation_def by blast
  have units: "boundary_units (boundary_record_effect b s) account=
    (if account=source_account_of b then boundary_units s account-binding_amount b
     else boundary_units s account)"
    by (auto simp: boundary_record_effect_def)
  have debit: "boundary_debited account (boundary_record_effect b s)=
    boundary_debited account s+
      (if source_account_of b=account then binding_amount b else 0)"
    by (simp add: boundary_record_effect_def boundary_debited_def)
  show "boundary_units (boundary_record_effect b s) account+
    boundary_debited account (boundary_record_effect b s)=balances account"
  proof (cases "account=source_account_of b")
    case True
    have bound: "binding_amount b\<le>boundary_units s account"
      using enough True by simp
    have arithmetic: "boundary_units s account-binding_amount b+
      (boundary_debited account s+binding_amount b)=
      boundary_units s account+boundary_debited account s"
      using bound by arith
    show ?thesis using units debit arithmetic old True by simp
  next
    case False
    show ?thesis using units debit old False by simp
  qed
qed

lemma boundary_record_fence_preserves_allocation:
  "boundary_allocation balances s \<Longrightarrow>
    boundary_allocation balances (boundary_record_fence b s)"
  by (simp add: boundary_allocation_def boundary_debited_def boundary_record_fence_def)

theorem boundary_step_preserves_history:
  assumes "boundary_history_consistent s"
  shows "boundary_history_consistent (fst (boundary_step command s))"
  using assms
  by (cases command)
     (auto simp: boundary_apply_def boundary_fence_def
       intro: boundary_record_effect_preserves_history boundary_record_fence_preserves_history
       split: option.splits source_boundary_record.splits)

theorem boundary_step_preserves_allocation:
  assumes "boundary_allocation balances s"
  shows "boundary_allocation balances (fst (boundary_step command s))"
  using assms
  by (cases command)
     (auto simp: boundary_apply_def boundary_fence_def
       intro: boundary_record_effect_preserves_allocation boundary_record_fence_preserves_allocation
       split: option.splits source_boundary_record.splits)

theorem boundary_run_preserves_history:
  "boundary_history_consistent s \<Longrightarrow>
    boundary_history_consistent (run_source_boundary commands s)"
  by (induction commands arbitrary:s) (auto intro: boundary_step_preserves_history)

theorem boundary_run_preserves_allocation:
  "boundary_allocation balances s \<Longrightarrow>
    boundary_allocation balances (run_source_boundary commands s)"
  by (induction commands arbitrary:s) (auto intro: boundary_step_preserves_allocation)

theorem boundary_finite_execution_contract:
  "boundary_history_consistent (run_source_boundary commands (initial_source_boundary balances)) \<and>
   boundary_allocation balances (run_source_boundary commands (initial_source_boundary balances))"
  using boundary_run_preserves_history[OF boundary_initial_history]
    boundary_run_preserves_allocation[OF boundary_initial_allocation] by blast

theorem boundary_arbitrary_trace_executes_each_key_at_most_once:
  "distinct (map binding_key
    (boundary_effects (run_source_boundary commands (initial_source_boundary balances))))"
  using boundary_finite_execution_contract[of commands balances]
  unfolding boundary_history_consistent_def by blast

theorem boundary_existing_record_survives_step:
  assumes "boundary_records s key=Some record"
  shows "boundary_records (fst (boundary_step command s)) key=Some record"
  using assms
  by (cases command)
     (auto simp: boundary_apply_def boundary_fence_def boundary_record_effect_def
       boundary_record_fence_def split: option.splits source_boundary_record.splits)

theorem boundary_existing_record_survives_continuation:
  assumes "boundary_records s key=Some record"
  shows "boundary_records (run_source_boundary commands s) key=Some record"
  using assms by (induction commands arbitrary:s)
    (auto intro: boundary_existing_record_survives_step)

theorem boundary_same_key_different_binding_rejected:
  assumes "boundary_records s key=Some record"
    "binding_key b=key" "b\<noteq>boundary_record_binding record"
  shows "boundary_apply b s=(s,Boundary_Rejected) \<and>
    boundary_fence b s=(s,Boundary_Rejected) \<and> boundary_evidence b s=None"
  using assms by (cases "record")
    (auto simp: boundary_apply_def boundary_fence_def boundary_evidence_def)

theorem boundary_evidence_exact:
  "boundary_evidence_matches b evidence s \<longleftrightarrow>
    (evidence=Boundary_Effect_Witness b \<and> boundary_has_effect b s) \<or>
    (evidence=Boundary_No_Effect_Witness b \<and> boundary_has_no_effect b s)"
  by (auto simp: boundary_evidence_matches_def boundary_evidence_def
    boundary_has_effect_def boundary_has_no_effect_def
    split: option.splits source_boundary_record.splits if_splits)

lemma boundary_recorded_effect_has_history:
  assumes "boundary_history_consistent s" "boundary_records s key=Some (Boundary_Effect b)"
  shows "b\<in>set (boundary_effects s) \<and> binding_key b=key"
  using assms unfolding boundary_history_consistent_def by blast

theorem boundary_effect_evidence_has_recorded_effect:
  assumes "boundary_history_consistent s"
    "boundary_evidence_matches b (Boundary_Effect_Witness b) s"
  shows "b\<in>set (boundary_effects s)"
proof -
  have recorded: "boundary_records s (binding_key b)=Some (Boundary_Effect b)"
    using assms(2) by (simp add: boundary_evidence_exact boundary_has_effect_def)
  show ?thesis using boundary_recorded_effect_has_history[OF assms(1) recorded] by blast
qed

theorem boundary_effect_and_non_effect_are_disjoint:
  "\<not>(boundary_has_effect b s \<and> boundary_has_no_effect b s)"
  by (simp add: boundary_has_effect_def boundary_has_no_effect_def)

theorem boundary_fence_rejects_every_late_effect:
  assumes "boundary_has_no_effect b s" "binding_key other=binding_key b"
  shows "boundary_apply other (run_source_boundary commands s)=
    (run_source_boundary commands s,Boundary_Rejected)"
  using boundary_existing_record_survives_continuation[of s "binding_key b"
      "Boundary_Fenced b" commands] assms
  by (simp add: boundary_has_no_effect_def boundary_apply_def)

theorem boundary_effect_rejects_every_late_fence:
  assumes "boundary_has_effect b s" "binding_key other=binding_key b"
  shows "boundary_fence other (run_source_boundary commands s)=
    (run_source_boundary commands s,Boundary_Rejected)"
  using boundary_existing_record_survives_continuation[of s "binding_key b"
      "Boundary_Effect b" commands] assms
  by (simp add: boundary_has_effect_def boundary_fence_def)

theorem boundary_no_effect_evidence_excludes_every_recorded_effect:
  assumes inv: "boundary_history_consistent s"
    and evidence: "boundary_evidence_matches b (Boundary_No_Effect_Witness b) s"
  shows "binding_key b\<notin>set (map binding_key
    (boundary_effects (run_source_boundary commands s)))"
proof -
  have recorded: "boundary_records s (binding_key b)=Some (Boundary_Fenced b)"
    using evidence by (simp add: boundary_evidence_exact boundary_has_no_effect_def)
  have persistent: "boundary_records (run_source_boundary commands s) (binding_key b)=
    Some (Boundary_Fenced b)"
    by (rule boundary_existing_record_survives_continuation[OF recorded])
  have history: "boundary_history_consistent (run_source_boundary commands s)"
    by (rule boundary_run_preserves_history[OF inv])
  show ?thesis using persistent history by (auto simp: boundary_history_consistent_def)
qed

theorem boundary_effect_retry_changes_nothing:
  "boundary_has_effect b s \<Longrightarrow>
    boundary_apply b s=(s,Boundary_Acknowledged (Boundary_Effect_Witness b))"
  by (simp add: boundary_has_effect_def boundary_apply_def)

theorem boundary_fence_retry_changes_nothing:
  "boundary_has_no_effect b s \<Longrightarrow>
    boundary_fence b s=(s,Boundary_Acknowledged (Boundary_No_Effect_Witness b))"
  by (simp add: boundary_has_no_effect_def boundary_fence_def)

theorem boundary_unused_fence_succeeds_without_debit:
  assumes "boundary_records s (binding_key b)=None" "boundary_valid_binding b"
  shows "boundary_fence b s=
      (boundary_record_fence b s,Boundary_Acknowledged (Boundary_No_Effect_Witness b)) \<and>
    boundary_units (fst (boundary_fence b s))=boundary_units s \<and>
    boundary_effects (fst (boundary_fence b s))=boundary_effects s"
  using assms by (simp add: boundary_fence_def boundary_record_fence_def)

theorem boundary_successful_reply_has_exact_evidence:
  assumes "snd (boundary_step command s)=Boundary_Acknowledged evidence"
  shows "\<exists>b. boundary_evidence_matches b evidence (fst (boundary_step command s))"
  using assms
  by (cases command)
     (auto simp: boundary_apply_def boundary_fence_def boundary_record_effect_def
       boundary_record_fence_def boundary_evidence_exact boundary_has_effect_def
       boundary_has_no_effect_def boundary_evidence_def
       split: option.splits source_boundary_record.splits if_splits)

section \<open>Lost Commands, Lost Replies and Lost Local Records\<close>

record source_boundary_machine =
  boundary_endpoint :: source_boundary_state
  boundary_local_commands :: "source_boundary_command list"
  boundary_local_replies :: "source_boundary_reply list"

definition initial_boundary_machine :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  source_boundary_machine" where
  "initial_boundary_machine balances =
    \<lparr>boundary_endpoint=initial_source_boundary balances,
      boundary_local_commands=[],boundary_local_replies=[]\<rparr>"

definition boundary_exchange :: "bool \<Rightarrow> bool \<Rightarrow> source_boundary_command \<Rightarrow>
  source_boundary_machine \<Rightarrow> source_boundary_machine" where
  "boundary_exchange request_arrives reply_arrives command m =
    (let result=(if request_arrives then boundary_step command (boundary_endpoint m)
                 else (boundary_endpoint m,Boundary_Unknown))
     in m\<lparr>boundary_endpoint:=fst result,
       boundary_local_commands:=boundary_local_commands m@[command],
       boundary_local_replies:=boundary_local_replies m@
         (if reply_arrives then [snd result] else [])\<rparr>)"

definition lose_boundary_local_records :: "source_boundary_machine \<Rightarrow> source_boundary_machine"
  where
  "lose_boundary_local_records m =
    m\<lparr>boundary_local_commands:=[],boundary_local_replies:=[]\<rparr>"

definition boundary_local_view :: "source_boundary_machine \<Rightarrow>
  source_boundary_command list \<times> source_boundary_reply list" where
  "boundary_local_view m=(boundary_local_commands m,boundary_local_replies m)"

theorem boundary_local_loss_preserves_authoritative_state:
  "boundary_endpoint (lose_boundary_local_records m)=boundary_endpoint m"
  by (simp add: lose_boundary_local_records_def)

theorem boundary_reply_loss_preserves_authoritative_execution:
  "boundary_endpoint (boundary_exchange arrived False command m)=
    boundary_endpoint (boundary_exchange arrived True command m)"
  by (simp add: boundary_exchange_def Let_def)

theorem boundary_retry_after_local_loss_does_not_repeat_effect:
  assumes "boundary_has_effect b (boundary_endpoint m)"
  shows "boundary_endpoint
    (boundary_exchange True reply_arrives (Boundary_Apply b) (lose_boundary_local_records m))=
    boundary_endpoint m"
  using boundary_effect_retry_changes_nothing[OF assms]
  by (simp add: boundary_exchange_def lose_boundary_local_records_def Let_def)

theorem boundary_query_recovers_effect_witness:
  assumes "boundary_has_effect b (boundary_endpoint m)"
  shows "boundary_local_replies
    (boundary_exchange True True (Boundary_Query b) (lose_boundary_local_records m))=
    [Boundary_Acknowledged (Boundary_Effect_Witness b)]"
  using assms
  by (simp add: boundary_has_effect_def boundary_exchange_def
    lose_boundary_local_records_def boundary_evidence_def Let_def)

theorem boundary_exchange_preserves_endpoint_contract:
  assumes "boundary_history_consistent (boundary_endpoint m)"
    "boundary_allocation balances (boundary_endpoint m)"
  shows "boundary_history_consistent (boundary_endpoint
      (boundary_exchange arrived replied command m)) \<and>
    boundary_allocation balances (boundary_endpoint
      (boundary_exchange arrived replied command m))"
  using assms
  by (auto simp: boundary_exchange_def Let_def
    intro: boundary_step_preserves_history boundary_step_preserves_allocation)

section \<open>The Limit of Local Absence\<close>

definition boundary_silent_attempt :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  transfer_binding \<Rightarrow> bool \<Rightarrow> source_boundary_machine" where
  "boundary_silent_attempt balances b arrived =
    boundary_exchange arrived False (Boundary_Apply b) (initial_boundary_machine balances)"

theorem boundary_silent_attempts_have_identical_local_view:
  "boundary_local_view (boundary_silent_attempt balances b True)=
    boundary_local_view (boundary_silent_attempt balances b False)"
  by (simp add: boundary_local_view_def boundary_silent_attempt_def
    boundary_exchange_def initial_boundary_machine_def Let_def)

theorem boundary_silent_arrival_has_effect:
  assumes "boundary_valid_binding b" "binding_amount b\<le>balances (source_account_of b)"
  shows "boundary_has_effect b (boundary_endpoint (boundary_silent_attempt balances b True))"
  using assms
  by (simp add: boundary_silent_attempt_def boundary_exchange_def initial_boundary_machine_def
    initial_source_boundary_def boundary_apply_def boundary_record_effect_def
    boundary_has_effect_def Let_def)

theorem boundary_silent_nonarrival_has_no_record:
  "boundary_records (boundary_endpoint (boundary_silent_attempt balances b False)) (binding_key b)=None"
  by (simp add: boundary_silent_attempt_def boundary_exchange_def initial_boundary_machine_def
    initial_source_boundary_def Let_def)

theorem boundary_local_absence_is_not_non_effect_evidence:
  "boundary_local_replies (boundary_silent_attempt balances b False)=[] \<and>
    boundary_evidence b (boundary_endpoint (boundary_silent_attempt balances b False))=None"
  by (simp add: boundary_silent_attempt_def boundary_exchange_def initial_boundary_machine_def
    initial_source_boundary_def boundary_evidence_def Let_def)

theorem boundary_no_local_classifier_of_remote_effect:
  assumes valid: "boundary_valid_binding b"
    and funded: "binding_amount b\<le>balances (source_account_of b)"
  shows "\<not>(\<exists>classify. \<forall>arrived.
    classify (boundary_local_view (boundary_silent_attempt balances b arrived))=
    boundary_has_effect b (boundary_endpoint (boundary_silent_attempt balances b arrived)))"
proof -
  have yes: "boundary_has_effect b
    (boundary_endpoint (boundary_silent_attempt balances b True))"
    by (rule boundary_silent_arrival_has_effect[where balances=balances and b=b])
       (rule valid, rule funded)
  have no: "\<not>boundary_has_effect b
    (boundary_endpoint (boundary_silent_attempt balances b False))"
    using boundary_silent_nonarrival_has_no_record[of balances b]
    by (simp add: boundary_has_effect_def)
  show ?thesis
    using yes no boundary_silent_attempts_have_identical_local_view[of balances b] by metis
qed

theorem boundary_timeout_refund_cannot_use_only_local_absence:
  assumes valid: "boundary_valid_binding b"
    and funded: "binding_amount b\<le>balances (source_account_of b)"
    and refunds: "refund (boundary_local_view (boundary_silent_attempt balances b False))"
  shows "refund (boundary_local_view (boundary_silent_attempt balances b True)) \<and>
    boundary_has_effect b (boundary_endpoint (boundary_silent_attempt balances b True))"
proof -
  have effect: "boundary_has_effect b
    (boundary_endpoint (boundary_silent_attempt balances b True))"
    by (rule boundary_silent_arrival_has_effect[where balances=balances and b=b])
       (rule valid, rule funded)
  show ?thesis using refunds effect
    boundary_silent_attempts_have_identical_local_view[of balances b] by simp
qed

section \<open>Concrete Branch Witnesses\<close>

definition boundary_sample_binding :: transfer_binding where
  "boundary_sample_binding =
    \<lparr>binding_key=(0,1),binding_asset=2,binding_amount=3,binding_destination=4,
      binding_recipient=5,binding_source_epoch=6,binding_operation=Destination_Credit,
      binding_separator=7\<rparr>"

lemma boundary_sample_is_valid: "boundary_valid_binding boundary_sample_binding"
  by (simp add: boundary_valid_binding_def boundary_sample_binding_def)

theorem boundary_effect_branch_is_inhabited:
  "snd (boundary_apply boundary_sample_binding (initial_source_boundary (\<lambda>_.5)))=
    Boundary_Acknowledged (Boundary_Effect_Witness boundary_sample_binding)"
  by (simp add: boundary_apply_def initial_source_boundary_def
    boundary_valid_binding_def boundary_sample_binding_def)

theorem boundary_fence_branch_is_inhabited:
  "snd (boundary_fence boundary_sample_binding (initial_source_boundary (\<lambda>_.5)))=
    Boundary_Acknowledged (Boundary_No_Effect_Witness boundary_sample_binding)"
  by (simp add: boundary_fence_def initial_source_boundary_def boundary_sample_is_valid)

theorem boundary_fence_after_effect_is_rejected:
  "snd (boundary_fence boundary_sample_binding
    (fst (boundary_apply boundary_sample_binding (initial_source_boundary (\<lambda>_.5)))))=
    Boundary_Rejected"
  by (simp add: boundary_fence_def boundary_apply_def initial_source_boundary_def
    boundary_record_effect_def boundary_valid_binding_def boundary_sample_binding_def)

theorem boundary_late_effect_after_fence_is_rejected:
  "snd (boundary_apply boundary_sample_binding
    (fst (boundary_fence boundary_sample_binding (initial_source_boundary (\<lambda>_.5)))))=
    Boundary_Rejected"
  by (simp add: boundary_fence_def boundary_apply_def initial_source_boundary_def
    boundary_record_fence_def boundary_sample_is_valid)

theorem boundary_different_amount_for_same_key_is_rejected:
  "snd (boundary_apply (boundary_sample_binding\<lparr>binding_amount:=4\<rparr>)
    (fst (boundary_apply boundary_sample_binding (initial_source_boundary (\<lambda>_.5)))))=
    Boundary_Rejected"
  by (simp add: boundary_apply_def initial_source_boundary_def boundary_record_effect_def
    boundary_valid_binding_def boundary_sample_binding_def)

theorem boundary_local_loss_retry_keeps_one_effect:
  "boundary_effects (boundary_endpoint (boundary_exchange True True
      (Boundary_Apply boundary_sample_binding)
      (lose_boundary_local_records
        (boundary_silent_attempt (\<lambda>_.5) boundary_sample_binding True))))=
    [boundary_sample_binding]"
  by (simp add: boundary_exchange_def lose_boundary_local_records_def
    boundary_silent_attempt_def initial_boundary_machine_def initial_source_boundary_def
    boundary_apply_def boundary_record_effect_def boundary_valid_binding_def
    boundary_sample_binding_def Let_def)

theorem boundary_local_ambiguity_is_inhabited:
  "\<not>(\<exists>classify. \<forall>arrived.
    classify (boundary_local_view (boundary_silent_attempt (\<lambda>_.5) boundary_sample_binding arrived))=
    boundary_has_effect boundary_sample_binding
      (boundary_endpoint (boundary_silent_attempt (\<lambda>_.5) boundary_sample_binding arrived)))"
  by (rule boundary_no_local_classifier_of_remote_effect)
     (simp_all add: boundary_valid_binding_def boundary_sample_binding_def)

text \<open>The indistinguishable executions have the same attempted command
  and no delivered reply. In one, the source has already executed the effect;
  in the other, the command has not arrived. Absence in the latter execution
  is not a fence and cannot rule out a delayed command. A timeout adds no
  authenticated source information. When an authoritative query or fence
  cannot be obtained, recovery must retain the unknown outcome.

  A consumer must check boundary_evidence_matches against the authoritative
  endpoint state, or refine that check to an authenticated source API. An
  arbitrary value of source_boundary_evidence is not trusted merely because
  it has that datatype. Effect evidence supplies source provenance; finality
  authentication and the later terminal decision remain separate checks.

  Safety ranges over arbitrary finite command lists and unbounded keys,
  accounts and amounts. No delivery, fairness or eventual termination claim
  follows from these results. Physical persistence of boundary_records,
  boundary_units and boundary_effects in one effect boundary remains a source
  adapter obligation; losing these authoritative records is not modeled as
  merely losing local acknowledgments.\<close>

end
