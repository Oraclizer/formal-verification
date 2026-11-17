theory Scoped_Source_Finality
  imports REOS_Rollback_Examples.Rollback_Examples
begin

record source_binding =
  source_deployment :: nat
  source_domain :: nat
  source_reference :: nat
  source_transition :: nat
  source_cut :: nat
  source_authority :: nat
  source_footprint :: "ledger_cell set"

datatype verified_source =
    Unavailable
  | Verified_Finality source_binding terminal_record
  | Verified_Abort source_binding

text \<open>The verifier supplies the authenticated binding and exact record.
  The expected and current cuts refer to the same authoritative rollback
  transaction. The source reader must establish those facts separately.\<close>

definition at_commit ::
  "rollback_state \<Rightarrow> source_binding \<Rightarrow> source_binding \<Rightarrow> source_binding \<Rightarrow> bool"
where
  "at_commit s expected current supplied =
    (current = expected \<and> supplied = expected \<and> source_authority expected = authority_epoch s)"

definition commit_internal ::
  "rollback_state \<Rightarrow> (rollback_result \<times> rollback_state) \<Rightarrow> rollback_result \<times> rollback_state"
where
  "commit_internal s rt = (case rt of (Internal e, t) \<Rightarrow> (Internal e, t) | (r, _) \<Rightarrow> (r, s))"

definition agrees_with_known_finality :: "rollback_state \<Rightarrow> nat \<Rightarrow> terminal_record \<Rightarrow> bool" where
  "agrees_with_known_finality s i p \<longleftrightarrow>
    ((finality_receipts s i = None \<or> finality_receipts s i = Some p)
      \<and> (\<forall>j q. finality_receipts s j = Some q \<longrightarrow>
        (\<forall>c \<in> terminal_cells p \<inter> terminal_cells q. terminal_value p c = terminal_value q c)))"

fun import_verified ::
  "rollback_state \<Rightarrow> source_binding \<Rightarrow> source_binding \<Rightarrow>
    verified_source \<Rightarrow> rollback_result \<times> rollback_state"
where
  "import_verified s expected current Unavailable = (Rejected No_Primary_Record, s)"
| "import_verified s expected current (Verified_Finality supplied p) =
    (if at_commit s expected current supplied \<and> terminal_cells p = source_footprint expected
        \<and> agrees_with_known_finality s (source_transition expected) p
     then let i = source_transition expected in
       commit_internal s (execute (s\<lparr>finality_receipts := (finality_receipts s)(i \<mapsto> p)\<rparr>)
          (Record_Finality i))
     else (Rejected Invalid_Context, s))"
| "import_verified s expected current (Verified_Abort supplied) =
    (if at_commit s expected current supplied
        \<and> (\<exists>h. journal s (source_transition expected) = Some h \<and> entry_cells h = source_footprint expected)
     then let i = source_transition expected in
       commit_internal s (execute (s\<lparr>abort_receipts := insert i (abort_receipts s)\<rparr>)
          (Record_Abort i))
     else (Rejected Invalid_Context, s))"

lemma missing_evidence_leaves_ledger_and_journal_intact:
  "import_verified s expected current Unavailable = (Rejected No_Primary_Record, s)"
  by simp

lemma a_valid_old_lookup_cannot_commit_against_a_different_cut:
  assumes "current \<noteq> expected"
  shows "import_verified s expected current (Verified_Finality expected p) = (Rejected Invalid_Context, s)"
    and "import_verified s expected current (Verified_Abort expected) = (Rejected Invalid_Context, s)"
  using assms by (simp_all add: at_commit_def)

lemma a_different_reference_or_scope_cannot_install_finality:
  assumes "supplied \<noteq> expected \<or> terminal_cells p \<noteq> source_footprint expected"
  shows "import_verified s expected current (Verified_Finality supplied p) = (Rejected Invalid_Context, s)"
  using assms by (auto simp: at_commit_def)

lemma rejected_adaptation_does_not_cache_a_receipt_or_abort:
  assumes "fst (import_verified s expected current reply) = Rejected why"
  shows "snd (import_verified s expected current reply) = s"
  using assms
  by (cases reply) (auto simp: commit_internal_def Let_def split: prod.splits transition_result.splits)

lemma a_partial_abort_cannot_release_the_whole_entry:
  assumes "\<not> (\<exists>h. journal s (source_transition expected) = Some h
    \<and> entry_cells h = source_footprint expected)"
  shows "import_verified s expected current (Verified_Abort supplied) = (Rejected Invalid_Context, s)"
  using assms by (auto split: if_splits)

lemma known_conflicting_finality_cannot_be_overwritten:
  assumes "finality_receipts s (source_transition expected) = Some q" "q \<noteq> p"
  shows "import_verified s expected current (Verified_Finality supplied p) = (Rejected Invalid_Context, s)"
  using assms by (simp add: agrees_with_known_finality_def)

abbreviation other_resource :: ledger_cell where
  "other_resource \<equiv> Cell 1 2 4 Billing"

definition expected_lookup :: source_binding where
  "expected_lookup = \<lparr>source_deployment = 7, source_domain = 0, source_reference = 2,
     source_transition = 77, source_cut = 31, source_authority = 4,
     source_footprint = {terminal}\<rparr>"

definition pending_ledger :: rollback_state where
  "pending_ledger = fixture\<lparr>journal := (journal fixture)
      (77 \<mapsto> in_flight_entry\<lparr>entry_cells := {terminal, other_resource}\<rparr>),
     finality_receipts := (\<lambda>_. None)\<rparr>"

definition scoped_finality :: rollback_state where
  "scoped_finality =
    snd (import_verified pending_ledger expected_lookup expected_lookup
      (Verified_Finality expected_lookup receipt))"

lemma installation_uses_the_certified_value_and_keeps_the_peer:
  "import_verified pending_ledger expected_lookup expected_lookup
      (Verified_Finality expected_lookup receipt)
    = (Internal (Recorded_Finality 77), scoped_finality)"
  "cell_value pending_ledger terminal = 9"
  "cell_value scoped_finality terminal = 13"
  "cell_value scoped_finality other_resource = 9"
  "rollback_step scoped_finality (Execute_Rollback terminal_intent None None)
    (Rejected Terminal_Effect) scoped_finality"
  by (simp_all add: expected_lookup_def pending_ledger_def scoped_finality_def
      fixture_setup decision_rules commit_internal_def at_commit_def agrees_with_known_finality_def)

lemma another_resource_at_the_same_transaction_cannot_supply_the_lookup:
  "import_verified pending_ledger expected_lookup expected_lookup
    (Verified_Finality expected_lookup (receipt\<lparr>terminal_cells := {other_resource}\<rparr>))
     = (Rejected Invalid_Context, pending_ledger)"
  by (simp add: expected_lookup_def receipt_def pending_ledger_def
      fixture_setup decision_rules commit_internal_def at_commit_def agrees_with_known_finality_def)

definition expected_abort :: source_binding where
  "expected_abort = expected_lookup\<lparr>source_footprint := {terminal, other_resource}\<rparr>"

definition stamped_abort :: rollback_state where
  "stamped_abort = snd (import_verified pending_ledger expected_abort expected_abort
    (Verified_Abort expected_abort))"

lemma compensation_requires_affirmative_abort_at_the_bound_cut:
  "rollback_step pending_ledger (Execute_Rollback terminal_intent None None)
    (Rejected Pending_Effect) pending_ledger"
  "import_verified pending_ledger expected_lookup expected_lookup
    (Verified_Abort expected_lookup) = (Rejected Invalid_Context, pending_ledger)"
  "import_verified pending_ledger expected_abort expected_abort
    (Verified_Abort expected_abort) = (Internal (Recorded_Abort 77), stamped_abort)"
  "\<exists>t. rollback_step stamped_abort (Execute_Rollback terminal_intent None None) (Accepted 11) t
     \<and> cell_value t terminal = 2 \<and> cell_value t other_resource = 9"
  "import_verified scoped_finality expected_abort expected_abort
    (Verified_Abort expected_abort) = (Rejected Invalid_Context, scoped_finality)"
  by (simp_all add: expected_lookup_def pending_ledger_def scoped_finality_def stamped_abort_def
      expected_abort_def fixture_setup decision_rules commit_internal_def at_commit_def agrees_with_known_finality_def)

end
