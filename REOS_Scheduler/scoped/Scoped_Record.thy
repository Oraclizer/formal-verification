theory Scoped_Record
  imports Scoped_Machine
begin

lemma staged_commit_keeps_the_installed_terminal_effect:
  assumes native: "commit_internal s (execute u action) = (reply,t)"
    and frame: "terminal_records u = terminal_records s" "cell_value u = cell_value s"
    and prior: "terminal_records s j = Some p"
  shows "terminal_records t j = Some p \<and>
    (\<forall>c \<in> terminal_cells p. cell_value t c = cell_value s c)"
proof -
  obtain x v where invoked: "execute u action = (x,v)" by (cases "execute u action") blast
  from native invoked have finished: "t = s \<or> rollback_step u action reply t"
    by (cases x) (auto simp: commit_internal_def rollback_step_def)
  from prior frame(1) have known: "terminal_records u j = Some p" by simp
  from finished show ?thesis
  proof
    assume "t = s"
    with prior show ?thesis by simp
  next
    assume "rollback_step u action reply t"
    from immutable_terminal_effect[OF this known] frame(2) show ?thesis by simp
  qed
qed

lemma verified_import_keeps_the_installed_terminal_effect:
  assumes prior: "terminal_records s j = Some p"
    and result: "import_verified s expected current evidence = (reply,t)"
  shows "terminal_records t j = Some p \<and>
    (\<forall>c \<in> terminal_cells p. cell_value t c = cell_value s c)"
proof (cases "t = s")
  case True
  with prior show ?thesis by simp
next
  case False
  show ?thesis
  proof (cases evidence)
    case Unavailable
    with result False show ?thesis by simp
  next
    case (Verified_Finality supplied p')
    let ?i = "source_transition expected"
    let ?staged = "s\<lparr>finality_receipts := (finality_receipts s)(?i \<mapsto> p')\<rparr>"
    from Verified_Finality result False have
      "commit_internal s (execute ?staged (Record_Finality ?i)) = (reply,t)"
      by (auto simp: Let_def split: if_splits)
    from staged_commit_keeps_the_installed_terminal_effect[OF this _ _ prior] show ?thesis by simp
  next
    case (Verified_Abort supplied)
    let ?i = "source_transition expected"
    let ?staged = "s\<lparr>abort_receipts := insert ?i (abort_receipts s)\<rparr>"
    from Verified_Abort result False have
      "commit_internal s (execute ?staged (Record_Abort ?i)) = (reply,t)"
      by (auto simp: Let_def split: if_splits)
    from staged_commit_keeps_the_installed_terminal_effect[OF this _ _ prior] show ?thesis by simp
  qed
qed

lemma import_at_the_current_cut_uses_the_certified_primary_cells:
  assumes committed: "run_machine E d (Import_At expected binding) =
    (Imported_Record (Internal (Recorded_Finality i)),t)"
  obtains p where
    "expected = committed_cut d"
    "source_at_cut E (store_cut expected) binding = (binding, Verified_Finality binding p)"
    "source_transition binding = i" "terminal_cells p = source_footprint binding"
    "source_authority binding = authority_epoch (rollback_context (scheduler_at d))"
    "finality_receipts (rollback_context (scheduler_at t)) i = Some p"
    "terminal_records (rollback_context (scheduler_at t)) i = Some p"
    "\<forall>c \<in> terminal_cells p. cell_value (rollback_context (scheduler_at t)) c = terminal_value p c"
    "preserves_outside cell_value (terminal_cells p) (rollback_context (scheduler_at d))
       (rollback_context (scheduler_at t))"
proof -
  let ?s = "rollback_context (scheduler_at d)"
  let ?t = "rollback_context (scheduler_at t)"
  from committed obtain current certified where
    cut: "expected = committed_cut d"
    and source: "source_at_cut E (store_cut expected) binding = (current,certified)"
    and imported: "import_verified ?s binding current certified = (Internal (Recorded_Finality i),?t)"
    by (auto split: prod.splits if_splits transition_result.splits)
  from imported obtain p where
    cert: "certified = Verified_Finality binding p" "current = binding"
    and bound: "source_transition binding = i" "terminal_cells p = source_footprint binding"
      "source_authority binding = authority_epoch ?s"
    and added: "?t = ?s\<lparr>finality_receipts := (finality_receipts ?s)(i \<mapsto> p),
         terminal_records := (terminal_records ?s)(i \<mapsto> p),
         cell_value := update_cells (terminal_cells p) (terminal_value p) (cell_value ?s)\<rparr>"
    by (cases certified) (auto simp: at_commit_def commit_internal_def Let_def
      split: prod.splits transition_result.splits option.splits if_splits)
  from cut source cert bound added show thesis
    by (intro that[of p]) (simp_all add: update_cells_def preserves_outside_def)
qed

lemma current_replica_repair_reads_the_protected_record:
  assumes "run_machine E d (Repair_At expected i replica) =
    (Repaired_Replica (Internal (Repaired_From_Record i replica)),t)"
  obtains p where
    "expected = committed_cut d"
    "terminal_records (rollback_context (scheduler_at d)) i = Some p"
    "terminal_records (rollback_context (scheduler_at t)) i = Some p"
    "\<forall>c \<in> terminal_cells p. replica_value (rollback_context (scheduler_at t)) replica c = terminal_value p c"
    "preserves_outside (\<lambda>x. replica_value x replica) (terminal_cells p)
      (rollback_context (scheduler_at d)) (rollback_context (scheduler_at t))"
    "cell_value (rollback_context (scheduler_at t)) = cell_value (rollback_context (scheduler_at d))"
proof -
  let ?s = "rollback_context (scheduler_at d)"
  let ?t = "rollback_context (scheduler_at t)"
  from assms have cut: "expected = committed_cut d"
    and repair: "rollback_step ?s (Repair_From_Record i replica)
          (Internal (Repaired_From_Record i replica)) ?t"
    by (auto simp: rollback_step_def split: prod.splits if_splits transition_result.splits)
  from finality_repair_matches_record[OF repair] obtain p where
    "terminal_records ?s i = Some p"
    "\<forall>c \<in> terminal_cells p. replica_value ?t replica c = terminal_value p c"
    "preserves_outside (\<lambda>x. replica_value x replica) (terminal_cells p) ?s ?t"
    "cell_value ?t = cell_value ?s" "terminal_records ?t = terminal_records ?s" .
  with cut show thesis by (intro that[of p]) simp_all
qed

lemma level_service_does_not_write_ledger_cells:
  assumes "scoped_service inputs signer verified s turn p = (Internal (Served_Regulation q k),t)"
    and "\<And>r a pf. packet_contents p \<noteq> Execute_Governed_Rollback r a pf"
  shows "rollback_context t = rollback_context s"
proof -
  from scoped_regulatory_effect[OF assms(1)] obtain u where
    effect: "regulatory_effect (authorized_view inputs s) p = Some u"
    and update: "t = u\<lparr>regulatory_queue := remove1 p (regulatory_queue s),
          regulation_receipts := (regulation_receipts (authorized_view inputs s))(q \<mapsto> p)\<rparr>"
    by blast
  from assms(2) effect update show ?thesis
    by (cases "packet_contents p")
      (auto simp: regulatory_effect_def authorized_view_def split: if_splits)
qed

lemma service_cannot_change_finality:
  assumes obs: "observe_sequence I signer orders retained expected current turn p = (answer,t)"
    and wrote: "committed_service answer"
    and installed: "terminal_records (rollback_context (observed_scheduler current)) i = Some prior"
  shows "terminal_records (rollback_context t) i = Some prior \<and>
    (\<forall>c \<in> terminal_cells prior. cell_value (rollback_context t) c =
       cell_value (rollback_context (observed_scheduler current)) c)"
proof -
  from wrote have actual:
    "(\<exists>q. answer = Compared_Attempt (Service_Result (Internal (Served_Ordinary q)))) \<or>
      (\<exists>q k. answer = Compared_Attempt (Service_Result (Internal (Served_Regulation q k))))"
    by (simp add: committed_service_replies)
  then show ?thesis
  proof
    assume "\<exists>q. answer = Compared_Attempt (Service_Result (Internal (Served_Ordinary q)))"
    with obs obtain q where
      "observe_sequence I signer orders retained expected current turn p =
         (Compared_Attempt (Service_Result (Internal (Served_Ordinary q))),t)" by blast
    from compare_commit_uses_the_exact_current_order(4)[OF this] obtain rest where
      "t = (observed_scheduler current)\<lparr>ordinary_queue := rest,
        ordinary_receipts := (ordinary_receipts (observed_scheduler current))(q \<mapsto> p)\<rparr>"
      by (elim scoped_ordinary_effect) blast
    with installed show ?thesis by simp
  next
    assume "\<exists>q k. answer = Compared_Attempt (Service_Result (Internal (Served_Regulation q k)))"
    with obs obtain q k where commit: "observe_sequence I signer orders retained expected current turn p =
      (Compared_Attempt (Service_Result (Internal (Served_Regulation q k))),t)" by blast
    show ?thesis
    proof (cases "\<exists>r a pf. packet_contents p = Execute_Governed_Rollback r a pf")
      case True
      then obtain r a pf where "packet_contents p = Execute_Governed_Rollback r a pf" by blast
      from committed_rollback_consumes_authority_frame_and_budget(6)[OF commit this installed]
      show ?thesis .
    next
      case False
      with level_service_does_not_write_ledger_cells[OF compare_commit_uses_the_exact_current_order(4)[OF commit]] installed
      show ?thesis by fastforce
    qed
  qed
qed

lemma one_scoped_step_preserves_an_installed_terminal_record:
  assumes step: "machine_step E d action reply t"
    and known: "terminal_records (rollback_context (scheduler_at d)) i = Some prior"
  shows "terminal_records (rollback_context (scheduler_at t)) i = Some prior \<and>
    (\<forall>c \<in> terminal_cells prior. cell_value (rollback_context (scheduler_at t)) c =
       cell_value (rollback_context (scheduler_at d)) c)"
  using step known
proof (cases action)
  case (Attempt_At expected turn p)
  from step Attempt_At obtain obs where reply: "reply = Observed_Service obs"
    by (auto simp: machine_step_def split: prod.splits if_splits)
  from step Attempt_At reply have actual:
    "machine_step E d (Attempt_At expected turn p) (Observed_Service obs) t" by simp
  show ?thesis
  proof (cases "committed_service obs")
    case True
    from service_cannot_change_finality[OF service_trace_consumes_checked_compare(1)[OF actual True] True known]
    show ?thesis .
  next
    case False
    then have "t = d" by (rule service_attempt_without_a_commit_is_a_read[OF actual])
    with known show ?thesis by simp
  qed
next
  case (Receive_Packet p)
  with step known show ?thesis
    by (auto simp: machine_step_def scoped_submit_def admit_def enqueue_packet_def Let_def
      split: prod.splits transition_result.splits if_splits)
next
  case (Import_At expected binding)
  with step known show ?thesis
    by (auto simp: machine_step_def split: prod.splits transition_result.splits if_splits
      dest: verified_import_keeps_the_installed_terminal_effect)
qed (auto simp: machine_step_def checked_advance_def retire_stale_def Let_def
     split: prod.splits option.splits transition_result.splits if_splits rollback_internal.splits)

theorem imported_finality_remains_in_the_same_service_trace:
  assumes installed: "terminal_records (rollback_context (scheduler_at d)) i = Some prior"
    and trace: "finite_trace (machine_step E) carrier d events t"
  shows "terminal_records (rollback_context (scheduler_at t)) i = Some prior \<and>
    (\<forall>c \<in> terminal_cells prior. cell_value (rollback_context (scheduler_at t)) c =
       cell_value (rollback_context (scheduler_at d)) c)"
  using trace installed
proof (induction events arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  then have actual: "machine_step E d (step_action e) (step_outcome e) (target_state e)"
    and more: "finite_trace (machine_step E) carrier (target_state e) es t"
    by (auto simp: step_occurs_def)
  from one_scoped_step_preserves_an_installed_terminal_record[OF actual Cons.prems(2)] have
    stay: "terminal_records (rollback_context (scheduler_at (target_state e))) i = Some prior"
    and cell: "\<And>c. c \<in> terminal_cells prior \<Longrightarrow>
      cell_value (rollback_context (scheduler_at (target_state e))) c =
        cell_value (rollback_context (scheduler_at d)) c"
    by auto
  from Cons.IH[OF more stay] cell show ?case by auto
qed

end
