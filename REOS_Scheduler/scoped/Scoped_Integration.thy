theory Scoped_Integration
  imports Scoped_Budgets Scoped_Controls
    Scoped_Receipt_Trace Scoped_Rotation Scoped_Starvation Scoped_Necessity
begin

theorem certified_finality_and_request_completion_share_one_scoped_trace:
  assumes installed: "run_machine E d (Import_At expected binding) =
      (Imported_Record (Internal (Recorded_Finality i)),after_import)"
    and trace: "finite_trace (machine_step E) carrier after_import events final_state"
    and finite: "finite K"
    and policy: "\<And>e. e \<in> set events \<Longrightarrow> budgeted_priority K e"
    and coherent: "coherent_ordinary_queue (scheduler_at after_import)"
    and pending: "p \<in> set (ordinary_queue (scheduler_at after_import))"
    and enough: "earlier_ordinary (packet_identity p) (scheduler_at after_import) + case_credits K after_import
      < length (filter used_service_slot events)"
  obtains primary e turn where
    "source_at_cut E (store_cut expected) binding = (binding, Verified_Finality binding primary)"
    "terminal_cells primary = source_footprint binding"
    "terminal_records (rollback_context (scheduler_at final_state)) i = Some primary"
    "\<forall>c \<in> terminal_cells primary. cell_value (rollback_context (scheduler_at final_state)) c = terminal_value primary c"
    "e \<in> set events" "ordinary_commit_id (step_outcome e) = Some (packet_identity p)"
    "ordinary_receipts (scheduler_at (target_state e)) (packet_identity p) = Some p"
    "step_action e = Attempt_At (committed_cut (source_state e)) turn p"
    "(turn,p) \<in> certified_order_pairs E"
    "run_machine E (target_state e) (Attempt_At retry_cut turn p) =
      (Observed_Service (Replayed_Receipt p),target_state e)"
proof -
  obtain primary where
    cert: "source_at_cut E (store_cut expected) binding = (binding, Verified_Finality binding primary)"
    and scope: "terminal_cells primary = source_footprint binding"
    and initial_record: "terminal_records (rollback_context (scheduler_at after_import)) i = Some primary"
    and initial_cells: "\<forall>c \<in> terminal_cells primary.
      cell_value (rollback_context (scheduler_at after_import)) c = terminal_value primary c"
    by (rule import_at_the_current_cut_uses_the_certified_primary_cells[OF installed]) (rule that; assumption)
  from imported_finality_remains_in_the_same_service_trace[OF initial_record trace] initial_cells
  have stable: "terminal_records (rollback_context (scheduler_at final_state)) i = Some primary"
    "\<forall>c \<in> terminal_cells primary. cell_value (rollback_context (scheduler_at final_state)) c = terminal_value primary c"
    by auto
  from registered_case_budget_is_consumed_by_exact_request_progress[OF finite trace policy coherent pending enough]
  obtain e where observed: "e \<in> set events" "ordinary_commit_id (step_outcome e) = Some (packet_identity p)"
    "ordinary_receipts (scheduler_at (target_state e)) (packet_identity p) = Some p"
    by blast
  from each_event_in_a_machine_trace_occurs[OF trace observed(1)] have step: "step_occurs (machine_step E) e" .
  obtain turn where called: "step_action e = Attempt_At (committed_cut (source_state e)) turn p"
    "(turn,p) \<in> certified_order_pairs E"
    "run_machine E (target_state e) (Attempt_At retry_cut turn p) =
      (Observed_Service (Replayed_Receipt p),target_state e)"
    by (rule a_committed_ordinary_receipt_names_the_certified_order_in_that_step[OF step observed(2,3)])
      (rule that; assumption)
  show thesis by (rule that[OF cert scope stable observed called])
qed

corollary exceeding_initial_credit_exhibits_a_priority_step_outside_the_budgeted_regime:
  assumes "finite K" "finite_trace (machine_step E) carrier d events t"
    "case_credits K d < length (filter used_priority_slot events)"
  shows "\<exists>e \<in> set events. used_priority_slot e \<and> \<not> budgeted_priority K e"
proof (rule ccontr)
  assume no_exempt: "\<not> (\<exists>e\<in>set events. used_priority_slot e \<and> \<not> budgeted_priority K e)"
  then have rule: "\<And>e. e \<in> set events \<Longrightarrow> budgeted_priority K e"
    by (auto simp: budgeted_priority_def)
  from fixed_case_capacity_bounds_scoped_raises_and_rollbacks[OF assms(1,2) rule] assms(3) show False
    by linarith
qed

end
