theory Scoped_Level_Boundaries
  imports Scoped_Dispatch Fresh_Case_Interference
begin

lemma level_only_queued_work_keeps_the_raw_priority_choice:
  assumes "\<And>p. p \<in> set (regulatory_queue s) \<Longrightarrow>
    (\<exists>k level. packet_contents p = Raise_Level k level \<or> packet_contents p = Lower_Level k level)"
  shows "authorized_view inputs s = s"
proof -
  have "\<And>p. p \<in> set (regulatory_queue s) \<Longrightarrow>
    policy_allows inputs (rollback_context s) (packet_contents p)"
  proof -
    fix p assume "p \<in> set (regulatory_queue s)"
    from assms[OF this] show "policy_allows inputs (rollback_context s) (packet_contents p)" by auto
  qed
  then show ?thesis by (simp add: authorized_view_def filter_id_conv)
qed

lemma real_level_step_is_reproduced_by_a_current_exact_signed_order:
  assumes raw: "scheduler_step s Honest_Service (Internal (Served_Regulation q k)) t"
    and permitted: "authorized_view inputs s = s"
    and signed: "(turn,p) \<in> verified" "qualified_turn signer {turn} s turn"
    and sole: "regulatory_queue s = [p]"
  shows "scoped_service inputs signer verified s turn p = (Internal (Served_Regulation q k),t)"
proof -
  obtain selected u where choose: "next_regulation s = Some selected"
    and member: "selected \<in> set (regulatory_queue s)"
    and post: "t = u\<lparr>regulatory_queue := remove1 selected (regulatory_queue s),
      regulation_receipts := (regulation_receipts s)(q \<mapsto> selected)\<rparr>"
    by (rule honest_service_uses_selected_regulation[OF raw]) (rule that; assumption)
  from member sole have selected: "selected = p" by simp
  from choose selected have plan: "planned s = Some p" by (simp add: planned_def)
  from raw have result: "schedule s = (Internal (Served_Regulation q k), t)" by (simp add: scheduler_step_def)
  from post selected have "t\<lparr>regulatory_queue := remove1 p (regulatory_queue s)\<rparr> = t" by simp
  with result permitted signed plan show ?thesis by (simp add: scoped_service_def Let_def)
qed

lemma every_strict_fresh_case_of_the_starvation_trace_is_still_executable:
  assumes signed: "(turn,fresh_packet n) \<in> verified"
    "qualified_turn signer {turn} (fresh_pending n) turn"
  shows "scoped_submit inputs (fresh_state n) (fresh_packet n) = (Accepted (102+n),fresh_pending n)"
    "scoped_service inputs signer verified (fresh_pending n) turn (fresh_packet n) =
      (Internal (Served_Regulation (102+n) (9+n)),fresh_state (Suc n))"
proof -
  from fresh_case_submitted[of n] show
    "scoped_submit inputs (fresh_state n) (fresh_packet n) = (Accepted (102+n),fresh_pending n)"
    by (simp add: scoped_submit_def scheduler_step_def fresh_packet_def)
  have one: "regulatory_queue (fresh_pending n) = [fresh_packet n]"
    by (simp add: fresh_pending_def fresh_state_def fresh_initial_def enqueue_packet_def fresh_packet_def packet_example)
  from one have "authorized_view inputs (fresh_pending n) = fresh_pending n"
    by (intro level_only_queued_work_keeps_the_raw_priority_choice) (simp add: fresh_packet_def)
  from real_level_step_is_reproduced_by_a_current_exact_signed_order[OF fresh_case_actually_served this signed one]
  show "scoped_service inputs signer verified (fresh_pending n) turn (fresh_packet n) =
      (Internal (Served_Regulation (102+n) (9+n)),fresh_state (Suc n))" .
qed

lemma each_raise_or_lower_in_the_fixed_case_lasso_can_commit_in_scope:
  assumes signed: "(turn,cycle_packet n) \<in> verified"
    "qualified_turn signer {turn} (cycle_queued n) turn"
  shows "scoped_service inputs signer verified (cycle_queued n) turn (cycle_packet n) =
      (Internal (Served_Regulation (102+n) 9),cycle_state (Suc n))"
proof -
  have one: "regulatory_queue (cycle_queued n) = [cycle_packet n]"
    by (cases "even n")
      (simp_all add: cycle_queued_def cycle_state_def enqueue_packet_def cycle_packet_def packet_example)
  from one have "authorized_view inputs (cycle_queued n) = cycle_queued n"
    by (intro level_only_queued_work_keeps_the_raw_priority_choice) (auto simp: cycle_packet_def)
  from real_level_step_is_reproduced_by_a_current_exact_signed_order[OF cycle_consumes_actual_priority_packet this signed one]
  show ?thesis .
qed

end
