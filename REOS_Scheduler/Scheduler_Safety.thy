theory Scheduler_Safety
  imports Open_Scheduler
begin

section \<open>Admission and exact execution evidence\<close>

lemma admitted_packet:
  assumes "scheduler_step s (Submit p) (Accepted q) t"
  shows "q = packet_identity p" "p \<in> signed_packets s"
    "packet_identity p \<notin> dedup_ids s" "packet_fresh s p"
    "ordinary_body (packet_contents p) \<or> ready_regulation s p"
    "t = enqueue_packet s p"
  using assms by (auto simp: scheduler_step_def admit_def split: if_splits)

lemma rejected_submit_keeps_the_state:
  assumes "scheduler_step s (Submit p) (Rejected reason) t"
  shows "t = s"
  using assms by (auto simp: scheduler_step_def admit_def split: if_splits)

theorem rejection_cannot_occupy_a_priority_slot:
  assumes "scheduler_step s (Submit p) (Rejected reason) t"
  shows "priority_slots t = priority_slots s"
    "ordinary_queue t = ordinary_queue s" "regulatory_queue t = regulatory_queue s"
    "dedup_ids t = dedup_ids s" "ordinary_receipts t = ordinary_receipts s"
    "regulation_receipts t = regulation_receipts s"
  using rejected_submit_keeps_the_state[OF assms] by simp_all

theorem failed_signature_leaves_the_id_available:
  assumes "p \<notin> signed_packets s"
  shows "scheduler_step s (Submit p) (Rejected Signature_Failed) s"
  using assms by (simp add: scheduler_step_def admit_def)

lemma regulation_queue_frame:
  assumes "regulatory_effect s p = Some u"
  shows "ordinary_queue u = ordinary_queue s"
    "dedup_ids u = dedup_ids s" "regulatory_queue u = regulatory_queue s"
    "signed_packets u = signed_packets s" "severity_limit u = severity_limit s"
    "ordinary_receipts u = ordinary_receipts s"
proof -
  have "ordinary_queue u = ordinary_queue s \<and> dedup_ids u = dedup_ids s \<and>
      regulatory_queue u = regulatory_queue s \<and> signed_packets u = signed_packets s \<and>
      severity_limit u = severity_limit s \<and> ordinary_receipts u = ordinary_receipts s"
    using assms by (cases "packet_contents p";
      auto simp: regulatory_effect_def split: if_splits prod.splits transition_result.splits)
  then show "ordinary_queue u = ordinary_queue s" "dedup_ids u = dedup_ids s"
    "regulatory_queue u = regulatory_queue s" "signed_packets u = signed_packets s"
    "severity_limit u = severity_limit s" "ordinary_receipts u = ordinary_receipts s" by simp_all
qed

lemma selected_regulation_ready:
  assumes "next_regulation s = Some p"
  shows "ready_regulation s p" "p \<in> set (regulatory_queue s)"
proof -
  let ?ps = "sort_key packet_order (regulatory_queue s)"
  from assms obtain i where index: "i < length ?ps"
    and state: "ready_regulation s (?ps ! i)" and selected: "p = ?ps ! i"
    by (auto simp: next_regulation_def find_Some_iff)
  from state selected show "ready_regulation s p" by simp
  from nth_mem[OF index] selected show "p \<in> set (regulatory_queue s)" by simp
qed

lemma no_regulation_selected_iff_no_priority_slot:
  "next_regulation s = None \<longleftrightarrow> priority_slots s = 0"
  by (auto simp: next_regulation_def priority_slots_def find_None_iff filter_empty_conv)

lemma honest_service_uses_selected_regulation:
  assumes step: "scheduler_step s Honest_Service (Internal (Served_Regulation q k)) t"
  obtains p u where
    "next_regulation s = Some p" "p \<in> set (regulatory_queue s)"
    "q = packet_identity p" "k = regulatory_case (packet_contents p)"
    "regulatory_effect s p = Some u"
    "t = u\<lparr>regulatory_queue := remove1 p (regulatory_queue s),
        regulation_receipts := (regulation_receipts s)(q \<mapsto> p)\<rparr>"
  using step selected_regulation_ready(2)
  by (auto simp: scheduler_step_def schedule_contract serve_ordinary_def
      split: option.splits list.splits if_splits)

theorem a_regulatory_rollback_executes_the_assured_handler:
  assumes step: "scheduler_step s Honest_Service (Internal (Served_Regulation q k)) t"
    and selected: "next_regulation s = Some p"
    and body_is_rollback: "packet_contents p = Execute_Governed_Rollback r a pf"
  shows "q = request_id r"
    and "rollback_step (rollback_context s) (Execute_Rollback r a pf) (Accepted q) (rollback_context t)"
proof -
  from step obtain chosen u where
    choice: "next_regulation s = Some chosen"
    and chosen_id: "q = packet_identity chosen" and chosen_effect: "regulatory_effect s chosen = Some u"
    and chosen_result: "t = u\<lparr>regulatory_queue := remove1 chosen (regulatory_queue s),
        regulation_receipts := (regulation_receipts s)(q \<mapsto> chosen)\<rparr>"
    by (elim honest_service_uses_selected_regulation)
  from choice selected have "chosen = p" by simp
  with chosen_id chosen_effect chosen_result have
    q: "q = packet_identity p" and effect: "regulatory_effect s p = Some u"
    and result: "t = u\<lparr>regulatory_queue := remove1 p (regulatory_queue s),
        regulation_receipts := (regulation_receipts s)(q \<mapsto> p)\<rparr>"
    by simp_all
  from q effect body_is_rollback show "q = request_id r"
    by (auto simp: regulatory_effect_def split: if_splits)
  from effect body_is_rollback obtain txn c where
    native: "Rollback_Model.execute (rollback_context s) (Execute_Rollback r a pf) = (Accepted txn,c)"
    and after_rb: "rollback_context u = c"
    by (auto simp: regulatory_effect_def split: if_splits prod.splits transition_result.splits)
  have rv: "rollback_step (rollback_context s) (Execute_Rollback r a pf) (Accepted txn) c"
    using native by (simp add: rollback_step_def)
  from accepted_rollback[OF rv] have "txn = request_id r" by blast
  with rv after_rb result \<open>q = request_id r\<close> show
    "rollback_step (rollback_context s) (Execute_Rollback r a pf) (Accepted q) (rollback_context t)"
    by simp
qed

theorem ordinary_service_records_the_head_packet:
  assumes "scheduler_step s Honest_Service (Internal (Served_Ordinary q)) t"
  obtains p rest where "ordinary_queue s = p # rest"
    "ordinary_body (packet_contents p)" "q = packet_identity p" "ordinary_queue t = rest"
    "ordinary_receipts t q = Some p" "priority_slots s = 0"
  using assms
  by (auto simp: scheduler_step_def schedule_contract serve_ordinary_def
      no_regulation_selected_iff_no_priority_slot split: option.splits list.splits if_splits)

theorem new_epoch_removes_old_priority_eligibility:
  assumes rotate: "scheduler_step s (Rotate_Context time a k policy) (Internal Snapshot_Changed) t"
    and stale: "packet_authority_epoch p \<noteq> a \<or>
      (regulatory_case (packet_contents p) = k \<and> packet_policy_epoch p \<noteq> policy)"
  shows "\<not> ready_regulation t p" "next_regulation t \<noteq> Some p"
    "ordinary_queue t = ordinary_queue s"
proof -
  from rotate have new_context:
    "authority_epoch (rollback_context t) = a"
    "policy_epoch (rollback_context t) k = policy"
    and frame: "ordinary_queue t = ordinary_queue s"
    by (auto simp: scheduler_step_def split: if_splits)
  from new_context stale show "\<not> ready_regulation t p"
    by (auto simp: ready_regulation_def regulatory_effect_def packet_fresh_def)
  then show "next_regulation t \<noteq> Some p" using selected_regulation_ready(1) by blast
  show "ordinary_queue t = ordinary_queue s" by (rule frame)
qed

section \<open>Ordinary requests across scheduling steps\<close>

lemma ordinary_queue_update:
  assumes step: "scheduler_step s action outcome t"
  obtains
    (same) "ordinary_queue t = ordinary_queue s" "ordinary_receipts t = ordinary_receipts s"
      "dedup_ids s \<subseteq> dedup_ids t"
  | (push) p where "action = Submit p" "ordinary_body (packet_contents p)"
      "outcome = Accepted (packet_identity p)" "packet_identity p \<notin> dedup_ids s"
      "ordinary_queue t = ordinary_queue s @ [p]" "ordinary_receipts t = ordinary_receipts s"
      "dedup_ids t = insert (packet_identity p) (dedup_ids s)"
  | (pop) p ps where "action = Honest_Service" "ordinary_queue s = p # ps"
      "ordinary_queue t = ps" "outcome = Internal (Served_Ordinary (packet_identity p))"
      "ordinary_receipts t = (ordinary_receipts s)(packet_identity p \<mapsto> p)"
      "dedup_ids t = dedup_ids s"
proof (cases action)
  case (Submit p)
  with step have action_step: "scheduler_step s (Submit p) outcome t" by simp
  show ?thesis
  proof (cases outcome)
    case (Accepted q)
    with action_step have success: "scheduler_step s (Submit p) (Accepted q) t" by simp
    from admitted_packet[OF success] have
      ident: "q = packet_identity p" and fresh: "packet_identity p \<notin> dedup_ids s"
      and updated: "t = enqueue_packet s p" by simp_all
    show ?thesis
    proof (cases "ordinary_body (packet_contents p)")
      case True
      from Submit Accepted ident fresh updated True show ?thesis
        by (intro that(2)[of p]) (simp_all add: enqueue_packet_def Let_def)
    next
      case False
      from updated False show ?thesis by (intro that(1)) (auto simp: enqueue_packet_def Let_def)
    qed
  next
    case (Rejected why)
    with action_step have "scheduler_step s (Submit p) (Rejected why) t" by simp
    from rejected_submit_keeps_the_state[OF this] show ?thesis by (intro that(1)) simp_all
  next
    case (Operational_Failure why)
    with action_step show ?thesis by (auto simp: scheduler_step_def admit_def split: if_splits)
  next
    case (Internal eff)
    with action_step show ?thesis by (auto simp: scheduler_step_def admit_def split: if_splits)
  qed
next
  case Honest_Service
  with step have action_step: "scheduler_step s Honest_Service outcome t" by simp
  show ?thesis
  proof (cases "next_regulation s")
    case None
    show ?thesis
    proof (cases "ordinary_queue s")
      case Nil
      with action_step None have "t = s" by (simp add: scheduler_step_def schedule_contract serve_ordinary_def)
      then show ?thesis by (intro that(1)) simp_all
    next
      case (Cons p ps)
      show ?thesis
      proof (cases "ordinary_body (packet_contents p)")
        case True
        from action_step None Cons True have result:
          "t = s\<lparr>ordinary_queue := ps, ordinary_receipts := (ordinary_receipts s)(packet_identity p \<mapsto> p)\<rparr>"
          "outcome = Internal (Served_Ordinary (packet_identity p))"
          by (simp_all add: scheduler_step_def schedule_contract serve_ordinary_def)
        from Honest_Service Cons result show ?thesis by (intro that(3)[of p ps]) simp_all
      next
        case False
        with action_step None Cons have "t = s" by (simp add: scheduler_step_def schedule_contract serve_ordinary_def)
        then show ?thesis by (intro that(1)) simp_all
      qed
    qed
  next
    case (Some p)
    from selected_regulation_ready(1)[OF Some] obtain u where effect: "regulatory_effect s p = Some u"
      by (auto simp: ready_regulation_def)
    from action_step Some effect have result:
      "t = u\<lparr>regulatory_queue := remove1 p (regulatory_queue s),
        regulation_receipts := (regulation_receipts s)(packet_identity p \<mapsto> p)\<rparr>"
      by (simp add: scheduler_step_def schedule_contract)
    from result regulation_queue_frame[OF effect] show ?thesis by (intro that(1)) simp_all
  qed
next
  case Unproductive_Turn
  with step have "t = s" by (simp add: scheduler_step_def)
  then show ?thesis by (intro that(1)) simp_all
next
  case (Rotate_Context time a k epoch)
  from step Rotate_Context show ?thesis
    by (intro that(1)) (auto simp: scheduler_step_def split: if_splits)
qed

lemma ordinary_shape_preserved:
  assumes step: "scheduler_step s action outcome t" and inv: "ordinary_shape s"
  shows "ordinary_shape t"
  using step
proof (cases rule: ordinary_queue_update)
  case same
  with inv show ?thesis by (simp add: ordinary_shape_def)
next
  case (push p)
  with inv show ?thesis by (auto simp: ordinary_shape_def)
next
  case (pop p ps)
  with inv show ?thesis by (auto simp: ordinary_shape_def)
qed

lemma waiting_persists_without_its_service:
  assumes happens: "step_occurs scheduler_step e" and held: "waiting q (source_state e)"
    and open_request: "\<not> served_ordinary q e"
  shows "waiting q (target_state e)"
proof -
  from happens have step: "scheduler_step (source_state e) (step_action e) (step_outcome e) (target_state e)"
    by (simp add: step_occurs_def)
  from step show ?thesis
  proof (cases rule: ordinary_queue_update)
    case same
    with held show ?thesis by (simp add: waiting_def)
  next
    case (push p)
    with held show ?thesis by (auto simp: waiting_def)
  next
    case (pop p ps)
    with held open_request show ?thesis by (auto simp: waiting_def served_ordinary_def)
  qed
qed

lemma prefix_before_waiting_packet_ignores_later_append:
  assumes "\<exists>p \<in> set ps. packet_identity p = q"
  shows "takeWhile (\<lambda>p. packet_identity p \<noteq> q) (ps @ suffix_packets) =
    takeWhile (\<lambda>p. packet_identity p \<noteq> q) ps"
  using assms by (induction ps) auto

theorem waiting_rank_nonincreasing:
  assumes happens: "step_occurs scheduler_step e" and held: "waiting q (source_state e)"
    and open_request: "\<not> served_ordinary q e"
  shows "rank_nonincreasing (earlier_ordinary q) (source_state e) (target_state e)"
proof -
  from happens have step: "scheduler_step (source_state e) (step_action e) (step_outcome e) (target_state e)"
    by (simp add: step_occurs_def)
  from step show ?thesis
  proof (cases rule: ordinary_queue_update)
    case same
    then show ?thesis by (simp add: rank_nonincreasing_def earlier_ordinary_def)
  next
    case (push p)
    from held have found: "\<exists>p \<in> set (ordinary_queue (source_state e)). packet_identity p = q"
      by (simp add: waiting_def)
    from push prefix_before_waiting_packet_ignores_later_append[OF found, of "[p]"] show ?thesis
      by (simp add: rank_nonincreasing_def earlier_ordinary_def)
  next
    case (pop p ps)
    with open_request have "packet_identity p \<noteq> q" by (auto simp: served_ordinary_def)
    with pop show ?thesis by (simp add: rank_nonincreasing_def earlier_ordinary_def)
  qed
qed

theorem serving_an_earlier_ordinary_packet_decreases_rank:
  assumes occurs: "step_occurs scheduler_step e" and "waiting q (source_state e)"
    and previous: "step_outcome e = Internal (Served_Ordinary earlier)" "earlier \<noteq> q"
    and tick: "step_action e = Honest_Service"
  shows "rank_decreases (earlier_ordinary q) (source_state e) (target_state e)"
proof -
  from occurs previous(1) tick have
    "scheduler_step (source_state e) Honest_Service (Internal (Served_Ordinary earlier)) (target_state e)"
    by (simp add: step_occurs_def)
  from ordinary_service_records_the_head_packet[OF this] obtain p ps where
    before_queue: "ordinary_queue (source_state e) = p # ps"
    and after_queue: "ordinary_queue (target_state e) = ps"
    and earlier: "earlier = packet_identity p" by blast
  from previous(2) earlier show ?thesis
    by (simp add: before_queue after_queue earlier_ordinary_def rank_decreases_def)
qed

lemma honest_turn_with_waiting_work_produces_service:
  assumes "ordinary_shape s" "waiting q s"
  shows "\<exists>t r. scheduler_step s Honest_Service (Internal r) t \<and>
    ((\<exists>q'. r = Served_Ordinary q') \<or> (\<exists>q' k. r = Served_Regulation q' k))"
proof (cases "next_regulation s")
  case None
  from assms obtain p ps where headq: "ordinary_queue s = p # ps"
    and kind: "ordinary_body (packet_contents p)"
    by (cases "ordinary_queue s") (auto simp: ordinary_shape_def waiting_def)
  with None show ?thesis
    by (auto simp: scheduler_step_def schedule_contract serve_ordinary_def)
next
  case (Some p)
  from selected_regulation_ready(1)[OF Some] obtain u where
    "regulatory_effect s p = Some u" by (auto simp: ready_regulation_def)
  with Some show ?thesis by (auto simp: scheduler_step_def schedule_contract)
qed

end
