theory Scoped_Dispatch
  imports Stored_Service_Observation
    Scoped_Source_Finality
begin

section \<open>Exact service in the approved view\<close>

lemma scoped_commit_runs_the_approved_view:
  assumes "scoped_service inputs signer verified s turn p = (Internal e,t)"
  obtains u where
    "(turn,p) \<in> verified"
    "qualified_turn signer {turn} s turn"
    "planned (authorized_view inputs s) = Some p"
    "scheduler_step (authorized_view inputs s) Honest_Service (Internal e) u"
    "t = u\<lparr>regulatory_queue := (case Internal e of
      Internal (Served_Regulation _ _) \<Rightarrow> remove1 p (regulatory_queue s)
      | _ \<Rightarrow> regulatory_queue s)\<rparr>"
  using assms by (auto simp: scoped_service_def scheduler_step_def Let_def split: prod.splits if_splits)

lemma compare_commit_uses_the_exact_current_order:
  assumes "observe_sequence inputs signer orders retained expected current turn p =
    (Compared_Attempt (Service_Result (Internal e)), t)"
  shows "expected = current"
    "orders turn = Some p"
    "qualified_turn signer {turn} (observed_scheduler current) turn"
    "scoped_service inputs signer (signed_packets_by_turn orders)
       (observed_scheduler current) turn p = (Internal e,t)"
proof -
  from assms have eq: "expected = current"
    and run: "scoped_service inputs signer (signed_packets_by_turn orders)
        (observed_scheduler current) turn p = (Internal e,t)"
    by (auto simp: observe_sequence_def try_service_at_def split: if_splits prod.splits)
  from run obtain "(turn,p) \<in> signed_packets_by_turn orders"
    "qualified_turn signer {turn} (observed_scheduler current) turn"
    by (elim scoped_commit_runs_the_approved_view) blast
  with eq run show "expected = current" "orders turn = Some p"
    "qualified_turn signer {turn} (observed_scheduler current) turn"
    "scoped_service inputs signer (signed_packets_by_turn orders)
        (observed_scheduler current) turn p = (Internal e,t)"
    by (simp_all add: signed_packets_by_turn_def)
qed

lemma scoped_regulatory_effect:
  assumes commit: "scoped_service inputs signer verified s turn p = (Internal (Served_Regulation q k), t)"
  obtains u where
    "next_regulation (authorized_view inputs s) = Some p"
    "p \<in> set (regulatory_queue s)"
    "policy_allows inputs (rollback_context s) (packet_contents p)"
    "q = packet_identity p"
    "k = regulatory_case (packet_contents p)"
    "regulatory_effect (authorized_view inputs s) p = Some u"
    "t = u\<lparr>regulatory_queue := remove1 p (regulatory_queue s),
           regulation_receipts := (regulation_receipts (authorized_view inputs s))(q \<mapsto> p)\<rparr>"
proof -
  let ?v = "authorized_view inputs s"
  from scoped_commit_runs_the_approved_view[OF commit] obtain stepped where
    plan: "planned ?v = Some p"
    and run: "scheduler_step ?v Honest_Service (Internal (Served_Regulation q k)) stepped"
    and out: "t = stepped\<lparr>regulatory_queue := remove1 p (regulatory_queue s)\<rparr>"
    by auto
  from honest_service_uses_selected_regulation[OF run] obtain selected u where
    choice: "next_regulation ?v = Some selected" and member: "selected \<in> set (regulatory_queue ?v)"
    and key: "q = packet_identity selected" and scope: "k = regulatory_case (packet_contents selected)"
    and effect: "regulatory_effect ?v selected = Some u"
    and result: "stepped = u\<lparr>regulatory_queue := remove1 selected (regulatory_queue ?v),
      regulation_receipts := (regulation_receipts ?v)(q \<mapsto> selected)\<rparr>" by blast
  from choice plan have selected: "selected = p" by (simp add: planned_def)
  with member have pending: "p \<in> set (regulatory_queue s)"
    and allowed: "policy_allows inputs (rollback_context s) (packet_contents p)"
    by (simp_all add: authorized_view_def)
  show thesis
    using choice key scope effect result selected out pending allowed
    by (intro that[of u]) simp_all
qed

lemma scoped_ordinary_effect:
  assumes commit: "scoped_service inputs signer verified s turn p = (Internal (Served_Ordinary q),t)"
  obtains rest where
    "next_regulation (authorized_view inputs s) = None"
    "ordinary_queue s = p # rest" "ordinary_body (packet_contents p)"
    "q = packet_identity p"
    "t = s\<lparr>ordinary_queue := rest, ordinary_receipts := (ordinary_receipts s)(q \<mapsto> p)\<rparr>"
proof -
  let ?v = "authorized_view inputs s"
  from scoped_commit_runs_the_approved_view[OF commit] obtain u where
    plan: "planned ?v = Some p"
    and run: "scheduler_step ?v Honest_Service (Internal (Served_Ordinary q)) u"
    and out: "t = u\<lparr>regulatory_queue := regulatory_queue s\<rparr>"
    by auto
  from ordinary_service_records_the_head_packet[OF run] obtain head rest where
    fifo: "ordinary_queue ?v = head # rest" and ordinary: "ordinary_body (packet_contents head)"
    and q: "q = packet_identity head" and none: "priority_slots ?v = 0"
    by blast
  have choice: "next_regulation ?v = None" using none
    by (simp add: no_regulation_selected_iff_no_priority_slot)
  with plan fifo have head: "head = p" by (simp add: planned_def)
  from run choice fifo ordinary q head have after:
    "u = ?v\<lparr>ordinary_queue := rest, ordinary_receipts := (ordinary_receipts ?v)(q \<mapsto> p)\<rparr>"
    by (auto simp: scheduler_step_def schedule_contract serve_ordinary_def)
  from after out have result:
    "t = s\<lparr>ordinary_queue := rest, ordinary_receipts := (ordinary_receipts s)(q \<mapsto> p)\<rparr>"
    by (cases s) (simp add: authorized_view_def)
  show thesis
    using choice fifo ordinary q result head
    by (intro that[of rest]) (simp_all add: authorized_view_def)
qed

section \<open>A constructive choice of an offered order\<close>

definition matches_plan_order ::
  "(nat \<Rightarrow> nat option) \<Rightarrow> (service_turn \<Rightarrow> packet option) \<Rightarrow>
    scheduler_state \<Rightarrow> packet \<Rightarrow> service_turn \<Rightarrow> bool" where
  "matches_plan_order signer orders s p turn \<longleftrightarrow>
    orders turn = Some p \<and> qualified_turn signer {turn} s turn"

definition choose_current_order ::
  "verified_inputs \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> (service_turn \<Rightarrow> packet option) \<Rightarrow>
    scheduler_state \<Rightarrow> service_turn list \<Rightarrow> (service_turn \<times> packet) option" where
  "choose_current_order inputs signer orders s offered =
    (case planned (authorized_view inputs s) of None \<Rightarrow> None | Some p \<Rightarrow>
       map_option (\<lambda>turn. (turn,p)) (List.find (matches_plan_order signer orders s p) offered))"

lemma a_matching_offered_order_gives_a_concrete_choice:
  assumes "planned (authorized_view inputs s) = Some p"
    "\<exists>turn \<in> set offered. matches_plan_order signer orders s p turn"
  obtains turn where
    "choose_current_order inputs signer orders s offered = Some (turn,p)"
    "matches_plan_order signer orders s p turn"
proof -
  have "List.find (matches_plan_order signer orders s p) offered \<noteq> None"
    using assms(2) by (auto simp: find_None_iff)
  then obtain turn where selected: "List.find (matches_plan_order signer orders s p) offered = Some turn" by auto
  then have "matches_plan_order signer orders s p turn" by (auto simp: find_Some_iff)
  then show thesis using selected assms(1)
    by (intro that[of turn]) (simp_all add: choose_current_order_def)
qed

theorem a_chosen_current_order_produces_a_real_service:
  assumes plan: "planned (authorized_view inputs s) = Some p"
    and valid: "matches_plan_order signer orders s p turn"
    and shape: "ordinary_shape s" and waiting: "waiting q s"
  obtains t e where
    "scoped_service inputs signer (signed_packets_by_turn orders) s turn p = (Internal e,t)"
    "(\<exists>i. e = Served_Ordinary i) \<or> (\<exists>i k. e = Served_Regulation i k)"
proof -
  let ?v = "authorized_view inputs s"
  have "ordinary_shape ?v" "waiting q ?v"
    using shape waiting by (simp_all add: authorized_view_def ordinary_shape_def waiting_def)
  from honest_turn_with_waiting_work_produces_service[OF this] obtain u e where
    service: "schedule ?v = (Internal e,u)"
    and actual: "(\<exists>i. e = Served_Ordinary i) \<or> (\<exists>i k. e = Served_Regulation i k)"
    by (auto simp: scheduler_step_def)
  from service valid plan obtain t where
    "scoped_service inputs signer (signed_packets_by_turn orders) s turn p = (Internal e,t)"
    by (auto simp: scoped_service_def Let_def signed_packets_by_turn_def matches_plan_order_def)
  then show thesis using actual by (rule that)
qed

lemma every_regulatory_effect_keeps_ordinary_responsibility:
  assumes "regulatory_effect s p = Some u"
  shows "ordinary_queue u = ordinary_queue s"
    "ordinary_receipts u = ordinary_receipts s"
    "dedup_ids u = dedup_ids s"
    "regulation_receipts u = regulation_receipts s"
proof -
  have "ordinary_queue u = ordinary_queue s \<and> ordinary_receipts u = ordinary_receipts s
    \<and> dedup_ids u = dedup_ids s \<and> regulation_receipts u = regulation_receipts s"
    using assms by (cases "packet_contents p")
      (auto simp: regulatory_effect_def split: if_splits prod.splits transition_result.splits)
  then show "ordinary_queue u = ordinary_queue s" "ordinary_receipts u = ordinary_receipts s"
    "dedup_ids u = dedup_ids s" "regulation_receipts u = regulation_receipts s" by simp_all
qed

lemma scoped_regulatory_commit_preserves_fifo:
  assumes "scoped_service inputs signer verified s turn p = (Internal (Served_Regulation q k),t)"
  shows "ordinary_queue t = ordinary_queue s"
    "ordinary_receipts t = ordinary_receipts s"
    "dedup_ids t = dedup_ids s"
    "regulation_receipts t q = Some p"
proof -
  let ?v = "authorized_view inputs s"
  from scoped_regulatory_effect[OF assms] obtain u where
    effect: "regulatory_effect ?v p = Some u"
    and out: "t = u\<lparr>regulatory_queue := remove1 p (regulatory_queue s),
           regulation_receipts := (regulation_receipts ?v)(q \<mapsto> p)\<rparr>" by blast
  show "ordinary_queue t = ordinary_queue s"
    "ordinary_receipts t = ordinary_receipts s"
    "dedup_ids t = dedup_ids s"
    "regulation_receipts t q = Some p"
    using every_regulatory_effect_keeps_ordinary_responsibility[OF effect] out
    by (simp_all add: authorized_view_def)
qed

lemma a_scoped_governed_commit_uses_the_same_checked_rollback:
  assumes commit: "scoped_service inputs signer verified s turn p = (Internal (Served_Regulation q k), t)"
    and body: "packet_contents p = Execute_Governed_Rollback r a pf"
  shows "q = packet_identity p" "q = request_id r" "k = request_case r"
    "checked_rollback inputs (rollback_context s) r a pf = (Accepted q, rollback_context t)"
    "rollback_step (rollback_context s) (Execute_Rollback r a pf) (Accepted q) (rollback_context t)"
proof -
  let ?v = "authorized_view inputs s"
  from scoped_commit_runs_the_approved_view[OF commit] obtain stepped where
    run: "scheduler_step ?v Honest_Service (Internal (Served_Regulation q k)) stepped"
    and out: "t = stepped\<lparr>regulatory_queue := remove1 p (regulatory_queue s)\<rparr>"
    by auto
  from scoped_regulatory_effect[OF commit] obtain
    choice: "next_regulation ?v = Some p"
    and allowed: "policy_allows inputs (rollback_context s) (packet_contents p)"
    and q: "q = packet_identity p"
    and k: "k = regulatory_case (packet_contents p)"
    by blast
  from a_regulatory_rollback_executes_the_assured_handler[OF run choice body] out
  have id: "q = request_id r"
    and raw: "rollback_step (rollback_context s) (Execute_Rollback r a pf)
      (Accepted q) (rollback_context t)"
    by (simp_all add: authorized_view_def)
  from allowed body raw have checked:
    "checked_rollback inputs (rollback_context s) r a pf = (Accepted q, rollback_context t)"
    by (auto simp: checked_rollback_def rollback_step_def split: option.splits if_splits)
  show "q = packet_identity p" "q = request_id r" "k = request_case r"
    "checked_rollback inputs (rollback_context s) r a pf = (Accepted q, rollback_context t)"
    "rollback_step (rollback_context s) (Execute_Rollback r a pf) (Accepted q) (rollback_context t)"
    using q id k body checked raw by simp_all
qed

section \<open>Combined scope, restoration, finality and accounting\<close>

theorem committed_rollback_consumes_authority_frame_and_budget:
  assumes obs: "observe_sequence inputs signer orders retained expected current turn p =
    (Compared_Attempt (Service_Result (Internal (Served_Regulation q k))), t)"
    and body: "packet_contents p = Execute_Governed_Rollback r a pf"
  defines "s \<equiv> observed_scheduler current"
  shows "expected = current \<and> orders turn = Some p \<and> q = request_id r \<and> k = request_case r"
    "regulation_receipts t q = Some p \<and> ordinary_queue t = ordinary_queue s"
    "requested_role r = Governance \<or> verified_origin inputs r = Some Regulatory_Review
      \<Longrightarrow> r \<in> collective_decisions inputs"
    "request_scope r = Wide \<Longrightarrow>
      matches_certificate (rollback_context s) r Governance_Ratification Governance a"
    "case_remaining (rollback_context t) k + 1 = case_remaining (rollback_context s) k"
    "terminal_records (rollback_context s) j = Some prior \<Longrightarrow>
      terminal_records (rollback_context t) j = Some prior \<and>
      (\<forall>c \<in> terminal_cells prior. cell_value (rollback_context t) c = cell_value (rollback_context s) c)"
    "\<exists>g rules h. grant_at (rollback_context s) (authority_epoch (rollback_context s)) (requester r) = Some g
      \<and> rules_at (rollback_context s) k (request_policy_epoch r) = Some rules
      \<and> journal (rollback_context s) (undo_entry r) = Some h
      \<and> r \<in> authenticated_intents (rollback_context s)
      \<and> grant_role g = requested_role r
      \<and> k = entry_case h
      \<and> request_authority_epoch r = authority_epoch (rollback_context s)
      \<and> request_policy_epoch r = policy_epoch (rollback_context s) k
      \<and> request_window r = case_window rules
      \<and> fst (case_window rules) \<le> consensus_time (rollback_context s)
      \<and> consensus_time (rollback_context s) < snd (case_window rules)
      \<and> footprint r \<subseteq> grant_cells g \<inter> policy_cells rules (requested_role r) \<inter> entry_cells h
      \<and> (\<forall>c \<in> footprint r. cell_value (rollback_context t) c = previous_value h c)
      \<and> preserves_outside cell_value (footprint r) (rollback_context s) (rollback_context t)
      \<and> replica_value (rollback_context t) = replica_value (rollback_context s)"
proof -
  from compare_commit_uses_the_exact_current_order[OF obs] have eq: "expected = current"
    and order: "orders turn = Some p"
    and service: "scoped_service inputs signer (signed_packets_by_turn orders) s turn p =
      (Internal (Served_Regulation q k), t)"
    by (simp_all add: s_def)
  from a_scoped_governed_commit_uses_the_same_checked_rollback[OF service body]
  have id: "q = request_id r" and key: "k = request_case r"
    and checked: "checked_rollback inputs (rollback_context s) r a pf = (Accepted q, rollback_context t)"
    and step: "rollback_step (rollback_context s) (Execute_Rollback r a pf) (Accepted q) (rollback_context t)"
    by blast+
  show "expected = current \<and> orders turn = Some p \<and> q = request_id r \<and> k = request_case r"
    by (simp add: eq order id key)
  show "regulation_receipts t q = Some p \<and> ordinary_queue t = ordinary_queue s"
    using scoped_regulatory_commit_preserves_fifo[OF service] by simp
  show "requested_role r = Governance \<or> verified_origin inputs r = Some Regulatory_Review
      \<Longrightarrow> r \<in> collective_decisions inputs"
    by (rule accepted_governance_or_review_has_the_exact_decision[OF checked])
  show "request_scope r = Wide \<Longrightarrow>
      matches_certificate (rollback_context s) r Governance_Ratification Governance a"
    using step broad_rollback_requires_ratification by blast
  show "case_remaining (rollback_context t) k + 1 = case_remaining (rollback_context s) k"
    using successful_rollback_spends_unit(1)[OF step] key by simp
  show "terminal_records (rollback_context s) j = Some prior \<Longrightarrow>
      terminal_records (rollback_context t) j = Some prior \<and>
      (\<forall>c \<in> terminal_cells prior. cell_value (rollback_context t) c = cell_value (rollback_context s) c)"
    by (rule immutable_terminal_effect[OF step])
  obtain g rules h where
    auth: "grant_at (rollback_context s) (authority_epoch (rollback_context s)) (requester r) = Some g"
      "rules_at (rollback_context s) (request_case r) (policy_epoch (rollback_context s) (request_case r)) = Some rules"
      "journal (rollback_context s) (undo_entry r) = Some h"
      "r \<in> authenticated_intents (rollback_context s)"
      "grant_role g = requested_role r"
      "request_case r = entry_case h"
      "request_authority_epoch r = authority_epoch (rollback_context s)"
      "request_policy_epoch r = policy_epoch (rollback_context s) (request_case r)"
      "request_window r = case_window rules"
      "fst (case_window rules) \<le> consensus_time (rollback_context s)"
      "consensus_time (rollback_context s) < snd (case_window rules)"
      "footprint r \<subseteq> grant_cells g \<inter> policy_cells rules (requested_role r) \<inter> entry_cells h"
    by (rule rollback_authority_contract[OF step]) (rule that; assumption)
  obtain previous where
    frame: "journal (rollback_context s) (undo_entry r) = Some previous"
      "\<forall>c \<in> footprint r. cell_value (rollback_context t) c = previous_value previous c"
      "preserves_outside cell_value (footprint r) (rollback_context s) (rollback_context t)"
      "replica_value (rollback_context t) = replica_value (rollback_context s)"
    by (rule selective_restoration[OF step]) (rule that; assumption)
  from auth(3) frame(1) have previous: "previous = h" by simp
  show "\<exists>g rules h. grant_at (rollback_context s) (authority_epoch (rollback_context s)) (requester r) = Some g
      \<and> rules_at (rollback_context s) k (request_policy_epoch r) = Some rules
      \<and> journal (rollback_context s) (undo_entry r) = Some h
      \<and> r \<in> authenticated_intents (rollback_context s)
      \<and> grant_role g = requested_role r
      \<and> k = entry_case h
      \<and> request_authority_epoch r = authority_epoch (rollback_context s)
      \<and> request_policy_epoch r = policy_epoch (rollback_context s) k
      \<and> request_window r = case_window rules
      \<and> fst (case_window rules) \<le> consensus_time (rollback_context s)
      \<and> consensus_time (rollback_context s) < snd (case_window rules)
      \<and> footprint r \<subseteq> grant_cells g \<inter> policy_cells rules (requested_role r) \<inter> entry_cells h
      \<and> (\<forall>c \<in> footprint r. cell_value (rollback_context t) c = previous_value h c)
      \<and> preserves_outside cell_value (footprint r) (rollback_context s) (rollback_context t)
      \<and> replica_value (rollback_context t) = replica_value (rollback_context s)"
    using auth frame previous key
    by (intro exI[of _ g] exI[of _ rules] exI[of _ h]) simp
qed

end
