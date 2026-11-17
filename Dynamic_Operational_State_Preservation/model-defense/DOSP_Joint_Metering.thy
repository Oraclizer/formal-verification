theory DOSP_Joint_Metering
  imports DOSP_Credit_Reconciliation
begin

record product_source_state =
  source_lifecycle :: lifecycle_state
  source_consensus :: integrated_authority
  source_recovery :: "nat recovery_state"
  observed_divergence_work :: "nat set"

datatype credit_admission = Active_Credit_Route | Retained_Debit_Route

definition retained_credit_admission where
  "retained_credit_admission p request index r \<longleftrightarrow>
    (let s = source_lifecycle p; native = current_operational (source_consensus p);
         b = request_binding r; key = binding_key b;
         state = machine_state (core_parent (credit_core native)) in
      lifecycle_phase s = Verified_Cycle request \<and> cycle_custody s = Native_Debit_Pending key \<and>
      source_was_debited state key \<and> native_source_pending native r \<and>
      cycle_names_native_binding request r \<and> current_binding_holds_its_native_lock native r \<and>
      exact_record_reference (credit_core native) index b Confirmed_Decision (request_certificate r) \<and>
      key \<notin> core_published (credit_core native))"

definition accounted_cutover_entry where
  "accounted_cutover_entry row =
    \<lparr>binding_id = accounted_binding row, billing_level = required_level (ticket_metadata (accounted_ticket row)),
      billing_version = accounted_tariff row, billing_epoch = cutover_epoch (ticket_metadata (accounted_ticket row)),
      domains_written = card (accounted_footprint row)\<rparr>"

definition recorded_success_history where
  "recorded_success_history s =
    map accounted_cutover_entry (filter (\<lambda>row. accounted_abort row = None) (lifecycle_invoice s))"

definition fresh_publication_work where
  "fresh_publication_work s allocation \<longleftrightarrow>
    finite (dom allocation) \<and> dom allocation \<inter> completion_log s = {} \<and>
    inj_on allocation (dom allocation - pending_ids s) \<and>
    (\<forall>job d. work_owner s job = Some d \<longrightarrow> allocation job = Some d) \<and>
    (\<forall>job d. allocation job = Some d \<longrightarrow> d \<in> active_domains s) \<and>
    (\<forall>d. (\<exists>job. allocation job = Some d \<and> job \<notin> pending_ids s) \<longleftrightarrow>
      d \<in> active_domains s \<and>
      (\<nexists>existing. work_owner s existing = Some d))"

definition publication_recovery_state where
  "publication_recovery_state s a receipt allocation =
    s\<lparr>primary_record := primary_transfer_value receipt, primary_sequence := published_sequence receipt,
      source_ready := True, work_owner := allocation,
      irreversible_facts := image prod_encode (core_published (credit_core (current_operational a)))\<rparr>"

definition current_primary_is_recorded where
  "current_primary_is_recorded a s \<longleftrightarrow>
    (source_ready s \<and> Suc (primary_sequence s) = next_publication_sequence a \<and>
      (\<exists>receipt. issued_receipt a (primary_sequence s) = Some receipt \<and>
        primary_record s = primary_transfer_value receipt) \<and>
      irreversible_facts s = image prod_encode (core_published (credit_core (current_operational a))))"

lemma the_publication_carries_exact_fresh_work_for_its_stale_replicas:
  assumes "fresh_publication_work s allocation"
  shows "publication_recovery_state s a receipt allocation \<in> recovery_carrier \<and>
    replica (publication_recovery_state s a receipt allocation) = replica s \<and>
    completion_log (publication_recovery_state s a receipt allocation) = completion_log s"
  using assms unfolding publication_recovery_state_def fresh_publication_work_def recovery_carrier_def replica_covered_def
    pending_ids_def by (auto simp: dom_def) blast+

lemma every_active_replica_requires_verification_of_the_new_publication:
  assumes "d \<in> active_domains s" "fresh_publication_work s allocation"
  shows "\<exists>job. allocation job = Some d \<and> job \<notin> completion_log s"
proof -
  obtain job where owner: "allocation job = Some d"
    using assms unfolding fresh_publication_work_def by blast
  have "job \<in> dom allocation" using owner by (simp add: dom_def)
  moreover have "dom allocation \<inter> completion_log s = {}" using assms(2) by (simp add: fresh_publication_work_def)
  ultimately show ?thesis using owner by blast
qed

lemma an_initial_publication_preserves_any_work_already_admitted:
  assumes "fresh_publication_work s allocation" "work_owner s job = Some domain"
  shows "work_owner (publication_recovery_state s a receipt allocation) job = Some domain"
  using assms by (auto simp: fresh_publication_work_def publication_recovery_state_def)

lemma a_finite_recovery_state_can_allocate_verification_for_the_new_publication:
  fixes s :: "nat recovery_state"
  assumes valid: "s \<in> recovery_carrier" and domains: "finite (active_domains s)"
    and log: "finite (completion_log s)" and reservations: "finite reserved"
  shows "\<exists>allocation. fresh_publication_work s allocation \<and> (dom allocation - pending_ids s) \<inter> reserved = {}"
proof -
  let ?old = "pending_ids s"
  let ?used = "?old \<union> completion_log s \<union> reserved"
  let ?missing = "active_domains s - ran (work_owner s)"
  have old: "finite ?old" "?old \<inter> completion_log s = {}"
      "\<And>i d. work_owner s i = Some d \<Longrightarrow> d \<in> active_domains s"
    using valid unfolding recovery_carrier_def by auto
  have "finite ?used" using old(1) log reservations by simp
  then obtain limit where limit: "\<And>i. i \<in> ?used \<Longrightarrow> i < limit"
    unfolding finite_nat_set_iff_bounded by blast
  let ?new = "image ((+) limit) ?missing"
  let ?allocate = "\<lambda>i. if i \<in> ?new then Some (i - limit) else work_owner s i"
  have new_used: "i \<notin> ?used" if "i \<in> ?new" for i
  proof
    assume "i \<in> ?used"
    with limit have "i < limit" by blast
    moreover have "limit \<le> i" using that by auto
    ultimately show False by simp
  qed
  have preserves: "?allocate i = Some d" if "work_owner s i = Some d" for i d
  proof -
    have "i \<in> ?used" using that by (auto simp: pending_ids_def domI)
    then show ?thesis using that new_used by auto
  qed
  have new_exact: "(?allocate i = Some d \<and> i \<notin> ?old) \<longleftrightarrow> d \<in> ?missing \<and> i = limit + d" for i d
  proof (cases "i \<in> ?new")
    case True
    then obtain owner where "owner \<in> ?missing" "i = limit + owner" by auto
    with True new_used[OF True] show ?thesis by auto
  next
    case False
    then show ?thesis by (auto simp: pending_ids_def domI)
  qed
  have allocated: "dom ?allocate = ?old \<union> ?new"
    by (auto simp: pending_ids_def dom_def)
  have finite_new: "finite ?new" using domains by simp
  have finite_all: "finite (dom ?allocate)" using allocated old(1) finite_new by simp
  have disjoint: "dom ?allocate \<inter> completion_log s = {}"
    using old(2) new_used unfolding allocated by blast
  have active: "d \<in> active_domains s" if "?allocate i = Some d" for i d
  proof (cases "i \<in> ?old")
    case True
    then have "i \<notin> ?new" using new_used by blast
    with that show ?thesis using old(3) by simp
  next
    case False
    then show ?thesis using that new_exact[of i d] by auto
  qed
  have unique: "inj_on ?allocate (dom ?allocate - ?old)"
  proof (rule inj_onI)
    fix x y
    assume x: "x \<in> dom ?allocate - ?old" and y: "y \<in> dom ?allocate - ?old"
      and equal: "?allocate x = ?allocate y"
    obtain d where owner_x: "?allocate x = Some d" using x by (auto simp: dom_def)
    have owner_y: "?allocate y = Some d" using equal owner_x by simp
    have "x = limit + d" using new_exact[of x d] x owner_x by blast
    moreover have "y = limit + d" using new_exact[of y d] y owner_y by blast
    ultimately show "x = y" by simp
  qed
  have coverage: "(\<exists>i. ?allocate i = Some d \<and> i \<notin> ?old) \<longleftrightarrow>
      d \<in> active_domains s \<and> (\<nexists>existing. work_owner s existing = Some d)" for d
    using new_exact by (simp add: ran_def)
  have avoids: "(dom ?allocate - ?old) \<inter> reserved = {}"
    unfolding allocated using new_used by blast
  have existing_assignments: "\<forall>job d. work_owner s job = Some d \<longrightarrow> ?allocate job = Some d"
    using preserves by blast
  have active_assignments: "\<forall>job d. ?allocate job = Some d \<longrightarrow> d \<in> active_domains s"
    using active by blast
  have covered_domains: "\<forall>d. (\<exists>job. ?allocate job = Some d \<and> job \<notin> ?old) \<longleftrightarrow>
      d \<in> active_domains s \<and> (\<nexists>existing. work_owner s existing = Some d)"
    using coverage by blast
  have selected: "fresh_publication_work s ?allocate"
    unfolding fresh_publication_work_def
    using finite_all disjoint unique existing_assignments active_assignments covered_domains by blast
  show ?thesis
  proof (rule exI[of _ ?allocate])
    show "fresh_publication_work s ?allocate \<and> (dom ?allocate - pending_ids s) \<inter> reserved = {}"
      using selected avoids by blast
  qed
qed

definition routed_domains_are_active where
  "routed_domains_are_active repair r \<longleftrightarrow>
    (let b = request_binding r; origin = fst (binding_key b)
     in binding_destination b \<in> active_domains repair \<and>
       origin \<in> active_domains repair)"

definition recovery_permits_existing_native_credit where
  "recovery_permits_existing_native_credit p \<longleftrightarrow>
    (let repair = source_recovery p; core = credit_core (current_operational (source_consensus p)) in
      \<not> rollback_incomplete repair \<and>
      (pending_ids repair = {} \<or> (\<not> source_ready repair \<and> core_published core = {})))"

definition recovery_permits_native_credit where
  "recovery_permits_native_credit p \<longleftrightarrow>
    observed_divergence_work p = {} \<and> recovery_permits_existing_native_credit p"

context integrated_dosp_authority
begin

definition joint_credit_candidate where
  "joint_credit_candidate mode versions confirmed evidence p request index route r t a \<longleftrightarrow>
    (let previous = source_consensus p;
         stamped = (source_lifecycle p)\<lparr>lifecycle_clock := consensus_now previous\<rparr>;
         ticket = cycle_ticket request in
     (case mode of Active_Credit_Route \<Rightarrow>
         routed_domains_are_active (source_recovery p) r \<and> recovery_permits_native_credit p
       | Retained_Debit_Route \<Rightarrow>
         retained_credit_admission p request index r \<and> recovery_permits_existing_native_credit p) \<and>
     lifecycle_phase stamped = Verified_Cycle request \<and>
     lifecycle_cutover stamped = degree_state (current_operational previous) \<and>
     lifecycle_registry stamped = authority_registry previous \<and>
     recorded_success_history stamped = billing_history (degree_state (current_operational previous)) \<and>
     tariffs_cover_recorded_usage versions stamped \<and>
     cycle_names_native_binding request r \<and>
     (\<exists>entry. run_registered_meter ticket (cycle_session_id request) index route r previous =
         Some (a, Credit_Result (Some (Credit_Metered entry)))) \<and>
     lifecycle_step flow_policy promotion_authorizations versions confirmed evidence
       (promotion_locks_clear flow_policy (current_operational previous)) stamped
       (Commit_Cycle True) (Cycle_Result (transition_result.Accepted Binding_Committed)) t \<and>
     lifecycle_cutover t = degree_state (current_operational a))"

definition joint_publication_transition where
  "joint_publication_transition mode versions confirmed evidence p request index route r q \<longleftrightarrow>
    (\<exists>t a receipt allocation.
      joint_credit_candidate mode versions confirmed evidence p request index route r t a \<and>
      issued_receipt a (next_publication_sequence (source_consensus p)) = Some receipt \<and>
      published_key receipt = binding_key (request_binding r) \<and>
      published_sequence receipt = next_publication_sequence (source_consensus p) \<and>
      Suc (published_sequence receipt) = next_publication_sequence a \<and>
      fresh_publication_work (source_recovery p) allocation \<and>
      irreversible_facts (source_recovery p) \<subseteq> image prod_encode (core_published (credit_core (current_operational a))) \<and>
      q = p\<lparr>source_lifecycle := t, source_consensus := a,
        source_recovery := publication_recovery_state (source_recovery p) a receipt allocation\<rparr>)"

definition joint_credit_step where
  "joint_credit_step mode versions confirmed evidence p request index route r reply q \<longleftrightarrow>
    (if (\<exists>updated. joint_publication_transition mode versions confirmed evidence p request index route r updated)
     then reply = Cycle_Result (transition_result.Accepted Binding_Committed) \<and>
       joint_publication_transition mode versions confirmed evidence p request index route r q
     else reply = Precommit_Refused \<and> q = p)"

definition joint_credit_excluding_jobs where
  "joint_credit_excluding_jobs reserved mode versions confirmed evidence p request index route r reply q \<longleftrightarrow>
    (let commits = (\<lambda>updated. joint_publication_transition mode versions confirmed evidence p request index route r updated \<and>
        (pending_ids (source_recovery updated) - pending_ids (source_recovery p)) \<inter> reserved = {})
     in if (\<exists>updated. commits updated)
        then reply = Cycle_Result (transition_result.Accepted Binding_Committed) \<and> commits q
        else reply = Precommit_Refused \<and> q = p)"

lemma joint_credit_excluding_no_jobs [simp]:
  "joint_credit_excluding_jobs {} mode versions confirmed evidence p request index route r reply q \<longleftrightarrow>
    joint_credit_step mode versions confirmed evidence p request index route r reply q"
  by (simp add: joint_credit_excluding_jobs_def joint_credit_step_def Let_def)

lemma a_joint_credit_cannot_use_an_outstanding_join_job_as_fresh_work:
  assumes "joint_credit_excluding_jobs reserved mode versions confirmed evidence p request index route r
    (Cycle_Result (transition_result.Accepted Binding_Committed)) q"
  shows "(pending_ids (source_recovery q) - pending_ids (source_recovery p)) \<inter> reserved = {}"
  using assms by (auto simp: joint_credit_excluding_jobs_def Let_def split: if_splits)

lemma a_valid_credit_can_allocate_fresh_jobs_outside_a_finite_reservation:
  assumes raw: "joint_credit_step mode versions confirmed evidence p request index route r
    (Cycle_Result (transition_result.Accepted Binding_Committed)) original"
    and carrier: "source_recovery p \<in> recovery_carrier" "finite (active_domains (source_recovery p))"
      "finite (completion_log (source_recovery p))" "finite reserved"
  shows "\<exists>q. joint_credit_excluding_jobs reserved mode versions confirmed evidence p request index route r
    (Cycle_Result (transition_result.Accepted Binding_Committed)) q"
proof -
  let ?repair = "source_recovery p"
  obtain t a receipt where candidate: "joint_credit_candidate mode versions confirmed evidence p request index route r t a"
    and issued: "issued_receipt a (next_publication_sequence (source_consensus p)) = Some receipt"
    and exact: "published_key receipt = binding_key (request_binding r)"
      "published_sequence receipt = next_publication_sequence (source_consensus p)"
      "Suc (published_sequence receipt) = next_publication_sequence a"
    and past: "irreversible_facts ?repair \<subseteq> image prod_encode (core_published (credit_core (current_operational a)))"
    using raw by (auto simp: joint_credit_step_def joint_publication_transition_def split: if_splits)
  obtain allocation where fresh: "fresh_publication_work ?repair allocation"
    and avoids: "(dom allocation - pending_ids ?repair) \<inter> reserved = {}"
    using a_finite_recovery_state_can_allocate_verification_for_the_new_publication[OF carrier] by blast
  let ?q = "p\<lparr>source_lifecycle := t, source_consensus := a,
    source_recovery := publication_recovery_state ?repair a receipt allocation\<rparr>"
  have new: "joint_publication_transition mode versions confirmed evidence p request index route r ?q"
    unfolding joint_publication_transition_def using candidate issued exact past fresh
    by (intro exI[of _ t] exI[of _ a] exI[of _ receipt] exI[of _ allocation]) blast
  have protected: "(pending_ids (source_recovery ?q) - pending_ids ?repair) \<inter> reserved = {}"
    using avoids by (simp add: pending_ids_def publication_recovery_state_def)
  have can: "\<exists>updated. joint_publication_transition mode versions confirmed evidence p request index route r updated \<and>
    (pending_ids (source_recovery updated) - pending_ids ?repair) \<inter> reserved = {}"
    using new protected by blast
  show ?thesis using new protected can
    by (intro exI[of _ ?q]) (simp add: joint_credit_excluding_jobs_def Let_def)
qed

lemma a_missing_final_measurement_cannot_publish_either_ledger:
  assumes no_measurement:
    "checked_final_leaves evidence ((source_lifecycle p)\<lparr>lifecycle_clock := consensus_now (source_consensus p)\<rparr>) request
      (transition_result.Accepted Binding_Committed) = None"
  shows "joint_credit_step mode versions confirmed evidence p request index route r reply q \<longleftrightarrow>
    reply = Precommit_Refused \<and> q = p"
proof -
  have impossible: "\<not> joint_credit_candidate mode versions confirmed evidence p request index route r t a" for t a
  proof
    assume ready: "joint_credit_candidate mode versions confirmed evidence p request index route r t a"
    let ?s = "(source_lifecycle p)\<lparr>lifecycle_clock := consensus_now (source_consensus p)\<rparr>"
    have verified: "lifecycle_phase ?s = Verified_Cycle request"
      and proposed: "lifecycle_step flow_policy promotion_authorizations versions confirmed evidence
       (promotion_locks_clear flow_policy (current_operational (source_consensus p))) ?s
       (Commit_Cycle True) (Cycle_Result (transition_result.Accepted Binding_Committed)) t"
      using ready by (auto simp: joint_credit_candidate_def Let_def)
    from proposed verified no_measurement show False
      by (cases rule: lifecycle_step.cases) (auto simp: metered_attempt_def)
  qed
  show ?thesis using impossible by (simp add: joint_credit_step_def joint_publication_transition_def)
qed

lemma an_exited_destination_cannot_start_a_new_native_credit:
  assumes "binding_destination (request_binding r) \<notin> active_domains (source_recovery p)"
  shows "joint_credit_step Active_Credit_Route versions confirmed evidence p request index route r reply q \<longleftrightarrow>
    reply = Precommit_Refused \<and> q = p"
  using assms by (simp add: joint_credit_step_def joint_publication_transition_def joint_credit_candidate_def
    routed_domains_are_active_def Let_def)

lemma an_exited_origin_cannot_start_a_new_native_credit:
  assumes "fst (binding_key (request_binding r)) \<notin> active_domains (source_recovery p)"
  shows "joint_credit_step Active_Credit_Route versions confirmed evidence p request index route r reply q \<longleftrightarrow>
    reply = Precommit_Refused \<and> q = p"
  using assms by (simp add: joint_credit_step_def joint_publication_transition_def joint_credit_candidate_def
    routed_domains_are_active_def Let_def)

lemma retained_settlement_requires_the_preexisting_debit_and_current_confirmation:
  assumes "\<not> retained_credit_admission p request index r"
  shows "joint_credit_step Retained_Debit_Route versions confirmed evidence p request index route r reply q \<longleftrightarrow>
    reply = Precommit_Refused \<and> q = p"
  using assms by (simp add: joint_credit_step_def joint_publication_transition_def joint_credit_candidate_def Let_def)

lemma retained_settlement_is_bound_to_the_actual_debit:
  assumes "joint_credit_step Retained_Debit_Route versions confirmed evidence p request index route r
    (Cycle_Result (transition_result.Accepted Binding_Committed)) q"
  shows "source_was_debited (machine_state (core_parent (credit_core (current_operational (source_consensus p)))))
      (binding_key (request_binding r)) \<and>
    exact_record_reference (credit_core (current_operational (source_consensus p))) index
      (request_binding r) Confirmed_Decision (request_certificate r)"
  using assms by (auto simp: joint_credit_step_def joint_publication_transition_def joint_credit_candidate_def
    retained_credit_admission_def Let_def split: if_splits)

lemma a_missing_native_success_history_blocks_the_joint_publication:
  assumes "recorded_success_history (source_lifecycle p) \<noteq> billing_history (degree_state (current_operational (source_consensus p)))"
  shows "joint_credit_step mode versions confirmed evidence p request index route r reply q \<longleftrightarrow>
    reply = Precommit_Refused \<and> q = p"
  using assms by (auto simp: joint_credit_step_def joint_publication_transition_def joint_credit_candidate_def
    recorded_success_history_def Let_def split: if_splits)

lemma missing_or_changed_historical_tariff_blocks_a_new_joint_credit:
  assumes "\<not> tariffs_cover_recorded_usage versions (source_lifecycle p)"
  shows "joint_credit_step mode versions confirmed evidence p request index route r reply q \<longleftrightarrow>
    reply = Precommit_Refused \<and> q = p"
  using assms by (simp add: joint_credit_step_def joint_publication_transition_def joint_credit_candidate_def Let_def)

lemma a_verified_debit_can_settle_after_its_original_route_exits:
  assumes offer: "joint_credit_candidate Active_Credit_Route versions confirmed evidence p request index route r t a"
    and same_binding: "source_lifecycle retired = source_lifecycle p" "source_consensus retired = source_consensus p"
    and ready: "retained_credit_admission retired request index r"
    and quiet: "pending_ids (source_recovery retired) = {}" "\<not> rollback_incomplete (source_recovery retired)"
  shows "joint_credit_candidate Retained_Debit_Route versions confirmed evidence retired request index route r t a"
  using assms by (auto simp: joint_credit_candidate_def recovery_permits_existing_native_credit_def Let_def)

lemma a_first_publication_can_adopt_work_already_admitted_at_bootstrap:
  assumes credit: "joint_credit_candidate Active_Credit_Route versions confirmed evidence p request index route r t a"
    and snapshots: "source_lifecycle boot = source_lifecycle p" "source_consensus boot = source_consensus p"
      "active_domains (source_recovery boot) = active_domains (source_recovery p)"
    and bootstrap: "\<not> source_ready (source_recovery boot)" "\<not> rollback_incomplete (source_recovery boot)"
      "core_published (credit_core (current_operational (source_consensus boot))) = {}" "observed_divergence_work boot = {}"
  shows "joint_credit_candidate Active_Credit_Route versions confirmed evidence boot request index route r t a"
  using assms by (auto simp: joint_credit_candidate_def recovery_permits_native_credit_def
    recovery_permits_existing_native_credit_def routed_domains_are_active_def Let_def)

lemma a_confirmed_joint_credit_requires_both_linked_effects:
  assumes "joint_credit_step mode versions confirmed evidence p request index route r
    (Cycle_Result (transition_result.Accepted Binding_Committed)) q"
  shows "joint_credit_candidate mode versions confirmed evidence p request index route r (source_lifecycle q) (source_consensus q)
    \<and> source_recovery q \<in> recovery_carrier \<and>
    primary_sequence (source_recovery q) = next_publication_sequence (source_consensus p) \<and>
    irreversible_facts (source_recovery p) \<subseteq> irreversible_facts (source_recovery q)"
proof -
  obtain t a receipt allocation where known:
    "joint_credit_candidate mode versions confirmed evidence p request index route r t a"
    "published_sequence receipt = next_publication_sequence (source_consensus p)"
    "irreversible_facts (source_recovery p) \<subseteq> image prod_encode (core_published (credit_core (current_operational a)))"
    "q = p\<lparr>source_lifecycle := t, source_consensus := a,
        source_recovery := publication_recovery_state (source_recovery p) a receipt allocation\<rparr>"
    and allocation: "fresh_publication_work (source_recovery p) allocation"
    using assms by (auto simp: joint_credit_step_def joint_publication_transition_def split: if_splits)
  have carrier: "publication_recovery_state (source_recovery p) a receipt allocation \<in> recovery_carrier"
    using the_publication_carries_exact_fresh_work_for_its_stale_replicas[OF allocation] by blast
  show ?thesis using carrier known by (simp add: publication_recovery_state_def)
qed

lemma published_credit_installs_the_actual_current_recovery_anchor:
  assumes "joint_credit_step mode versions confirmed evidence p request index route r
    (Cycle_Result (transition_result.Accepted Binding_Committed)) q"
  shows "current_primary_is_recorded (source_consensus q) (source_recovery q)"
  using assms by (auto simp: joint_credit_step_def joint_publication_transition_def publication_recovery_state_def
      current_primary_is_recorded_def split: if_splits)

end

end
