theory DOSP_Classified_Entry
  imports DOSP_Product_Source
begin

definition applies_classified_registry where
  "applies_classified_registry features path version epoch p \<longleftrightarrow>
    (let s = source_lifecycle p; a = source_consensus p; native = current_operational a; asset = registered_asset native;
         recovery = source_recovery p in
      lifecycle_phase s = Idle_Cycle \<and> cycle_custody s = Local_Cells_Only \<and>
      asset_owner (machine_state (core_parent (credit_core native))) asset = None \<and>
      fst (lifecycle_session s) = asset \<and> lifecycle_cutover s = degree_state native \<and>
      lifecycle_registry s = authority_registry a \<and> lifecycle_tariff s = version \<and>
      recorded_success_history s = billing_history (degree_state native) \<and>
      irreversible_facts recovery = image prod_encode (core_published (credit_core native)) \<and>
      recovery \<in> recovery_carrier \<and> finite (active_domains recovery) \<and> finite (completion_log recovery) \<and>
      observed_divergence_work p \<subseteq> pending_ids recovery \<and>
      (rollback_incomplete recovery \<longrightarrow> pending_ids recovery \<noteq> {}) \<and>
      (if source_ready recovery then
         (\<exists>receipt. issued_receipt a (primary_sequence recovery) = Some receipt \<and>
          primary_transfer_value receipt = primary_record recovery \<and> Suc (primary_sequence recovery) = next_publication_sequence a)
       else core_published (credit_core native) = {}) \<and>
      initial_registry_record features path version epoch = Some (route_metadata (degree_state native)))"

lemma the_initial_recovery_facts_are_the_native_published_facts:
  assumes "applies_classified_registry features path version epoch p"
  shows "irreversible_facts (source_recovery p) =
    image prod_encode (core_published (credit_core (current_operational (source_consensus p))))"
  using assms by (simp add: applies_classified_registry_def Let_def)

lemma only_unpublished_genesis_can_start_without_the_current_primary_anchor:
  assumes "applies_classified_registry features path version epoch p"
    "\<not> source_ready (source_recovery p)"
  shows "core_published (credit_core (current_operational (source_consensus p))) = {}"
  using assms by (simp add: applies_classified_registry_def Let_def)

record product_supply =
  supplied_versions :: "nat \<Rightarrow> meter_schedule option"
  supplied_restorations :: "restoration_evidence set"
  supplied_measurement :: commit_evidence
  supplied_administrators :: "nat set"
  supplied_approvals :: "resync_approval set"
  supplied_journals :: available_journals
  supplied_head :: recovery_head
  supplied_offers :: "recovery_offer list"
  supplied_routing_grants :: "nat routing_grants"
  supplied_routing_plan :: "scheduled_routing_change list"

context integrated_dosp_authority
begin

definition classified_product_execution where
  "classified_product_execution features path version epoch versions confirmed evidence administrators approvals sources head offers grants
     carrier p events q \<longleftrightarrow>
      applies_classified_registry features path version epoch p \<and>
      lifecycle_session (source_lifecycle p) = active_session \<and>
      versions version \<noteq> None \<and>
      tariffs_cover_recorded_usage versions (source_lifecycle p) \<and>
      (\<exists>plan. valid_routing_approval_plan (source_recovery p) grants plan) \<and>
      finite_trace (product_source_step versions confirmed evidence administrators approvals sources head offers grants) carrier p events q"

definition product_step_with_supply where
  "product_step_with_supply input p command reply q =
    product_source_step (supplied_versions input) (supplied_restorations input) (supplied_measurement input)
      (supplied_administrators input) (supplied_approvals input) (supplied_journals input) (supplied_head input)
      (supplied_offers input) (supplied_routing_grants input) p command reply q"

definition indexed_product_step where
  "indexed_product_step supplies before command reply after \<longleftrightarrow>
    (case before of (i,p) \<Rightarrow> case after of (j,q) \<Rightarrow>
      (let current = supplied_routing_grants (supplies i); supplied = supplied_routing_grants (supplies j)
       in j = Suc i \<and> product_step_with_supply (supplies i) p command reply q \<and>
          (supplied = current \<or>
           review_routing_approvals (source_recovery q) (consensus_now (source_consensus q)) current supplied (supplied_routing_plan (supplies j)) =
            (supplied,Routing_Approvals_Accepted))))"

definition classified_execution_with_current_supplies where
  "classified_execution_with_current_supplies features path version epoch supplies carrier p events q \<longleftrightarrow>
    applies_classified_registry features path version epoch p \<and>
    lifecycle_session (source_lifecycle p) = active_session \<and>
    supplied_versions (supplies 0) version \<noteq> None \<and>
    tariffs_cover_recorded_usage (supplied_versions (supplies 0)) (source_lifecycle p) \<and>
    valid_routing_approval_plan (source_recovery p) (supplied_routing_grants (supplies 0)) (supplied_routing_plan (supplies 0)) \<and>
    (\<forall>i<length events. extends_tariff_archive (supplied_versions (supplies i)) (supplied_versions (supplies (Suc i)))) \<and>
    (\<exists>indexed.
      finite_trace (indexed_product_step supplies)
        (UNIV \<times> carrier) (0,p) indexed (length events,q) \<and>
      map (\<lambda>e. mk_event (snd (source_state e)) (step_action e) (step_outcome e) (snd (target_state e))) indexed = events)"

lemma a_false_registry_classification_cannot_seed_a_product_execution:
  assumes declared: "tvo_required_level features = Some expected"
    and wrong: "required_level (route_metadata (degree_state (current_operational (source_consensus p)))) \<noteq> expected"
  shows "\<not> classified_product_execution features path version epoch versions confirmed evidence administrators approvals sources head offers grants
     carrier p events q"
  using assms by (auto simp: classified_product_execution_def applies_classified_registry_def Let_def
    first_matching_registry_rule_is_the_one_consumed)

lemma current_supply_cannot_override_wrong_seed_classification:
  assumes declared: "tvo_required_level features = Some expected"
    and wrong: "required_level (route_metadata (degree_state (current_operational (source_consensus p)))) \<noteq> expected"
  shows "\<not> classified_execution_with_current_supplies features path version epoch supplies carrier p events q"
  using assms by (auto simp: classified_execution_with_current_supplies_def applies_classified_registry_def Let_def
    first_matching_registry_rule_is_the_one_consumed)

lemma a_replaced_issued_tariff_cannot_enter_the_classified_trace:
  assumes "i < length events" "supplied_versions (supplies i) key = Some price"
    "supplied_versions (supplies (Suc i)) key \<noteq> Some price"
  shows "\<not> classified_execution_with_current_supplies features path version epoch supplies carrier p events q"
  using assms unfolding classified_execution_with_current_supplies_def extends_tariff_archive_def by blast

lemma a_session_cannot_open_with_an_unissued_tariff:
  assumes "supplied_versions (supplies 0) version = None"
  shows "\<not> classified_execution_with_current_supplies features path version epoch supplies carrier p events q"
  using assms by (simp add: classified_execution_with_current_supplies_def)

lemma a_current_supply_cannot_drop_an_unapplied_routing_grant:
  assumes "indexed_product_step supplies (i,p) command reply (j,q)"
    "(change,epoch,boundary) \<in> supplied_routing_grants (supplies i)"
    "route_epoch (source_recovery q) < epoch"
  shows "(change,epoch,boundary) \<in> supplied_routing_grants (supplies j)"
  using assms by (auto simp: indexed_product_step_def review_routing_approvals_def
    outstanding_routing_grants_def Let_def split: if_splits)

lemma a_changed_routing_supply_has_passed_approval_before_it_can_be_used:
  assumes step: "indexed_product_step supplies (i,p) command reply (j,q)"
    and changed: "supplied_routing_grants (supplies i) \<noteq> supplied_routing_grants (supplies j)"
  shows "valid_routing_approval_plan (source_recovery q) (supplied_routing_grants (supplies j)) (supplied_routing_plan (supplies j))"
  using assms by (auto simp: indexed_product_step_def review_routing_approvals_def Let_def split: if_splits)

lemma a_newly_issued_route_cannot_be_backdated_behind_processed_work:
  assumes "(change,epoch,boundary) \<in> supplied_routing_grants (supplies j) - supplied_routing_grants (supplies i)"
    "boundary \<le> consensus_now (source_consensus q)"
  shows "\<not> indexed_product_step supplies (i,p) command reply (j,q)"
proof
  assume step: "indexed_product_step supplies (i,p) command reply (j,q)"
  let ?old = "supplied_routing_grants (supplies i)"
  let ?new = "supplied_routing_grants (supplies j)"
  let ?root = "consensus_now (source_consensus q)"
  have different: "?new \<noteq> ?old" using assms(1) by auto
  have review: "review_routing_approvals (source_recovery q) ?root ?old ?new (supplied_routing_plan (supplies j)) =
    (?new,Routing_Approvals_Accepted)"
    using step different unfolding indexed_product_step_def
    by (simp only: prod.case Let_def) blast
  have later: "\<forall>entry\<in>?new - ?old. ?root < snd (snd entry)"
    using an_accepted_approval_checks_the_whole_order_and_keeps_outstanding_grants[OF review]
    unfolding new_routing_grants_are_prospective_def by blast
  have "?root < snd (snd (change,epoch,boundary))"
    by (rule bspec[OF later assms(1)])
  then show False using assms(2) by simp
qed

lemma a_classified_trace_replays_the_original_public_bill_at_every_later_input:
  assumes run: "classified_execution_with_current_supplies features path version epoch supplies carrier p events q"
    and within: "j \<le> length events"
  shows "public_session_bill precision (supplied_versions (supplies j)) session
      (map usage_row_for_epoch (lifecycle_invoice (source_lifecycle p))) =
    Some (full_session_usage precision session (lifecycle_invoice (source_lifecycle p)))"
proof -
  have prior: "tariffs_cover_recorded_usage (supplied_versions (supplies 0)) (source_lifecycle p)"
    using run unfolding classified_execution_with_current_supplies_def by blast
  have updates: "extends_tariff_archive (supplied_versions (supplies i)) (supplied_versions (supplies (Suc i)))"
    if "i < length events" for i
    using run that unfolding classified_execution_with_current_supplies_def by blast
  have from_start: "(0::nat) \<le> j" by (rule le0)
  have archived: "extends_tariff_archive (supplied_versions (supplies 0)) (supplied_versions (supplies j))"
    by (rule successive_updates_keep_all_previously_issued_tariffs[where versions="\<lambda>i. supplied_versions (supplies i)"
          and limit="length events", OF updates from_start within])
  have prices: "\<forall>row \<in> set (lifecycle_invoice (source_lifecycle p)).
    supplied_versions (supplies j) (accounted_tariff row) = Some (accounted_schedule row)"
    using prior archived unfolding tariffs_cover_recorded_usage_def extends_tariff_archive_def by blast
  show ?thesis by (rule public_epoch_log_reconstructs_a_session_bill[OF prices])
qed

end

abbreviation classified_genesis where
  "classified_genesis \<equiv> with_finality_core finality_sample_initial joined_initial"

abbreviation first_unpublished_recovery where
  "first_unpublished_recovery \<equiv> \<lparr>active_domains = {0,2,4}, route_epoch = 1, primary_record = 0,
    primary_sequence = 0, source_ready = False, replica = (\<lambda>_. 0), work_owner = Map.empty,
    completion_log = {}, irreversible_facts = image prod_encode (core_published (credit_core (current_operational classified_genesis))),
    rollback_incomplete = False\<rparr>"

abbreviation classified_first_state where
  "classified_first_state \<equiv> \<lparr>source_lifecycle = episode_initial\<lparr>lifecycle_cutover := degree_state (current_operational classified_genesis),
      lifecycle_registry := authority_registry classified_genesis, lifecycle_tariff := 3\<rparr>,
    source_consensus = classified_genesis,
    source_recovery = first_unpublished_recovery, observed_divergence_work = {}\<rparr>"

lemma the_actual_registry_seed_consumes_the_first_matching_classification:
  "applies_classified_registry two_conditions_asset Atomic 3 11 classified_first_state"
  "\<not> applies_classified_registry only_rate Atomic 3 11 classified_first_state"
  by (simp_all add: applies_classified_registry_def registered_metadata_follows_all_decided_tvo_branches
    initial_registry_record_def tvo_required_level_def observation_metadata_def quiet_asset_def coupling_ticket_def
    joined_initial_def cycle_fixture_def meter_fixture_def episode_initial_def Let_def recorded_success_history_def
    with_finality_core_def with_operational_state_def finality_sample_initial_def initial_finality_core_def
    initial_reservation_machine_def initial_reservation_state_def recovery_carrier_def pending_ids_def replica_covered_def)

end
