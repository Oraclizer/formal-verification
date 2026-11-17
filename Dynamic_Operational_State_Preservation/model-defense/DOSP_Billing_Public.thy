theory DOSP_Billing_Public
  imports DOSP_Lifecycle_Defense_Cases
begin

record public_usage_row =
  public_session :: oracle_session_identity
  public_degree :: operational_level
  public_domain_count :: nat
  public_payload_units :: nat
  public_abort_cause :: "abort_responsibility option"
  public_meter_version :: nat
  public_billing_day :: nat

definition usage_row_for_epoch where
  "usage_row_for_epoch entry =
     (let base = payload_base (accounted_schedule entry)
      in \<lparr>public_session = accounted_session entry,
        public_degree = required_level (ticket_metadata (accounted_ticket entry)),
        public_domain_count = card (accounted_footprint entry),
        public_payload_units = (accounted_payload entry + (base - 1)) div base,
        public_abort_cause = accounted_abort entry, public_meter_version = accounted_tariff entry,
        public_billing_day = settlement_epoch entry\<rparr>)"

definition charge_from_public_row where
  "charge_from_public_row precision versions row =
    (case versions (public_meter_version row) of None \<Rightarrow> None | Some tariff \<Rightarrow>
      (let usage = degree_weight tariff (public_degree row) *
        (precision + fanout_slope tariff * (public_domain_count row - fanout_base tariff (public_degree row))) *
        public_payload_units row
       in Some (case public_abort_cause row of
           None \<Rightarrow> precision * usage
         | Some Client_Abort \<Rightarrow> failure_fraction tariff * usage
         | Some _ \<Rightarrow> 0)))"

lemma public_row_reconstructs_the_exact_private_charge:
  assumes "versions (accounted_tariff entry) = Some (accounted_schedule entry)"
  shows "charge_from_public_row precision versions (usage_row_for_epoch entry) = Some (charge_of precision entry)"
  using assms by (simp add: charge_from_public_row_def usage_row_for_epoch_def charge_of_def usage_units_def Let_def)

fun sum_public_rows :: "(public_usage_row \<Rightarrow> nat option) \<Rightarrow> public_usage_row list \<Rightarrow> nat option" where
  "sum_public_rows charge [] = Some 0"
| "sum_public_rows charge (row # rows) =
    (case (charge row, sum_public_rows charge rows) of (Some amount, Some remainder) \<Rightarrow> Some (amount + remainder)
     | _ \<Rightarrow> None)"

definition public_session_bill where
  "public_session_bill precision versions session log =
    map_option ((+) (precision * precision)) (sum_public_rows (charge_from_public_row precision versions)
      (filter (\<lambda>row. public_session row = session) log))"

definition publish_tariff where
  "publish_tariff versions version price =
    (if versions version = None then versions(version \<mapsto> price) else versions)"

definition extends_tariff_archive where
  "extends_tariff_archive old newer \<longleftrightarrow> (\<forall>version price. old version = Some price \<longrightarrow> newer version = Some price)"

definition tariffs_cover_recorded_usage where
  "tariffs_cover_recorded_usage versions s \<longleftrightarrow>
    (\<forall>row \<in> set (lifecycle_invoice s). versions (accounted_tariff row) = Some (accounted_schedule row))"

lemma stamping_consensus_time_preserves_the_recorded_tariffs [simp]:
  "tariffs_cover_recorded_usage versions (s\<lparr>lifecycle_clock := time\<rparr>) = tariffs_cover_recorded_usage versions s"
  by (simp add: tariffs_cover_recorded_usage_def)

lemma adding_a_new_tariff_extends_the_archive:
  "extends_tariff_archive versions (publish_tariff versions version price)"
  by (auto simp: extends_tariff_archive_def publish_tariff_def)

lemma successive_updates_keep_all_previously_issued_tariffs:
  assumes step: "\<And>k. k < limit \<Longrightarrow> extends_tariff_archive (versions k) (versions (Suc k))"
    and bounds: "i \<le> j" "j \<le> limit"
  shows "extends_tariff_archive (versions i) (versions j)"
  using bounds
proof (induction j)
  case 0
  then show ?case by (simp add: extends_tariff_archive_def)
next
  case (Suc j)
  show ?case
  proof (cases "i = Suc j")
    case True
    then show ?thesis by (simp add: extends_tariff_archive_def)
  next
    case False
    have prior: "extends_tariff_archive (versions i) (versions j)"
      using Suc.IH Suc.prems False by auto
    have current: "extends_tariff_archive (versions j) (versions (Suc j))"
      by (rule step) (use Suc.prems in simp)
    from prior current show ?thesis unfolding extends_tariff_archive_def by blast
  qed
qed

lemma an_archived_tariff_cannot_be_replaced:
  "versions version = Some price \<Longrightarrow> publish_tariff versions new_version new_price version = Some price"
  by (auto simp: publish_tariff_def)

lemma a_new_tariff_cannot_reprice_an_archived_session_bill:
  assumes tariffs: "\<forall>row \<in> set log. versions (public_meter_version row) \<noteq> None"
  shows "public_session_bill precision (publish_tariff versions version price) session log =
    public_session_bill precision versions session log"
proof -
  have same: "\<And>row. row \<in> set log \<Longrightarrow>
    charge_from_public_row precision (publish_tariff versions version price) row =
    charge_from_public_row precision versions row"
  proof -
    fix row assume "row \<in> set log"
    then obtain prior where prior: "versions (public_meter_version row) = Some prior"
      using tariffs by (cases "versions (public_meter_version row)") auto
    have archived: "publish_tariff versions version price (public_meter_version row) = Some prior"
      by (rule an_archived_tariff_cannot_be_replaced) (rule prior)
    from archived prior show
      "charge_from_public_row precision (publish_tariff versions version price) row =
        charge_from_public_row precision versions row"
      by (simp add: charge_from_public_row_def)
  qed
  have "sum_public_rows (charge_from_public_row precision (publish_tariff versions version price))
       (filter (\<lambda>row. public_session row = session) log) =
       sum_public_rows (charge_from_public_row precision versions) (filter (\<lambda>row. public_session row = session) log)"
    using same by (induction log) (auto split: option.splits)
  then show ?thesis by (simp add: public_session_bill_def)
qed

theorem public_epoch_log_reconstructs_a_session_bill:
  assumes tariffs: "\<forall>entry \<in> set history. versions (accounted_tariff entry) = Some (accounted_schedule entry)"
  shows "public_session_bill precision versions session (map usage_row_for_epoch history) =
    Some (full_session_usage precision session history)"
proof -
  have "sum_public_rows (charge_from_public_row precision versions)
       (filter (\<lambda>row. public_session row = session) (map usage_row_for_epoch history)) =
       Some (invoice_usage precision session history)"
    using tariffs
  proof (induction history)
    case Nil
    then show ?case by (simp add: invoice_usage_def)
  next
    case (Cons entry history)
    have prefix: "charge_from_public_row precision versions (usage_row_for_epoch entry) = Some (charge_of precision entry)"
      by (rule public_row_reconstructs_the_exact_private_charge) (use Cons.prems in auto)
    have session: "public_session (usage_row_for_epoch entry) = accounted_session entry"
      by (simp add: usage_row_for_epoch_def Let_def)
    from Cons show ?case using prefix session by (cases "accounted_session entry = session")
      (simp_all add: invoice_usage_def)
  qed
  then show ?thesis by (simp add: public_session_bill_def full_session_usage_def)
qed

lemma only_an_accepted_promotion_repins_the_session_tariff:
  assumes "lifecycle_step policy grants versions confirmed verified locks s command reply t"
  shows "lifecycle_session t = lifecycle_session s \<and> (if reply = Lifecycle_Promoted then
     (\<exists>epoch version. command = Promote_Cycle epoch version \<and> lifecycle_tariff t = version \<and>
       versions version \<noteq> None \<and> lifecycle_invoice t = lifecycle_invoice s \<and>
       lifecycle_registry t (fst (lifecycle_session s)) = Some (route_metadata (lifecycle_cutover t)))
    else lifecycle_tariff t = lifecycle_tariff s)"
  using assms by (cases rule: lifecycle_step.cases) (auto simp: finish_promotion_def)

lemma the_public_bill_keeps_the_old_rows_after_the_tariff_repin:
  "lifecycle_tariff episode_promoted = 5"
  "meter_version (route_metadata (lifecycle_cutover episode_promoted)) = 5"
  "public_session_bill 100 example_versions (17,7,3) (map usage_row_for_epoch (lifecycle_invoice episode_promoted)) = Some 20000"
  "public_session_bill 100 Map.empty (17,7,3) (map usage_row_for_epoch (lifecycle_invoice episode_promoted)) = None"
proof -
  show "lifecycle_tariff episode_promoted = 5" "meter_version (route_metadata (lifecycle_cutover episode_promoted)) = 5"
    by (simp_all add: episode_restored_def episode_initial_def promoted_metadata_def finish_promotion_def)
  have registry: "\<forall>entry \<in> set (lifecycle_invoice episode_promoted).
    example_versions (accounted_tariff entry) = Some (accounted_schedule entry)"
    by (simp add: historical_failed_attempt_survives_cutover_without_repricing(1)
      observed_failure_row_def example_versions_def)
  show "public_session_bill 100 example_versions (17,7,3) (map usage_row_for_epoch (lifecycle_invoice episode_promoted)) = Some 20000"
    using public_epoch_log_reconstructs_a_session_bill[OF registry, of 100 "(17,7,3)"]
      historical_failed_attempt_survives_cutover_without_repricing(2)
    by metis
  show "public_session_bill 100 Map.empty (17,7,3) (map usage_row_for_epoch (lifecycle_invoice episode_promoted)) = None"
    by (simp add: historical_failed_attempt_survives_cutover_without_repricing(1) public_session_bill_def
      observed_failure_row_def charge_from_public_row_def usage_row_for_epoch_def Let_def)
qed

end
