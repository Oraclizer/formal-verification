theory DOSP_Source_Defense
  imports DOSP_Commit_Defense DOSP_Views.Recovery_Observations DOSP_Quiet_Run_Comparison.Quiet_Run_Comparison
begin

record recovery_head =
  head_issuer :: nat
  head_route_epoch :: nat
  head_sequence :: nat
  head_key :: source_key

type_synonym available_journals = "nat \<Rightarrow> integrated_journal option"
type_synonym recovery_offer = "nat \<times> integrated_recovery_candidate"

context integrated_dosp_authority
begin

text \<open>The authenticated head is supplied separately from the received
  offers. Issuance counters belong to their respective publishers.\<close>

definition select_current_publication ::
  "available_journals \<Rightarrow> recovery_head \<Rightarrow> recovery_offer list \<Rightarrow>
    nat \<Rightarrow> (eab_primary_authority \<times> eab_primary_receipt) option" where
  "select_current_publication sources head offers epoch =
    (if head_route_epoch head \<noteq> epoch then None
     else case sources (head_issuer head) of
       None \<Rightarrow> None
     | Some original \<Rightarrow>
         (let live = call_authority_state original
          in if (\<exists>candidate. (head_issuer head, candidate) \<in> set offers \<and>
                journal.checked_current_replay original candidate = Some live)
             then case issued_receipt live (head_sequence head) of
                 None \<Rightarrow> None
               | Some receipt \<Rightarrow>
                   (if published_key receipt = head_key head then Some (current_publication_authority live, receipt)
                    else None)
             else None))"

lemma order_of_delivery_is_not_an_authority_decision:
  assumes "set left = set right"
  shows "select_current_publication sources head left epoch = select_current_publication sources head right epoch"
  unfolding select_current_publication_def assms by (rule refl)

lemma success_requires_the_current_issuer_and_replay:
  assumes "select_current_publication sources head offers epoch = Some (authority, receipt)"
  shows "head_route_epoch head = epoch \<and>
    (\<exists>original candidate.
       sources (head_issuer head) = Some original \<and>
       (head_issuer head, candidate) \<in> set offers \<and>
       journal.checked_current_replay original candidate = Some (call_authority_state original) \<and>
       authority = current_publication_authority (call_authority_state original) \<and>
       issued_receipt (call_authority_state original) (head_sequence head) = Some receipt \<and>
       published_key receipt = head_key head)"
  using assms
  by (auto simp: select_current_publication_def Let_def split: option.splits if_splits)

lemma an_offer_from_another_issuer_is_not_a_substitute:
  assumes "\<And>candidate. (head_issuer head,candidate) \<notin> set offers"
  shows "select_current_publication sources head offers epoch = None"
proof (cases "select_current_publication sources head offers epoch")
  case None
  then show ?thesis .
next
  case (Some selected)
  obtain authority receipt where selected: "selected = (authority, receipt)" by (cases selected) auto
  from Some[unfolded selected] have match:
    "\<exists>candidate. (head_issuer head, candidate) \<in> set offers"
    using success_requires_the_current_issuer_and_replay by blast
  then show ?thesis using assms by blast
qed

definition offered_recovery_step ::
  "available_journals \<Rightarrow> recovery_head \<Rightarrow> recovery_offer list \<Rightarrow> nat routing_grants \<Rightarrow> nat set
    \<Rightarrow> (nat recovery_state, nat repair_action, nat repair_result) step_rel" where
  "offered_recovery_step sources head offers grants governance s action reply t \<longleftrightarrow>
    (if replica_repair action then
       case select_current_publication sources head offers (route_epoch s) of
         None \<Rightarrow> reply = transition_result.Operational_Failure Evidence_Unavailable \<and> t = s
       | Some (authority, receipt) \<Rightarrow> receipt_repair_step grants governance authority receipt s action reply t
     else recovery_step grants governance s action reply t)"

lemma an_outdated_head_cannot_install:
  assumes "head_route_epoch head \<noteq> route_epoch s"
  shows "offered_recovery_step sources head offers grants governance s (Apply_Repair job sequence)
    (transition_result.Operational_Failure Evidence_Unavailable) s"
    "\<not> offered_recovery_step sources head offers grants governance s (Apply_Repair job sequence)
    (transition_result.Accepted (Installed job domain sequence)) t"
  using assms by (simp_all add: offered_recovery_step_def select_current_publication_def)

lemma sourced_repair_preserves_irreversibility:
  "offered_recovery_step sources head offers grants governance s action reply t
    \<Longrightarrow> irreversible_facts t = irreversible_facts s"
  by (cases action)
     (auto simp: offered_recovery_step_def receipt_repair_step_def
       split: if_splits option.splits prod.splits route_change.splits dest: recovery_never_changes_irreversible_facts)

lemma an_offered_leave_preserves_the_actual_handed_off_job:
  assumes left: "offered_recovery_step sources head offers grants governance s
    (Activate (Leave_Domain old successor) epoch boundary time)
    (transition_result.Accepted (Left old successor)) t"
    and pending: "work_owner s job = Some old"
  shows "work_owner t job = Some successor"
proof -
  have actual: "recovery_step grants governance s (Activate (Leave_Domain old successor) epoch boundary time)
    (transition_result.Accepted (Left old successor)) t"
    using left by (simp add: offered_recovery_step_def)
  show ?thesis using leave_transports_work[OF actual] pending by blast
qed

definition verified_job_ready ::
  "available_journals \<Rightarrow> recovery_head \<Rightarrow> recovery_offer list \<Rightarrow>
    nat recovery_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "verified_job_ready sources head offers s job domain sequence \<longleftrightarrow>
    (\<exists>authority receipt.
      select_current_publication sources head offers (route_epoch s) = Some (authority, receipt) \<and>
      primary_receipt_matches authority receipt s) \<and>
    work_owner s job = Some domain \<and> domain \<in> active_domains s \<and> source_ready s \<and>
    sequence = primary_sequence s \<and> \<not> rollback_incomplete s"

lemma a_ready_chosen_installation_actually_finishes_its_job:
  assumes "verified_job_ready sources head offers s job domain sequence"
    "offered_recovery_step sources head offers grants governance s (Apply_Repair job sequence) reply t"
  shows "reply = transition_result.Accepted (Installed job domain sequence) \<and> t = install_replica s job domain"
proof -
  obtain authority receipt where selected:
    "select_current_publication sources head offers (route_epoch s) = Some (authority, receipt)"
    and matches: "primary_receipt_matches authority receipt s"
    and owner: "work_owner s job = Some domain"
    using assms(1) by (auto simp: verified_job_ready_def)
  have actual: "recovery_step grants governance s (Apply_Repair job sequence) reply t"
    using assms(2) selected matches by (simp add: offered_recovery_step_def receipt_repair_step_def)
  then show ?thesis using owner by (cases rule: recovery_step.cases) auto
qed

lemma ready_job_can_install:
  assumes "verified_job_ready sources head offers s job domain sequence"
  shows "offered_recovery_step sources head offers grants governance s (Apply_Repair job sequence)
    (transition_result.Accepted (Installed job domain sequence)) (install_replica s job domain)"
proof -
  obtain authority receipt where selected:
    "select_current_publication sources head offers (route_epoch s) = Some (authority, receipt)"
    and matches: "primary_receipt_matches authority receipt s"
    using assms by (auto simp: verified_job_ready_def)
  have actual: "recovery_step grants governance s (Apply_Repair job sequence)
     (transition_result.Accepted (Installed job domain sequence)) (install_replica s job domain)"
    using assms by (auto simp: verified_job_ready_def intro: recovery_step.Ordinary_Repair)
  show ?thesis using selected matches actual by (simp add: offered_recovery_step_def receipt_repair_step_def)
qed

end

definition other_publisher_journal :: integrated_journal where
  "other_publisher_journal =
    joined_dosp.journal.run_calls (integrated_call_program 99 0 [Inl first_meter])
      (initial_call_machine joined_initial)"

lemma other_publisher_really_runs_the_first_credit:
  "call_authority_state other_publisher_journal = after_first_meter"
proof -
  have ready: "source_call_ready 99 0 (initial_call_machine joined_initial)" by simp
  show ?thesis unfolding other_publisher_journal_def
    using joined_dosp.integrated_event_program_uses_the_actual_journal_callbacks[OF ready, of "[Inl first_meter]"]
    by (simp only: joined_dosp.run_integrated_events.simps initial_call_machine_def
        durable_call_machine.select_convs after_first_meter_def)
qed

lemma publishers_have_different_actual_histories:
  "next_publication_sequence (call_authority_state other_publisher_journal) = 51"
  "next_publication_sequence (call_authority_state actual_metering_journal) = 52"
  "other_publisher_journal \<noteq> actual_metering_journal"
proof -
  show first: "next_publication_sequence (call_authority_state other_publisher_journal) = 51"
    by (simp add: other_publisher_really_runs_the_first_credit after_first_meter_shape(1))
  show second: "next_publication_sequence (call_authority_state actual_metering_journal) = 52"
    by (rule the_same_asset_was_metered_and_published_on_both_sides_of_promotion(5))
  show "other_publisher_journal \<noteq> actual_metering_journal" using first second by auto
qed

definition two_journals :: available_journals where
  "two_journals = Map.empty(41 \<mapsto> other_publisher_journal, 52 \<mapsto> actual_metering_journal)"

definition current_repair_head :: recovery_head where
  "current_repair_head = \<lparr>head_issuer = 52, head_route_epoch = 3, head_sequence = 51, head_key = (0,23)\<rparr>"

abbreviation prior_offer :: recovery_offer where
  "prior_offer \<equiv> (41, current_source_candidate other_publisher_journal)"

abbreviation live_offer :: recovery_offer where
  "live_offer \<equiv> (52, current_source_candidate actual_metering_journal)"

lemma current_source_chosen_from_two_actual_histories:
  "joined_dosp.select_current_publication two_journals current_repair_head [prior_offer, live_offer] 3 =
    Some (current_publication_authority actual_authority, issued_second_receipt)"
  "joined_dosp.select_current_publication two_journals current_repair_head [live_offer, prior_offer] 3 =
    Some (current_publication_authority actual_authority, issued_second_receipt)"
  "joined_dosp.select_current_publication two_journals current_repair_head [prior_offer] 3 = None"
  "joined_dosp.select_current_publication two_journals current_repair_head
    [(52, current_source_candidate other_publisher_journal)] 2 = None"
  by (simp_all add: joined_dosp.select_current_publication_def two_journals_def current_repair_head_def
      replay_of_the_metered_journal actual_publication_fields(2) issued_second_receipt_def Let_def)

end
