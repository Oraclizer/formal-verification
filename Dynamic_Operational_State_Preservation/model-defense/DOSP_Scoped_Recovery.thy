theory DOSP_Scoped_Recovery
  imports DOSP_Integrated_Defense
begin

datatype governance_verb = Execute_Resolution | Change_Resolution_Parameter | Other_Governance

record resync_approval =
  approval_id :: nat
  approval_authority :: nat
  approval_verb :: governance_verb
  approval_asset :: "nat option"
  approval_route_epoch :: nat
  approval_work :: nat
  approval_sequence :: nat

definition resync_permitted where
  "resync_permitted authorized_issuers confirmed asset s approval job sequence \<longleftrightarrow>
    approval \<in> confirmed \<and> approval_authority approval \<in> authorized_issuers \<and>
    approval_verb approval \<in> {Execute_Resolution, Change_Resolution_Parameter} \<and>
    approval_asset approval = Some asset \<and> approval_route_epoch approval = route_epoch s \<and>
    approval_work approval = job \<and> approval_sequence approval = sequence"

context integrated_dosp_authority
begin

definition consensus_membership_step where
  "consensus_membership_step a sources head offers grants s change epoch boundary reply t \<longleftrightarrow>
    offered_recovery_step sources head offers grants {} s
      (Activate change epoch boundary (consensus_now a)) reply t"

definition selected_asset where
  "selected_asset sources head offers s =
    map_option (\<lambda>(_,receipt). binding_asset (published_binding receipt))
      (select_current_publication sources head offers (route_epoch s))"

definition scoped_resync where
  "scoped_resync authorities confirmed asset sources head offers grants s approval job sequence reply t \<longleftrightarrow>
    (if resync_permitted authorities confirmed asset s approval job sequence then
       (let repair = offered_recovery_step sources head offers grants {approval_id approval} s
           (Governance_Resync (approval_id approval) job sequence)
        in if selected_asset sources head offers s = Some asset \<and> (\<exists>outcome updated. repair outcome updated)
           then repair reply t
           else reply = transition_result.Operational_Failure Evidence_Unavailable \<and> t = s)
     else reply = transition_result.Rejected Recovery_Blocks_Trade \<and> t = s)"

lemma mismatched_authority_or_asset_rejects_the_governance_command:
  assumes "approval_asset approval \<noteq> Some asset \<or> approval_authority approval \<notin> authorities"
  shows "scoped_resync authorities confirmed asset sources head offers grants s approval job sequence reply t
    \<longleftrightarrow> reply = transition_result.Rejected Recovery_Blocks_Trade \<and> t = s"
  using assms by (auto simp: scoped_resync_def resync_permitted_def)

lemma accepted_governance_requires_the_exact_scope_and_preserves_irreversibility:
  assumes "scoped_resync authorities confirmed asset sources head offers grants s approval job sequence
    (transition_result.Accepted (Installed job d sequence)) t"
  shows "resync_permitted authorities confirmed asset s approval job sequence \<and>
    selected_asset sources head offers s = Some asset \<and> irreversible_facts t = irreversible_facts s"
  using assms by (auto simp: scoped_resync_def Let_def split: if_splits dest: sourced_repair_preserves_irreversibility)

lemma ready_scoped_governance_can_install:
  assumes scope: "resync_permitted authorities confirmed asset s approval job sequence"
    and selected: "select_current_publication sources head offers (route_epoch s) = Some (authority, receipt)"
    and asset: "binding_asset (published_binding receipt) = asset"
    and matches: "primary_receipt_matches authority receipt s"
    and owner: "work_owner s job = Some d" and member: "d \<in> active_domains s"
    and ready: "source_ready s" and rollback: "rollback_incomplete s" and exact: "sequence = primary_sequence s"
  shows "scoped_resync authorities confirmed asset sources head offers grants s approval job sequence
    (transition_result.Accepted (Installed job d sequence))
    ((install_replica s job d)\<lparr>rollback_incomplete := pending_ids (install_replica s job d) \<noteq> {}\<rparr>)"
proof -
  have grant: "approval_id approval \<in> {approval_id approval}" by simp
  have actual_asset: "selected_asset sources head offers s = Some asset"
    using selected asset by (simp add: selected_asset_def)
  note repair = prepared_governance_repair_uses_the_verified_record[OF selected matches owner member ready rollback grant]
  show ?thesis unfolding scoped_resync_def Let_def using scope repair exact actual_asset by metis
qed

lemma projection_keeps_authenticated_recovery_when_it_keeps_the_current_issuer:
  assumes kept: "head_issuer head \<in> keep"
  shows "offered_recovery_step (\<lambda>issuer. if issuer \<in> keep then sources issuer else None) head
      (filter (\<lambda>offer. fst offer \<in> keep) offers) grants governance s action reply t =
    offered_recovery_step sources head offers grants governance s action reply t"
proof -
  have offered: "\<And>candidate. (head_issuer head,candidate) \<in> set (filter (\<lambda>offer. fst offer \<in> keep) offers) =
      ((head_issuer head,candidate) \<in> set offers)"
    using kept by simp
  have "select_current_publication (\<lambda>issuer. if issuer \<in> keep then sources issuer else None) head
      (filter (\<lambda>offer. fst offer \<in> keep) offers) (route_epoch s) =
      select_current_publication sources head offers (route_epoch s)"
    using kept by (cases "sources (head_issuer head)") (simp_all add: select_current_publication_def offered Let_def)
  then show ?thesis by (simp only: offered_recovery_step_def)
qed

lemma hiding_the_current_issuer_cannot_simulate_a_current_install:
  assumes hidden: "head_issuer head \<notin> keep"
  shows "offered_recovery_step (\<lambda>issuer. if issuer \<in> keep then sources issuer else None) head
      (filter (\<lambda>offer. fst offer \<in> keep) offers) grants governance s (Apply_Repair job sequence)
      (transition_result.Operational_Failure Evidence_Unavailable) s"
  using hidden by (simp add: offered_recovery_step_def select_current_publication_def)

end

lemma native_clock_is_consumed_at_the_membership_boundary:
  "joined_dosp.consensus_membership_step joined_initial two_journals current_repair_head []
    joined_recovery_grants noticed_recovery (Join_Domain 6 9) 2 86400
    (transition_result.Rejected Stale_Route) noticed_recovery"
  "joined_dosp.consensus_membership_step before_second_meter two_journals current_repair_head []
    joined_recovery_grants noticed_recovery (Join_Domain 6 9) 2 86400
    (transition_result.Accepted (Joined 6 9)) joined_recovery"
proof -
  have early: "consensus_now joined_initial = 86399" by (simp add: joined_initial_def)
  show "joined_dosp.consensus_membership_step joined_initial two_journals current_repair_head []
    joined_recovery_grants noticed_recovery (Join_Domain 6 9) 2 86400
    (transition_result.Rejected Stale_Route) noticed_recovery"
    unfolding joined_dosp.consensus_membership_step_def early by (rule membership_uses_the_consensus_boundary_and_current_grant(1))
  show "joined_dosp.consensus_membership_step before_second_meter two_journals current_repair_head []
    joined_recovery_grants noticed_recovery (Join_Domain 6 9) 2 86400
    (transition_result.Accepted (Joined 6 9)) joined_recovery"
    unfolding joined_dosp.consensus_membership_step_def second_meter_operational_fields(6)
    by (rule membership_uses_the_consensus_boundary_and_current_grant(3))
qed

definition resolution_for_job_eight :: resync_approval where
  "resolution_for_job_eight = \<lparr>approval_id = 90, approval_authority = 71, approval_verb = Execute_Resolution,
    approval_asset = Some 17, approval_route_epoch = 3, approval_work = 8, approval_sequence = 51\<rparr>"

abbreviation flagged_handoff where "flagged_handoff \<equiv> handed_off_recovery\<lparr>rollback_incomplete := True\<rparr>"
abbreviation wrong_asset_approval where "wrong_asset_approval \<equiv> resolution_for_job_eight\<lparr>approval_asset := Some 18\<rparr>"

lemma even_a_confirmed_other_asset_approval_cannot_resolve_the_job:
  "joined_dosp.scoped_resync {71} {wrong_asset_approval} 17 two_journals current_repair_head [live_offer]
    joined_recovery_grants flagged_handoff wrong_asset_approval 8 51
    (transition_result.Rejected Recovery_Blocks_Trade) flagged_handoff"
  by (simp add: joined_dosp.scoped_resync_def resync_permitted_def resolution_for_job_eight_def)

lemma exact_governance_can_resync_the_same_pending_job_and_leaves_the_other_pending:
  "joined_dosp.scoped_resync {71} {resolution_for_job_eight} 17 two_journals current_repair_head [prior_offer, live_offer]
     joined_recovery_grants flagged_handoff resolution_for_job_eight 8 51
     (transition_result.Accepted (Installed 8 6 51)) (after_job_eight\<lparr>rollback_incomplete := True\<rparr>)"
proof -
  have scope: "resync_permitted {71} {resolution_for_job_eight} 17 flagged_handoff resolution_for_job_eight 8 51"
    by (simp add: resync_permitted_def resolution_for_job_eight_def handoff_has_a_real_primary_and_current_epoch(1))
  have selected: "joined_dosp.select_current_publication two_journals current_repair_head [prior_offer,live_offer] (route_epoch flagged_handoff)
    = Some (current_publication_authority actual_authority, issued_second_receipt)"
    using current_source_chosen_from_two_actual_histories(1) by (simp add: handoff_has_a_real_primary_and_current_epoch(1))
  have matches: "primary_receipt_matches (current_publication_authority actual_authority) issued_second_receipt flagged_handoff"
    using handoff_has_a_real_primary_and_current_epoch(2) by (simp add: primary_receipt_matches_def)
  have asset: "binding_asset (published_binding issued_second_receipt) = 17"
    by (simp add: issued_second_receipt_def second_request_fields)
  have facts: "work_owner flagged_handoff 8 = Some 6" "6 \<in> active_domains flagged_handoff"
    "source_ready flagged_handoff" "rollback_incomplete flagged_handoff" "51 = primary_sequence flagged_handoff"
    by (simp_all add: handed_off_recovery_def joined_recovery_def noticed_recovery_def published_recovery_state_def
      carry_owner_def actual_publication_fields issued_second_receipt_def Let_def)
  have waiting: "pending_ids after_job_eight \<noteq> {}"
    using the_joined_install_closes_only_its_own_job(3) by (auto simp: pending_ids_def)
  have installed: "install_replica flagged_handoff 8 6 = after_job_eight\<lparr>rollback_incomplete := True\<rparr>"
    by (simp add: install_replica_def)
  have waiting_flagged: "pending_ids (install_replica flagged_handoff 8 6) \<noteq> {}"
    using waiting by (simp add: installed pending_ids_def)
  have same: "(install_replica flagged_handoff 8 6)\<lparr>
      rollback_incomplete := pending_ids (install_replica flagged_handoff 8 6) \<noteq> {}\<rparr> =
    after_job_eight\<lparr>rollback_incomplete := True\<rparr>"
    using waiting_flagged by (simp add: installed)
  show ?thesis using joined_dosp.ready_scoped_governance_can_install[OF scope selected asset matches facts, where grants=joined_recovery_grants]
    by (simp only: same)
qed

lemma a_caller_cannot_select_another_assets_approval_scope:
  "joined_dosp.scoped_resync {71} {wrong_asset_approval} 18 two_journals current_repair_head [prior_offer, live_offer]
    joined_recovery_grants flagged_handoff wrong_asset_approval 8 51
    (transition_result.Operational_Failure Evidence_Unavailable) flagged_handoff"
  by (simp add: joined_dosp.scoped_resync_def joined_dosp.selected_asset_def resync_permitted_def
      resolution_for_job_eight_def handoff_has_a_real_primary_and_current_epoch(1)
      current_source_chosen_from_two_actual_histories(1) issued_second_receipt_def second_request_fields Let_def)

end
