theory Reference_Witness_Selection
  imports "Reference_Product_Image"
begin

record 'control reference_witness_cut =
  witness_version :: nat
  witness_generation :: nat
  witness_control :: 'control

record ('control, 'archive) reference_witness_proposal =
  proposal_before :: "'control reference_witness_cut"
  proposal_after :: "'control reference_witness_cut"
  proposal_archive :: 'archive

definition witnessed_selection where
  "witnessed_selection archive_bound archives proposal current =
    (if proposal_before proposal = current \<and>
         witness_version (proposal_after proposal) = Suc (witness_version current) \<and>
         witness_generation current \<le> witness_generation (proposal_after proposal) \<and>
         proposal_archive proposal \<in> archives \<and>
         archive_bound (proposal_archive proposal) (proposal_after proposal)
     then Some (proposal_after proposal) else None)"

definition witnessed_current where
  "witnessed_current archive_bound archives recovered observed =
    (if recovered = observed \<and> (\<exists>archive \<in> archives. archive_bound archive observed)
     then Some (witness_control observed) else None)"

definition prepared_mirror_agrees where
  "prepared_mirror_agrees mirrored prepared selected \<longleftrightarrow>
    mirrored = Some selected \<or> (\<exists>proposal \<in> prepared. proposal_after proposal = selected)"

definition current_through_authority_mirror where
  "current_through_authority_mirror archive_bound archives recovered observed mirrored prepared =
    (if prepared_mirror_agrees mirrored prepared observed
     then witnessed_current archive_bound archives recovered observed else None)"

theorem a_selection_requires_the_exact_current_cut_and_durable_archive:
  assumes "witnessed_selection archive_bound archives proposal current = Some selected"
  shows "proposal_before proposal = current"
    "selected = proposal_after proposal"
    "witness_version selected = Suc (witness_version current)"
    "witness_generation current \<le> witness_generation selected"
    "proposal_archive proposal \<in> archives"
    "archive_bound (proposal_archive proposal) selected"
  using assms by (auto simp: witnessed_selection_def split: if_splits)

theorem an_old_publication_proposal_cannot_overwrite_the_selected_control:
  assumes "witnessed_selection archive_bound archives first before = Some selected"
    and "proposal_before stale = before"
  shows "witnessed_selection archive_bound later_archives stale selected = None"
proof -
  have "witness_version selected = Suc (witness_version before)"
    by (rule a_selection_requires_the_exact_current_cut_and_durable_archive(3)[OF assms(1)])
  then have "selected \<noteq> before" by auto
  then show ?thesis using assms(2) by (simp add: witnessed_selection_def)
qed

theorem readback_and_repair_depend_on_the_independently_selected_control:
  assumes "witnessed_current archive_bound archives recovered observed = Some reported"
  shows "recovered = observed" "reported = witness_control observed"
    "\<exists>archive \<in> archives. archive_bound archive observed"
  using assms by (auto simp: witnessed_current_def split: if_splits)

lemma primary_rollback_and_missing_archive_keep_authority_unavailable:
  assumes "recovered \<noteq> observed \<or> (\<forall>archive \<in> archives. \<not> archive_bound archive observed)"
  shows "witnessed_current archive_bound archives recovered observed = None"
  using assms by (auto simp: witnessed_current_def)

lemma an_exact_preparation_can_recover_a_selected_cut_after_mirror_loss:
  assumes "witnessed_selection archive_bound archives proposal before = Some selected"
    "proposal \<in> prepared"
  shows "current_through_authority_mirror archive_bound archives selected selected None prepared =
    Some (witness_control selected)"
  using a_selection_requires_the_exact_current_cut_and_durable_archive[OF assms(1)] assms(2)
  by (auto simp: current_through_authority_mirror_def prepared_mirror_agrees_def witnessed_current_def)

lemma a_primary_preparation_alone_cannot_release_an_unselected_result:
  assumes "proposal_after proposal \<noteq> observed"
  shows "current_through_authority_mirror archive_bound archives (proposal_after proposal) observed mirrored prepared = None"
  using assms by (simp add: current_through_authority_mirror_def witnessed_current_def)

definition witnessed_reference_debit where
  "witnessed_reference_debit archive_bound archives archive observed frame request candidate_head after_authority current_witness =
    (let selected_frame = commit_reference_debit observed frame request candidate_head after_authority;
         version = Suc (witness_version current_witness);
         selected = current_witness\<lparr>witness_version := version, witness_control := selected_frame\<rparr>;
         proposal = \<lparr>proposal_before = current_witness, proposal_after = selected, proposal_archive = archive\<rparr>
     in if witness_control current_witness = frame \<and> selected_frame \<noteq> frame
        then witnessed_selection archive_bound archives proposal current_witness else None)"

lemma a_prior_authority_change_defeats_a_stale_signed_debit_at_the_witness:
  assumes "observed \<noteq> image_ordered_control frame"
  shows "witnessed_reference_debit archive_bound archives archive observed frame request head authority current_witness = None"
  using a_stale_control_observation_preserves_the_entire_reference_image[OF assms]
  by (simp add: witnessed_reference_debit_def Let_def)

theorem witnessed_debit_selects_the_exact_image_for_a_later_readback:
  assumes selected: "witnessed_reference_debit archive_bound archives archive observed frame request head authority current_witness = Some latest"
    and observed: "observed = image_ordered_control frame"
    and pending: "control_decisions observed (original_call request) = Some (request, Ref_Pending)"
    and decoded: "decode_wire_packet (original_packet request) = Some packet"
  shows "control_head (image_ordered_control (witness_control latest)) = Some head"
    "image_authority (witness_control latest) = authority"
    "reference_image_views_agree (witness_control latest)"
    "image_transport (witness_control latest) (original_transport request) = Some (encode_wire_core (packet_core packet))"
    "witnessed_current archive_bound archives latest latest = Some (witness_control latest)"
proof -
  have frame: "witness_control latest = commit_reference_debit observed frame request head authority"
    and archive: "archive \<in> archives" "archive_bound archive latest"
    using selected by (auto simp: witnessed_reference_debit_def witnessed_selection_def Let_def split: if_splits)
  have effects: "let after = commit_reference_debit observed frame request head authority in
      control_head (image_ordered_control after) = Some head \<and> image_authority after = authority \<and>
      reference_image_views_agree after \<and>
      image_transport after (original_transport request) = Some (encode_wire_core (packet_core packet))"
    by (rule an_ordered_debit_publishes_the_exact_input_and_product_view_together[OF observed pending decoded])
  show "control_head (image_ordered_control (witness_control latest)) = Some head"
    "image_authority (witness_control latest) = authority"
    "reference_image_views_agree (witness_control latest)"
    "image_transport (witness_control latest) (original_transport request) = Some (encode_wire_core (packet_core packet))"
    using effects by (simp_all add: frame Let_def)
  show "witnessed_current archive_bound archives latest latest = Some (witness_control latest)"
    using archive by (auto simp: witnessed_current_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms a_selection_requires_the_exact_current_cut_and_durable_archive
      an_old_publication_proposal_cannot_overwrite_the_selected_control
      readback_and_repair_depend_on_the_independently_selected_control
      primary_rollback_and_missing_archive_keep_authority_unavailable
      an_exact_preparation_can_recover_a_selected_cut_after_mirror_loss
      a_primary_preparation_alone_cannot_release_an_unselected_result
      a_prior_authority_change_defeats_a_stale_signed_debit_at_the_witness
      witnessed_debit_selects_the_exact_image_for_a_later_readback})
  then () else error "Unexpected oracle in independent reference witness selection"
\<close>

end
