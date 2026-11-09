theory Sync_V061_Selection
  imports "OIP_Sync_V061_Position_Proofs.Sync_V061_Product_Proofs"
    "OIP_Reference_Profile.Reference_Witness_Selection"
begin

type_synonym ('key, 'product) sync_witness = "('key, 'product) sync_receiver reference_witness_cut"

record ('key, 'product) sync_archive =
  sync_archive_before :: "('key, 'product) sync_witness"
  sync_archive_after :: "('key, 'product) sync_witness"
  sync_archive_core :: wire_bytes
  sync_archive_reply :: sync_result

definition sync_prepare_record where
  "sync_prepare_record verify core observed =
    (let (state,reply) = sync_receive_verified verify core (witness_control observed) in
     if state = witness_control observed then None else
       Some \<lparr>sync_archive_before = observed,
         sync_archive_after = observed\<lparr>witness_version := Suc (witness_version observed), witness_control := state\<rparr>,
         sync_archive_core = encode_wire_core core, sync_archive_reply = reply\<rparr>)"

definition sync_archived_control where
  "sync_archived_control archive selected \<longleftrightarrow> sync_archive_after archive = selected"

definition sync_witness_proposal where
  "sync_witness_proposal archive =
    \<lparr>proposal_before = sync_archive_before archive,
     proposal_after = sync_archive_after archive, proposal_archive = archive\<rparr>"

definition sync_publish_record where
  "sync_publish_record verify core archives archive observed actual =
    (if sync_prepare_record verify core observed = Some archive
     then map_option (\<lambda>selected. (selected,sync_archive_reply archive))
       (witnessed_selection sync_archived_control archives (sync_witness_proposal archive) actual)
     else None)"

definition sync_reopen_selected where
  "sync_reopen_selected archives recovered observed =
    witnessed_current sync_archived_control archives recovered observed"

lemma sync_preparation_contains_exact_call_transition:
  assumes "sync_prepare_record verify core observed = Some archive"
  shows "sync_archive_before archive = observed"
    "sync_archive_core archive = encode_wire_core core"
    "sync_receive_verified verify core (witness_control observed) =
      (witness_control (sync_archive_after archive),sync_archive_reply archive)"
proof -
  obtain updated reply where transition:
    "sync_receive_verified verify core (witness_control observed) = (updated,reply)"
    by (cases "sync_receive_verified verify core (witness_control observed)") auto
  have exact: "archive =
    \<lparr>sync_archive_before = observed,
      sync_archive_after = observed\<lparr>witness_version := Suc (witness_version observed), witness_control := updated\<rparr>,
      sync_archive_core = encode_wire_core core, sync_archive_reply = reply\<rparr>"
    using assms transition by (auto simp: sync_prepare_record_def Let_def split: if_splits)
  show "sync_archive_before archive = observed" using exact by simp
  show "sync_archive_core archive = encode_wire_core core" using exact by simp
  show "sync_receive_verified verify core (witness_control observed) =
    (witness_control (sync_archive_after archive),sync_archive_reply archive)"
    using exact transition by simp
qed

theorem sync_published_reply_and_recovery_use_one_selected_record:
  assumes "sync_publish_record verify core archives archive observed actual = Some (selected,reply)"
  shows "observed = actual"
    "archive \<in> archives"
    "sync_archive_core archive = encode_wire_core core"
    "sync_receive_verified verify core (witness_control actual) = (witness_control selected,reply)"
    "sync_reopen_selected archives selected selected = Some (witness_control selected)"
proof -
  have prepared: "sync_prepare_record verify core observed = Some archive"
    and picked: "witnessed_selection sync_archived_control archives (sync_witness_proposal archive) actual = Some selected"
    and result: "reply = sync_archive_reply archive"
    using assms by (auto simp: sync_publish_record_def split: option.splits if_splits)
  note preparation = sync_preparation_contains_exact_call_transition[OF prepared]
  note selected = a_selection_requires_the_exact_current_cut_and_durable_archive[OF picked]
  show "observed = actual"
    using preparation(1) selected(1) by (simp add: sync_witness_proposal_def)
  show "archive \<in> archives"
    using selected(5) by (simp add: sync_witness_proposal_def)
  show "sync_archive_core archive = encode_wire_core core" by (rule preparation(2))
  show "sync_receive_verified verify core (witness_control actual) = (witness_control selected,reply)"
    using preparation(1,3) selected(1,2) result by (simp add: sync_witness_proposal_def)
  show "sync_reopen_selected archives selected selected = Some (witness_control selected)"
    using selected(5,6) by (auto simp: sync_witness_proposal_def sync_reopen_selected_def witnessed_current_def)
qed

lemma sync_unselected_or_unarchived_preparation_releases_no_new_reply:
  assumes "observed \<noteq> actual \<or> archive \<notin> archives"
  shows "sync_publish_record verify core archives archive observed actual = None"
proof (cases "sync_publish_record verify core archives archive observed actual")
  case None
  then show ?thesis .
next
  case (Some result)
  obtain selected reply where pair: "result = (selected,reply)" by (cases result) auto
  have published: "sync_publish_record verify core archives archive observed actual = Some (selected,reply)"
    using Some pair by simp
  show ?thesis using assms sync_published_reply_and_recovery_use_one_selected_record(1,2)[OF published] by blast
qed

lemma sync_reopen_cannot_use_a_rolled_back_authority:
  "recovered \<noteq> observed \<Longrightarrow> sync_reopen_selected archives recovered observed = None"
  by (simp add: sync_reopen_selected_def witnessed_current_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_preparation_contains_exact_call_transition
    sync_published_reply_and_recovery_use_one_selected_record
    sync_unselected_or_unarchived_preparation_releases_no_new_reply sync_reopen_cannot_use_a_rolled_back_authority})
  then () else error "Unexpected oracle in SyncCommitment durable selection"
\<close>

end
