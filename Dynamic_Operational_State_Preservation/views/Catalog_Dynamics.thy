theory Catalog_Dynamics
  imports DOSP_Recovery.Recovery_Examples
begin

definition empty_catalogue :: catalog where
  "empty_catalogue =
    \<lparr>mirrors = {1,2}, releases = {}, tombstones = {}, raw_contents = (\<lambda>_. {}),
      catalogue_pending = {}, catalogue_done = {}, host = id\<rparr>"

definition queued_copies :: "copy_key set" where
  "queued_copies = {(1,one_release), (2,one_release)}"

definition distributed :: catalog where
  "distributed = empty_catalogue\<lparr>releases := insert one_release (releases empty_catalogue),
    catalogue_pending := catalogue_pending empty_catalogue \<union> queued_copies\<rparr>"

definition replicated :: catalog where
  "replicated = (record_copy distributed (2,one_release))
    \<lparr>raw_contents := (raw_contents distributed)(2 := insert one_release (raw_contents distributed 2))\<rparr>"

definition withdrawn :: catalog where
  "withdrawn = replicated\<lparr>tombstones := insert one_release (tombstones replicated)\<rparr>"

definition remapped :: catalog where
  "remapped = withdrawn\<lparr>mirrors := mirrors withdrawn - {1},
    host := (\<lambda>slot. if host withdrawn slot = 1 then 2 else host withdrawn slot)\<rparr>"

definition clean_mirror :: catalog where
  "clean_mirror = (record_copy remapped (1,one_release))
    \<lparr>raw_contents := (raw_contents remapped)(2 := raw_contents remapped 2 - {one_release})\<rparr>"

lemma accepted_publication_admits_two_jobs:
  "catalogue_step empty_catalogue (Publish one_release) (Accepted (Published queued_copies)) distributed"
  unfolding distributed_def
  by (rule catalogue_step.Publish_To_Mirrors)
     (auto simp: queued_copies_def fresh_copies_def empty_catalogue_def)

lemma replica_genuinely_copied:
  "catalogue_step distributed (Copy (2,one_release)) (Accepted (Copied (2,one_release))) replicated"
  unfolding replicated_def
  by (rule catalogue_step.Reproduce_Release)
     (simp_all add: distributed_def queued_copies_def empty_catalogue_def)

lemma publisher_withdraws:
  "catalogue_step replicated (Withdraw one_release) (Accepted (Withdrawn one_release)) withdrawn"
  unfolding withdrawn_def
  by (rule catalogue_step.Withdraw_Release)
     (simp add: replicated_def record_copy_def distributed_def empty_catalogue_def)

lemma physical_mirror_is_retired:
  "catalogue_step withdrawn (Disconnect 1 2) (Accepted (Disconnected 1)) remapped"
  unfolding remapped_def
  by (rule catalogue_step.Disconnect_Mirror)
     (simp_all add: withdrawn_def replicated_def record_copy_def distributed_def empty_catalogue_def)

lemma transferred_withdrawal_is_executed_at_current_host:
  "catalogue_step remapped (Copy (1,one_release)) (Accepted (Withdrew_From_Mirror (1,one_release))) clean_mirror"
  unfolding clean_mirror_def
  by (rule catalogue_step.Propagate_Withdrawal)
     (simp_all add: remapped_def withdrawn_def replicated_def record_copy_def distributed_def queued_copies_def empty_catalogue_def)

theorem publish_withdraw_handoff_and_cleanup:
  "finite_trace catalogue_step catalogue_carrier empty_catalogue
    [mk_event empty_catalogue (Publish one_release) (Accepted (Published queued_copies)) distributed,
     mk_event distributed (Copy (2,one_release)) (Accepted (Copied (2,one_release))) replicated,
     mk_event replicated (Withdraw one_release) (Accepted (Withdrawn one_release)) withdrawn,
     mk_event withdrawn (Disconnect 1 2) (Accepted (Disconnected 1)) remapped,
     mk_event remapped (Copy (1,one_release)) (Accepted (Withdrew_From_Mirror (1,one_release))) clean_mirror]
    clean_mirror \<and>
    catalogue_pending clean_mirror = {} \<and>
    catalogue_done clean_mirror = queued_copies \<and>
    one_release \<in> raw_contents remapped 2 \<and> one_release \<notin> raw_contents clean_mirror 2"
  using accepted_publication_admits_two_jobs replica_genuinely_copied publisher_withdraws
    physical_mirror_is_retired transferred_withdrawal_is_executed_at_current_host
  by (auto simp: step_occurs_def mk_event_def catalogue_carrier_def empty_catalogue_def distributed_def
    queued_copies_def replicated_def withdrawn_def remapped_def clean_mirror_def record_copy_def)

end
