theory Recovery_Boundary_Environment
  imports "Recovery_Boundary_Rollback"
begin

text \<open>These named environment premises separate complete-record flushing in the model from physical
  storage guarantees. Cryptographic use needs an execution-bounded collision assumption, not global
  injectivity. Witness freshness excludes witness restoration separately; generation zero excludes
  host reconfiguration.\<close>

definition records_are_at_their_own_addresses where
  "records_are_at_their_own_addresses digest disk \<longleftrightarrow>
    (\<forall>h record. flushed_records disk h = Some record \<longrightarrow> head_for_record digest record = h)"

locale recovery_address_environment =
  fixes digest :: "'digest persisted_commit \<Rightarrow> 'digest"
  assumes record_address_collision_free: "inj digest"
begin

lemma one_address_has_one_record:
  "head_for_record digest a = head_for_record digest b \<Longrightarrow> a = b"
  by (rule addressed_records_are_unique[OF record_address_collision_free])

lemma flushing_an_addressed_store_supplies_the_exact_candidate:
  assumes addressed: "records_are_at_their_own_addresses digest disk"
  shows "flushed_records (flush_commit_record digest record disk) (head_for_record digest record) = Some record"
proof (cases "flushed_records disk (head_for_record digest record)")
  case None
  then show ?thesis by (simp add: flush_commit_record_def Let_def)
next
  case (Some old)
  have same_head: "head_for_record digest old = head_for_record digest record"
    using addressed Some unfolding records_are_at_their_own_addresses_def by blast
  have same: "old = record" by (rule one_address_has_one_record[OF same_head])
  show ?thesis using Some same by (simp add: flush_commit_record_def Let_def)
qed

end

lemma complete_record_flush_keeps_address_correctness:
  assumes "records_are_at_their_own_addresses digest disk"
  shows "records_are_at_their_own_addresses digest (flush_commit_record digest record disk)"
  using assms by (auto simp: records_are_at_their_own_addresses_def flush_commit_record_def Let_def)

lemma head_publication_keeps_address_correctness:
  "records_are_at_their_own_addresses digest disk \<Longrightarrow>
    records_are_at_their_own_addresses digest (publish_recovery_head digest expected record disk)"
  by (simp add: records_are_at_their_own_addresses_def publish_recovery_head_def)

lemma genesis_has_correct_record_addresses:
  "records_are_at_their_own_addresses digest (genesis_disk digest profile R0)"
  by (auto simp: records_are_at_their_own_addresses_def genesis_disk_def)

lemma an_effective_disk_restore_requires_a_stopped_system:
  assumes "roll_back_disk_effect k s \<noteq> s"
  shows "sys_endpoint s = None \<and> sys_staged s = []"
  using assms by (auto simp: roll_back_disk_effect_def system_down_def split: if_splits)

lemma an_effective_witness_restore_requires_a_stopped_system:
  assumes "roll_back_witness_effect k s \<noteq> s"
  shows "sys_endpoint s = None \<and> sys_staged s = []"
  using assms by (auto simp: roll_back_witness_effect_def system_down_def split: if_splits)

lemma reopen_does_not_replace_an_existing_endpoint:
  "sys_endpoint s \<noteq> None \<Longrightarrow> reopen_effect digest profile attachment s = s"
  by (cases "sys_endpoint s") (simp_all add: reopen_effect_def)

lemma the_witness_archive_contains_only_real_flushed_records:
  "record \<in> flushed_archive digest disk \<Longrightarrow>
    flushed_records disk (head_for_record digest record) = Some record"
  by (simp add: flushed_archive_def)

lemma witness_record_binding_is_the_exact_control_head:
  "record_binds_cut digest record observed \<longleftrightarrow>
    head_for_record digest record = witness_control observed"
  by (simp add: record_binds_cut_def)

interpretation list_record_address_environment: recovery_address_environment list_digest
  by unfold_locales (rule list_digest_is_injective)

text \<open>The list-valued model inhabits the address premise. This interpretation is not a
  claim that a finite production digest is injective, and it supplies no physical durability or
  availability result. The existing boundary record has no request ghost field to remove.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms recovery_address_environment.one_address_has_one_record
      recovery_address_environment.flushing_an_addressed_store_supplies_the_exact_candidate
      complete_record_flush_keeps_address_correctness head_publication_keeps_address_correctness
      genesis_has_correct_record_addresses an_effective_disk_restore_requires_a_stopped_system
      an_effective_witness_restore_requires_a_stopped_system reopen_does_not_replace_an_existing_endpoint
      the_witness_archive_contains_only_real_flushed_records witness_record_binding_is_the_exact_control_head})
  then () else error "Unexpected oracle in named recovery environment"
\<close>

end
