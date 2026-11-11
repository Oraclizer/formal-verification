theory Schedule_Boundaries
  imports "OIP_Schedule_Product.Schedule_Product"
    "OIP_Query_Cache_Source_G0.Query_Cache_Source_G0"
    "OIP_Reference_Profile.Reference_Witness_Selection"
begin

text \<open>
  These are separately named conditional interfaces for the signed scheduler,
  ordered publication and independent archive selection. They do not turn the
  thirteen typed fixtures into signed ACK/Current packets. Current admission
  facts and replay equality must be obtained for the very same ordered batch,
  not borrowed from unrelated successful ACK or read tests. Cache composition
  imports the existing native Busy consumer and its source/profile binding;
  the reference cache fallback function is not substituted for that consumer.
\<close>

record sb_current_checks =
  sb_identity_matches :: bool
  sb_exact_packet_matches :: bool
  sb_current_admission :: bool
  sb_current_permissions :: bool
  sb_replay_replies_match :: bool

definition sb_checks_hold where
  "sb_checks_hold checks \<longleftrightarrow> sb_identity_matches checks \<and>
    sb_exact_packet_matches checks \<and> sb_current_admission checks \<and>
    sb_current_permissions checks \<and> sb_replay_replies_match checks"

definition sb_release where
  "sb_release checks observed current observed_checkpoint current_checkpoint prepared =
    (if sb_checks_hold checks \<and> observed_checkpoint = current_checkpoint
     then reference_schedule_release observed current prepared else None)"

theorem sb_released_replies_require_the_same_cut_checkpoint_and_current_checks:
  assumes released: "sb_release checks observed current observed_checkpoint current_checkpoint prepared = Some result"
  shows "observed = current" "observed_checkpoint = current_checkpoint"
    "sb_checks_hold checks" "result = prepared"
  using released by (auto simp: sb_release_def reference_schedule_release_def split: if_splits)

lemma sb_old_cut_or_checkpoint_cannot_release_a_prepared_reply:
  assumes "observed \<noteq> current \<or> observed_checkpoint \<noteq> current_checkpoint"
  shows "sb_release checks observed current observed_checkpoint current_checkpoint prepared = None"
  using assms by (auto simp: sb_release_def reference_schedule_release_def)

lemma sb_lost_current_authorization_or_replay_never_uses_the_prepared_reply:
  assumes "\<not> sb_checks_hold checks"
  shows "sb_release checks observed current observed_checkpoint current_checkpoint prepared = None"
  using assms by (simp add: sb_release_def)

theorem sb_signed_exchange_retains_the_extra_image_and_labeled_reply_check:
  assumes exchanged: "rust_try_adjacent_exchange eligible distinct_transport compatible baseline alternate =
      Rust_Exchanged selected_image left_reply right_reply"
    and released: "sb_release checks observed current observed_checkpoint current_checkpoint
      (selected_image,left_reply,right_reply) = Some result"
  shows "baseline = result" "alternate = result"
    "eligible left_reply \<and> eligible right_reply \<and> distinct_transport \<and> compatible"
    "observed = current \<and> observed_checkpoint = current_checkpoint \<and> sb_checks_hold checks"
proof -
  have exact: "result = (selected_image,left_reply,right_reply)"
    using sb_released_replies_require_the_same_cut_checkpoint_and_current_checks(4)[OF released] .
  show "baseline = result" "alternate = result"
    using a_rust_exchange_releases_only_the_checked_image_and_the_same_labeled_replies(1,2)[OF exchanged]
    by (simp_all add: exact)
  show "eligible left_reply \<and> eligible right_reply \<and> distinct_transport \<and> compatible"
    using a_rust_exchange_releases_only_the_checked_image_and_the_same_labeled_replies(3)[OF exchanged] .
  show "observed = current \<and> observed_checkpoint = current_checkpoint \<and> sb_checks_hold checks"
    using sb_released_replies_require_the_same_cut_checkpoint_and_current_checks(1,2,3)[OF released] by blast
qed

theorem sb_independent_selection_is_bound_to_the_prepared_image:
  assumes selected: "witnessed_selection
      (\<lambda>archive sb_archive_cut. archived_image archive = Some prepared_image \<and> archived_control archive = witness_control sb_archive_cut)
      archives proposal current_witness = Some next_witness"
  shows "proposal_before proposal = current_witness"
    "witness_version next_witness = Suc (witness_version current_witness)"
    "witness_generation current_witness \<le> witness_generation next_witness"
    "proposal_archive proposal \<in> archives"
    "archived_image (proposal_archive proposal) = Some prepared_image"
    "archived_control (proposal_archive proposal) = witness_control next_witness"
  using a_selection_requires_the_exact_current_cut_and_durable_archive[OF selected] by auto

lemmas sb_cache_source_profile_and_exact_value_binding =
  query_cache_runtime_source_matches_the_three_product_branches
  query_cache_source_success_preserves_every_binding
  query_cache_g0_upstream_refusals_are_preserved

lemmas sb_old_independent_preparation_is_fenced =
  an_old_publication_proposal_cannot_overwrite_the_selected_control
  a_primary_preparation_alone_cannot_release_an_unselected_result

context source_attestation
begin
lemmas sb_native_cache_reuses_the_existing_busy_consumer = query_cache_same_source_agrees_with_existing_busy_consumer
lemmas sb_authenticated_signed_reference_composition = a_confirmed_rust_exchange_refines_the_actual_reference_service_pair
end

text \<open>
  Physical archive durability, verified journal-prefix provenance, a genuine
  independent selector/CAS, current strict signature/credential observations,
  and the mapping of its opaque stored control/checkpoint to these complete
  values are explicit remaining implementation obligations. The current checks
  are named premises, not input protocol verdicts and not an executable claim
  that arbitrary Booleans authenticate packets. The archived-image/control
  functions must be observations of the same retained archive. No physical
  persistence or live writer selection is proved by the finite typed run.
\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sb_released_replies_require_the_same_cut_checkpoint_and_current_checks
      sb_old_cut_or_checkpoint_cannot_release_a_prepared_reply
      sb_lost_current_authorization_or_replay_never_uses_the_prepared_reply
      sb_signed_exchange_retains_the_extra_image_and_labeled_reply_check
      sb_independent_selection_is_bound_to_the_prepared_image})
  then () else error "Unexpected oracle in separate signed scheduler boundary"
\<close>

end
