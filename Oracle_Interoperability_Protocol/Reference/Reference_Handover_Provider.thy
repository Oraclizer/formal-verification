theory Reference_Handover_Provider
  imports "Reference_Handover_Consumption"
begin

definition reference_provider_for_current_epoch where
  "reference_provider_for_current_epoch approved snapshot =
     approved (reference_epoch (reference_inputs snapshot))"

definition reference_provider_image_matches where
  "reference_provider_image_matches approved snapshot stored \<longleftrightarrow>
     (\<exists>fingerprint. stored = Some fingerprint \<and>
       reference_provider_for_current_epoch approved snapshot = Some fingerprint)"

lemma preloading_a_future_provider_cannot_substitute_for_the_current_one:
  assumes "reference_provider_for_current_epoch approved snapshot \<noteq> Some future_fingerprint"
  shows "\<not> reference_provider_image_matches approved snapshot (Some future_fingerprint)"
  using assms by (simp add: reference_provider_image_matches_def)

lemma an_epoch_without_an_approved_provider_cannot_publish_a_reference_image:
  assumes "reference_provider_for_current_epoch approved snapshot = None"
  shows "\<not> reference_provider_image_matches approved snapshot stored"
  using assms by (simp add: reference_provider_image_matches_def)

context source_attestation
begin

theorem a_selected_reference_handover_binds_the_successor_provider_at_the_same_epoch:
  assumes executed: "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
    authenticated connection (Service_Handover owner_token successor_token maintainer proposal) supplied before =
      (after, Some (Scheduled_Endpoint (Service_Handover_Result True)))"
    and bound: "reference_provider_image_matches approved after (Some fingerprint)"
  shows "approved (transfer_epoch proposal) = Some fingerprint"
    "product_owners (retained_authority (retained_source (reference_product after))) (transfer_asset proposal) =
       Some (transfer_successor proposal)"
    "product_sessions (retained_authority (retained_source (reference_product after))) (transfer_old_session proposal) = None"
    "core_parent (retained_core (retained_source (reference_product after))) =
       core_parent (retained_core (retained_source (reference_product before)))"
proof -
  note handover = the_actual_reference_handover_updates_owner_sessions_and_grants_at_one_epoch[OF executed]
  show "approved (transfer_epoch proposal) = Some fingerprint"
    using bound handover(4) by (simp add: reference_provider_image_matches_def reference_provider_for_current_epoch_def)
  show "product_owners (retained_authority (retained_source (reference_product after))) (transfer_asset proposal) =
      Some (transfer_successor proposal)"
    "product_sessions (retained_authority (retained_source (reference_product after))) (transfer_old_session proposal) = None"
    "core_parent (retained_core (retained_source (reference_product after))) =
      core_parent (retained_core (retained_source (reference_product before)))"
    by (rule handover(1) handover(2) handover(5))+
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms preloading_a_future_provider_cannot_substitute_for_the_current_one
      an_epoch_without_an_approved_provider_cannot_publish_a_reference_image
      source_attestation.a_selected_reference_handover_binds_the_successor_provider_at_the_same_epoch})
  then () else error "Unexpected oracle in reference handover provider selection"
\<close>

end
