theory Promotion_Source_Pool
  imports Owner_Recovery
begin

context source_attestation
begin

lemma registry_owner_handover_does_not_rebind_the_authoritative_source_pool:
  assumes admit: "handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal (identity_source s)"
  shows "let after = handover_product_owner directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal s
    in source_units (authoritative_reservation_state (identity_source after)) account =
       source_units (authoritative_reservation_state (identity_source s)) account"
proof -
  let ?s = "identity_source s"
  have exact: "authoritative_reservation_state (apply_owner_handover directory policy authenticate approve owner_token successor_token
      maintainer maintainers registered proposal ?s) = authoritative_reservation_state ?s"
    by (rule handover_atomically_changes_owner_and_sessions_without_spending(5)[OF admit])
  show ?thesis using admit exact
    by (simp add: handover_product_owner_def replace_identity_source_consumes_the_same_authority Let_def)
qed

lemma the_named_authority_prefix_survives_registry_owner_handover:
  fixes s directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal after
  assumes admit: "handover_is_authorized directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal (identity_source s)"
    and bound: "revision \<le> cut_revision (observed_product_cut (read_authority (regulated_read_world s)))"
  defines "after \<equiv> handover_product_owner directory policy authenticate approve owner_token successor_token maintainer maintainers registered proposal s"
  shows "authority_prefix_snapshot revision (read_authority (regulated_read_world after)) =
    authority_prefix_snapshot revision (read_authority (regulated_read_world s))"
proof -
  let ?old = "read_authority (regulated_read_world s)"
  let ?new = "read_authority (regulated_read_world after)"
  let ?changes = "transfer_contexts proposal"
  have guard: "maintainer \<in> maintainers"
    "lock_context_batch_is_newer registered (transfer_epoch proposal) ?changes (identity_source s)"
    using admit by (simp_all add: handover_is_authorized_def Let_def)
  have calls: "product_calls (identity_source after) =
      finality_calls.run_calls (map Apply_Authority_Input ?changes) (product_calls (identity_source s))"
    using admit guard by (simp add: after_def handover_product_owner_def apply_owner_handover_def
      replace_identity_source_consumes_the_same_authority product_apply_public_def Let_def)
  have actual: "exact_calls ?new = finality_calls.run_calls (map Apply_Authority_Input ?changes) (exact_calls ?old)"
    using calls by (simp add: identity_source_def observed_product_source_def exact_calls_def outcome_calls_def)
  obtain suffix where longer: "call_authority_log (exact_calls ?new) = call_authority_log (exact_calls ?old) @ suffix"
    using public_word_only_appends_authority_log[of "map Apply_Authority_Input ?changes" "exact_calls ?old"]
    unfolding actual by blast
  have genesis: "call_genesis (exact_calls ?new) = call_genesis (exact_calls ?old)"
    by (simp add: actual)
  show ?thesis using bound
    by (simp add: authority_prefix_snapshot_def authority_prefix_core_def observed_revision_is_the_public_log_length
       longer genesis take_append)
qed

end

end
