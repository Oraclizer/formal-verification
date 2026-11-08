theory Reference_Proof_Derived_Contrasts
  imports "Reference_Entry_Closure" "OIP_Product.Recovery_Anchor"
begin

context source_attestation
begin

definition checked_execution_without_the_expected_revision where
  "checked_execution_without_the_expected_revision permitted verified maintainers registered verified_ack
     entry who expected call_id payload state =
     (let authority = read_authority state; actual = observed_product_cut authority in
       if \<not> result_access_bound verified who call_id payload (origin_outcomes (settlement_primary authority))
       then (state,Checked_Execution_Rejected)
       else if \<not> read_authority_available state then (state,Checked_Execution_Unavailable)
       else if cut_authority_epoch expected \<noteq> cut_authority_epoch actual \<or> envelope_cut (payload_envelope payload) \<noteq> actual
       then (state,Checked_Execution_Busy)
       else (state\<lparr>read_authority := exact_step permitted verified maintainers registered verified_ack
           (Exact_Submit entry who call_id payload) authority\<rparr>, Forwarded_At_Checked_Cut))"

lemma the_same_current_payload_cannot_replace_a_stale_wrapper_revision:
  fixes actual state
  defines "actual \<equiv> observed_product_cut (read_authority state)"
  assumes access: "result_access_bound verified who call_id payload (origin_outcomes (settlement_primary (read_authority state)))"
    and ready: "read_authority_available state" "envelope_cut (payload_envelope payload) = actual"
    and same_epoch: "cut_authority_epoch expected = cut_authority_epoch actual"
    and stale_revision: "cut_revision expected \<noteq> cut_revision actual"
  shows "execute_at_checked_cut permitted verified maintainers registered verified_ack
      entry who expected call_id payload state = (state,Checked_Execution_Busy)"
    "checked_execution_without_the_expected_revision permitted verified maintainers registered verified_ack
      entry who expected call_id payload state =
      (state\<lparr>read_authority := exact_step permitted verified maintainers registered verified_ack
         (Exact_Submit entry who call_id payload) (read_authority state)\<rparr>, Forwarded_At_Checked_Cut)"
proof -
  have stale: "expected \<noteq> actual" using stale_revision by auto
  show "execute_at_checked_cut permitted verified maintainers registered verified_ack
      entry who expected call_id payload state = (state,Checked_Execution_Busy)"
    using access ready stale by (simp add: execute_at_checked_cut_def actual_def Let_def)
  show "checked_execution_without_the_expected_revision permitted verified maintainers registered verified_ack
      entry who expected call_id payload state =
      (state\<lparr>read_authority := exact_step permitted verified maintainers registered verified_ack
         (Exact_Submit entry who call_id payload) (read_authority state)\<rparr>, Forwarded_At_Checked_Cut)"
    using access ready same_epoch by (simp add: checked_execution_without_the_expected_revision_def actual_def Let_def)
qed

lemma dropping_only_read_scope_allows_the_same_live_authenticated_read_to_reach_the_value:
  assumes present: "authenticate token = Some identity" "active_identity directory identity proof (identity_source state)"
    and signed: "verify_read identity proof target request"
    and denied: "\<not> policy identity target request (proof_epoch proof)"
    and available: "read_authority_available (regulated_read_world state)"
  shows "read_at_identity_endpoint directory policy authenticate verify_read token proof target request state = Identity_Read_Rejected"
    "read_at_identity_endpoint directory (\<lambda>_ _ _ _. True) authenticate verify_read token proof target request state =
       authorized_read_value identity proof target request (regulated_read_world state)"
  using assms by (simp_all add: read_at_identity_endpoint_def identity_read_allowed_def Let_def)

end

definition retained_decision_without_origin_epoch where
  "retained_decision_without_origin_epoch world binding kind \<longleftrightarrow>
    (\<exists>saved. origin_decisions world (binding_key binding) = Some saved \<and>
         origin_binding saved = binding \<and> origin_kind saved = kind)"

lemma dropping_only_origin_epoch_reuses_the_wrong_original_terminal_slot:
  assumes "origin_decisions world (binding_key binding) = Some original"
    "origin_binding original = binding" "origin_kind original = kind" "origin_epoch original \<noteq> requested_epoch"
  shows "\<not> existing_decision_matches world binding kind requested_epoch"
    "retained_decision_without_origin_epoch world binding kind"
  using assms by (simp_all add: existing_decision_matches_def decision_matches_def retained_decision_without_origin_epoch_def)

definition reopen_without_matching_the_record_digest where
  "reopen_without_matching_the_record_digest profile attachment store =
    (case (attachment, committed_head store) of (Some current, Some head) \<Rightarrow>
       if attachment_profile current \<noteq> profile \<or> head_profile head \<noteq> profile then None
       else case flushed_records store head of None \<Rightarrow> None | Some stored \<Rightarrow>
         if image_profile stored = head_profile head \<and> image_sequence stored = head_sequence head
         then Some (reopen_retained_product (attachment_connection current) (image_records stored)) else None
     | _ \<Rightarrow> None)"

lemma omitting_only_record_digest_accepts_the_same_altered_body_at_the_current_sequence:
  assumes "committed_head store = Some (head_for_record digest current)"
    "flushed_records store (head_for_record digest current) = Some altered"
    "digest altered \<noteq> digest current" "image_profile altered = image_profile current"
    "image_sequence altered = image_sequence current" "attachment_profile attachment = image_profile current"
  shows "reopen_from_authenticated_head digest (image_profile current) (Some attachment) store = None"
    "reopen_without_matching_the_record_digest (image_profile current) (Some attachment) store =
      Some (reopen_retained_product (attachment_connection attachment) (image_records altered))"
  using assms by (simp_all add: reopen_from_authenticated_head_def reopen_without_matching_the_record_digest_def head_for_record_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.the_same_current_payload_cannot_replace_a_stale_wrapper_revision
    source_attestation.dropping_only_read_scope_allows_the_same_live_authenticated_read_to_reach_the_value
    dropping_only_origin_epoch_reuses_the_wrong_original_terminal_slot
    omitting_only_record_digest_accepts_the_same_altered_body_at_the_current_sequence})
  then () else error "Unexpected oracle in proof-derived guard contrasts"
\<close>

end
