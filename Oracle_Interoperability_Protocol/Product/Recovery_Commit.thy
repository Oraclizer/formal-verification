theory Recovery_Commit
  imports Recovery_Simulation
begin

record 'digest prepared_product_step =
  prepared_record :: "'digest persisted_commit"
  prepared_reply :: retained_service_reply
  prepared_base :: "'digest commit_head"

context source_attestation
begin

definition prepare_served_mutation where
  "prepare_served_mutation digest profile attachment store
    directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action =
    (case (committed_head store, reopen_from_authenticated_head digest profile attachment store) of
       (Some head, Some before) \<Rightarrow>
       let result = live_product_service_step directory policy read_policy authenticate verify verify_read endorse approve
           legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action before;
           next_records = capture_retained_product (fst result)
       in if next_records = capture_retained_product before then None else
          Some \<lparr>prepared_record = \<lparr>image_profile = profile, image_sequence = Suc (head_sequence head),
                    image_parent = Some (head_digest head), image_records = next_records\<rparr>,
                 prepared_reply = snd result, prepared_base = head\<rparr>
     | _ \<Rightarrow> None)"

lemma a_prepared_effect_and_reply_are_from_the_same_anchored_execution:
  assumes "prepare_served_mutation digest profile attachment store
    directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action =
    Some prepared"
  shows "\<exists>before after. reopen_from_authenticated_head digest profile attachment store = Some before \<and>
    live_product_service_step directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      action before = (after, prepared_reply prepared) \<and>
    capture_retained_product after = image_records (prepared_record prepared) \<and>
    committed_head store = Some (prepared_base prepared)"
proof -
  obtain head before where head: "committed_head store = Some head"
    and opened: "reopen_from_authenticated_head digest profile attachment store = Some before"
    using assms by (cases "committed_head store"; cases "reopen_from_authenticated_head digest profile attachment store")
      (auto simp: prepare_served_mutation_def)
  let ?result = "live_product_service_step directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action before"
  let ?records = "capture_retained_product (fst ?result)"
  let ?built = "\<lparr>prepared_record = \<lparr>image_profile = profile, image_sequence = Suc (head_sequence head),
        image_parent = Some (head_digest head), image_records = ?records\<rparr>,
      prepared_reply = snd ?result, prepared_base = head\<rparr>"
  have prepared: "(if ?records = capture_retained_product before then None else Some ?built) = Some prepared"
    using assms head opened by (simp add: prepare_served_mutation_def Let_def)
  have exact: "prepared = ?built" using prepared by (cases "?records = capture_retained_product before") simp_all
  show ?thesis unfolding exact using head opened by (intro exI[of _ before] exI[of _ "fst ?result"]) simp
qed

end

definition issue_committed_response where
  "issue_committed_response digest prepared s =
    (let candidate = prepared_record prepared; expected = head_for_record digest candidate in
      if committed_head s = Some expected \<and> flushed_records s expected = Some candidate
      then Some (prepared_reply prepared) else None)"

lemma new_reply_is_invisible_during_prepare_or_flush:
  assumes "committed_head s \<noteq> Some (head_for_record digest (prepared_record prepared))"
  shows "issue_committed_response digest prepared (flush_commit_record digest (prepared_record prepared) s) = None"
  using assms by (simp add: issue_committed_response_def Let_def flushed_candidate_is_not_visible_before_the_head_changes)

lemma exact_committed_head_releases_the_prepared_response:
  assumes "committed_head s = Some (prepared_base prepared)"
    "candidate_extends_head (Some (prepared_base prepared)) (prepared_record prepared)"
    "flushed_records s (head_for_record digest (prepared_record prepared)) = Some (prepared_record prepared)"
  shows "issue_committed_response digest prepared
      (publish_recovery_head digest (Some (prepared_base prepared)) (prepared_record prepared) s) = Some (prepared_reply prepared)"
  using published_head_identifies_the_flushed_record[OF assms]
  by (simp add: issue_committed_response_def Let_def)

theorem the_committed_reply_and_reopened_effect_use_one_record:
  assumes base: "committed_head s = Some (prepared_base prepared)"
    and extends: "candidate_extends_head (Some (prepared_base prepared)) (prepared_record prepared)"
    and flushed: "flushed_records s (head_for_record digest (prepared_record prepared)) = Some (prepared_record prepared)"
    and profile: "attachment_profile attachment = image_profile (prepared_record prepared)"
  shows "let committed = publish_recovery_head digest (Some (prepared_base prepared)) (prepared_record prepared) s
    in issue_committed_response digest prepared committed = Some (prepared_reply prepared) \<and>
       (\<exists>restored. reopen_from_authenticated_head digest (attachment_profile attachment) (Some attachment) committed = Some restored \<and>
          capture_retained_product restored = image_records (prepared_record prepared))"
proof -
  let ?candidate = "prepared_record prepared"
  let ?committed = "publish_recovery_head digest (Some (prepared_base prepared)) ?candidate s"
  let ?restored = "reopen_retained_product (attachment_connection attachment) (image_records ?candidate)"
  note located = published_head_identifies_the_flushed_record[OF base extends flushed]
  have reply: "issue_committed_response digest prepared ?committed = Some (prepared_reply prepared)"
    by (rule exact_committed_head_releases_the_prepared_response[OF base extends flushed])
  have reopen: "reopen_from_authenticated_head digest (attachment_profile attachment) (Some attachment) ?committed = Some ?restored"
    unfolding profile by (rule independently_anchored_records_construct_a_fresh_endpoint[OF located profile])
  show ?thesis using reply reopen product_round_trip_preserves_the_durable_projection[of "attachment_connection attachment" "image_records ?candidate"]
    by (simp add: Let_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    independently_anchored_records_construct_a_fresh_endpoint
    an_old_valid_record_at_the_current_address_is_rejected
    a_changed_body_cannot_match_the_anchored_digest
    source_attestation.an_admitted_exact_retry_checks_the_retained_result_before_fresh_conditions
    source_attestation.authenticated_records_only_recovery_is_a_forward_simulation
    source_attestation.mismatched_source_evidence_only_holds_the_exact_pending_binding
    source_attestation.missing_or_wrong_reversal_cannot_move_the_source_balance
    source_attestation.a_prepared_effect_and_reply_are_from_the_same_anchored_execution
    the_committed_reply_and_reopened_effect_use_one_record
    new_reply_is_invisible_during_prepare_or_flush})
  then () else error "Unexpected oracle in authenticated recovery"
\<close>

end
