theory Recovery_Request_Provenance_Controls
  imports "Recovery_Request_Provenance_Run"
begin

text \<open>A noninjective address can reopen an actually requested but unselected image. This
  illustrates the boundary of state provenance; it is not a deployed collision attack or a
  violation of the separate honest-witness-plus-injective-address selected-word theorem.\<close>

fun forked_request_step ::
  "authority_connection \<Rightarrow> bool \<Rightarrow> retained_product \<Rightarrow> retained_product \<times> nat" where
  "forked_request_step connection False R = (toy_bump R, 0)"
| "forked_request_step connection True R = (toy_bump (toy_bump R), 1)"

definition collapsed_record_address :: "nat persisted_commit \<Rightarrow> nat" where
  "collapsed_record_address record = 0"

definition request_profile_attachment where
  "request_profile_attachment profile connection =
    \<lparr>attachment_profile = profile, attachment_connection = connection\<rparr>"

definition unselected_image_restore_events where
  "unselected_image_restore_events connection profile =
    [Ask connection True, Flush_Record 0, Publish_Head 0, Crash_Endpoint,
     Roll_Back_Disk 0, Reopen_Endpoint (request_profile_attachment profile connection),
     Ask connection False, Flush_Record 0, Publish_Head 0, Select_Head 0, Crash_Endpoint,
     Roll_Back_Disk 2, Reopen_Endpoint (request_profile_attachment profile connection)]"

definition unselected_image_restore_state where
  "unselected_image_restore_state connection profile R0 =
    fold (boundary_step forked_request_step collapsed_record_address profile)
      (unselected_image_restore_events connection profile)
      (genesis_system collapsed_record_address profile R0)"

lemma the_control_address_really_collides:
  "collapsed_record_address (genesis_record profile R0) =
    collapsed_record_address (genesis_record profile (toy_bump R0))"
  "genesis_record profile R0 \<noteq> genesis_record profile (toy_bump R0)"
  by (simp_all add: collapsed_record_address_def genesis_record_def)

lemma the_control_uses_actual_requests_and_only_historical_restore:
  "actual_ask_word (unselected_image_restore_events connection profile) = [(connection, True), (connection, False)]"
  "\<forall>event \<in> set (unselected_image_restore_events connection profile). \<not> is_witness_rollback event"
  by (simp_all add: unselected_image_restore_events_def)

lemma the_selected_word_contains_only_the_other_request:
  "ghost_word (unselected_image_restore_state connection profile R0) = [(connection, False)]"
proof -
  have changed_true: "toy_bump (toy_bump R0) \<noteq> R0"
    by (cases R0) (simp add: toy_bump_def)
  show ?thesis using changed_true
    by (simp add: unselected_image_restore_state_def unselected_image_restore_events_def
      collapsed_record_address_def request_profile_attachment_def boundary_run_simps)
qed

lemma a_requested_unselected_image_is_reopened:
  "sys_endpoint (unselected_image_restore_state connection profile R0) =
    Some (head_for_record collapsed_record_address
      (staged_commit profile (head_for_record collapsed_record_address (genesis_record profile R0))
        (toy_bump (toy_bump R0))), toy_bump (toy_bump R0))"
proof -
  have changed_true: "toy_bump (toy_bump R0) \<noteq> R0"
    by (cases R0) (simp add: toy_bump_def)
  show ?thesis using changed_true
    by (simp add: unselected_image_restore_state_def unselected_image_restore_events_def
      collapsed_record_address_def request_profile_attachment_def boundary_run_simps)
qed

lemma the_reopened_image_has_an_actual_request_subsequence:
  "requested_subsequence [(connection, True)] (actual_ask_word (unselected_image_restore_events connection profile))"
  "run_product_action_word forked_request_step [(connection, True)] R0 = toy_bump (toy_bump R0)"
  "state_has_ask_witness forked_request_step R0 (actual_ask_word (unselected_image_restore_events connection profile))
    (toy_bump (toy_bump R0))"
proof -
  show sub: "requested_subsequence [(connection, True)] (actual_ask_word (unselected_image_restore_events connection profile))"
    by (simp add: unselected_image_restore_events_def)
      (rule requested_subsequence.keep, rule requested_subsequence.empty)
  show image: "run_product_action_word forked_request_step [(connection, True)] R0 = toy_bump (toy_bump R0)"
    by simp
  show "state_has_ask_witness forked_request_step R0 (actual_ask_word (unselected_image_restore_events connection profile))
      (toy_bump (toy_bump R0))"
    unfolding state_has_ask_witness_def
  proof (rule exI[of _ "[(connection, True)]"], rule conjI)
    show "requested_subsequence [(connection, True)]
        (actual_ask_word (unselected_image_restore_events connection profile))"
      by (rule sub)
    show "toy_bump (toy_bump R0) = run_product_action_word forked_request_step [(connection, True)] R0"
      by (rule sym[OF image])
  qed
qed

lemma provenance_does_not_imply_selected_word_equality:
  "toy_bump (toy_bump R0) \<noteq> run_product_action_word forked_request_step
    (ghost_word (unselected_image_restore_state connection profile R0)) R0"
  by (simp add: the_selected_word_contains_only_the_other_request)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_control_address_really_collides
      the_control_uses_actual_requests_and_only_historical_restore the_selected_word_contains_only_the_other_request
      a_requested_unselected_image_is_reopened the_reopened_image_has_an_actual_request_subsequence
      provenance_does_not_imply_selected_word_equality})
  then () else error "Unexpected oracle in state-provenance boundary controls"
\<close>

end
