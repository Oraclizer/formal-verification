theory Recovery_Request_Provenance_Run
  imports Recovery_Request_Provenance_Step
begin

text \<open>The machine and step/profile/digest are fixed throughout a finite trace from genesis.
  Restores use only copies in the frozen history universe. The theorem concerns state witnesses;
  it supplies no selected-latest, reply-order, physical-once-only or whole-history replay claim.\<close>

lemma genesis_has_trace_indexed_state_provenance:
  "boundary_has_ask_provenance step R0 requests (genesis_system digest profile R0)"
  by (auto simp: boundary_has_ask_provenance_def archive_has_ask_witness_def genesis_system_def
    genesis_disk_def genesis_record_def split: if_splits)

lemma a_finite_boundary_trace_keeps_request_provenance:
  assumes inv: "boundary_has_ask_provenance step R0 requests s"
  shows "boundary_has_ask_provenance step R0 (requests @ actual_ask_word events)
    (fold (boundary_step step digest profile) events s)"
  using inv
proof (induction events arbitrary: requests s)
  case Nil
  then show ?case by simp
next
  case (Cons event events)
  have first: "boundary_has_ask_provenance step R0 (requests @ ask_occurrence event)
      (boundary_step step digest profile event s)"
    by (rule every_boundary_event_preserves_trace_indexed_state_provenance[OF Cons.prems])
  show ?case using Cons.IH[OF first] by (simp add: append_assoc)
qed

theorem every_boundary_prefix_has_request_provenance:
  "boundary_has_ask_provenance step R0 (actual_ask_word events)
    (fold (boundary_step step digest profile) events (genesis_system digest profile R0))"
  using a_finite_boundary_trace_keeps_request_provenance
    [OF genesis_has_trace_indexed_state_provenance, where requests = "[]" and events = events]
  by simp

corollary every_take_prefix_has_its_own_actual_ask_word:
  "boundary_has_ask_provenance step R0 (actual_ask_word (take count events))
    (fold (boundary_step step digest profile) (take count events) (genesis_system digest profile R0))"
  by (rule every_boundary_prefix_has_request_provenance)

theorem every_retained_image_has_an_actual_ask_subsequence_witness:
  assumes run: "s = fold (boundary_step step digest profile) events (genesis_system digest profile R0)"
  shows "witnessed_reopen digest profile attachment (sys_disk s) (sys_witness s) = Some (h, R) \<Longrightarrow>
      (\<exists>word. requested_subsequence word (actual_ask_word events) \<and>
        R = run_product_action_word step word R0)"
    and "sys_endpoint s = Some (h, R) \<Longrightarrow>
      (\<exists>word. requested_subsequence word (actual_ask_word events) \<and>
        R = run_product_action_word step word R0)"
    and "prepared \<in> set (sys_staged s) \<Longrightarrow>
      (\<exists>word. requested_subsequence word (actual_ask_word events) \<and>
        image_records (staged_record prepared) = run_product_action_word step word R0)"
    and "flushed_records (sys_disk s) address = Some record \<Longrightarrow>
      (\<exists>word. requested_subsequence word (actual_ask_word events) \<and>
        image_records record = run_product_action_word step word R0)"
    and "old_disk \<in> set (ghost_disks s) \<Longrightarrow> flushed_records old_disk address = Some record \<Longrightarrow>
      (\<exists>word. requested_subsequence word (actual_ask_word events) \<and>
        image_records record = run_product_action_word step word R0)"
proof -
  have inv: "boundary_has_ask_provenance step R0 (actual_ask_word events) s"
    unfolding run by (rule every_boundary_prefix_has_request_provenance)
  show "\<exists>word. requested_subsequence word (actual_ask_word events) \<and>
      R = run_product_action_word step word R0"
    if opened: "witnessed_reopen digest profile attachment (sys_disk s) (sys_witness s) = Some (h, R)"
  proof -
    have archive: "archive_has_ask_witness step R0 (actual_ask_word events) (sys_disk s)"
      using inv unfolding boundary_has_ask_provenance_def by blast
    have "state_has_ask_witness step R0 (actual_ask_word events) R"
      by (rule a_successful_reopen_has_the_flushed_images_ask_witness[OF archive opened])
    then show ?thesis unfolding state_has_ask_witness_def .
  qed
  show "\<exists>word. requested_subsequence word (actual_ask_word events) \<and>
      R = run_product_action_word step word R0" if "sys_endpoint s = Some (h, R)"
    using inv that unfolding boundary_has_ask_provenance_def state_has_ask_witness_def by blast
  show "\<exists>word. requested_subsequence word (actual_ask_word events) \<and>
      image_records (staged_record prepared) = run_product_action_word step word R0"
    if "prepared \<in> set (sys_staged s)"
    using inv that unfolding boundary_has_ask_provenance_def state_has_ask_witness_def by blast
  show "\<exists>word. requested_subsequence word (actual_ask_word events) \<and>
      image_records record = run_product_action_word step word R0"
    if "flushed_records (sys_disk s) address = Some record"
    using inv that unfolding boundary_has_ask_provenance_def archive_has_ask_witness_def state_has_ask_witness_def by blast
  show "\<exists>word. requested_subsequence word (actual_ask_word events) \<and>
      image_records record = run_product_action_word step word R0"
    if "old_disk \<in> set (ghost_disks s)" "flushed_records old_disk address = Some record"
    using inv that unfolding boundary_has_ask_provenance_def archive_has_ask_witness_def state_has_ask_witness_def by blast
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms genesis_has_trace_indexed_state_provenance
      a_finite_boundary_trace_keeps_request_provenance every_boundary_prefix_has_request_provenance
      every_take_prefix_has_its_own_actual_ask_word every_retained_image_has_an_actual_ask_subsequence_witness})
  then () else error "Unexpected oracle in finite-trace state provenance"
\<close>

end
