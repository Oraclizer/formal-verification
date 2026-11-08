theory Reference_Product_Image
  imports Reference_Read_Consumption Reference_Wire_Admission
begin

record 'head reference_product_image =
  image_authority :: reference_authority_snapshot
  image_read_history :: "endpoint_snapshot reference_read_history"
  image_transport :: wire_dedup_store
  image_ordered_control :: "'head reference_control"

definition capture_reference_view where
  "capture_reference_view authority = capture_snapshot (retained_core (retained_source (reference_product authority)))"

definition reference_image_views_agree where
  "reference_image_views_agree frame \<longleftrightarrow>
    reference_history_epoch (image_read_history frame) = reference_records_epoch (reference_product (image_authority frame)) \<and>
    reference_history_prefixes (image_read_history frame) \<noteq> [] \<and>
    last (reference_history_prefixes (image_read_history frame)) = capture_reference_view (image_authority frame)"

definition record_reference_product_image where
  "record_reference_product_image authority steps old =
    old\<lparr>image_authority := authority, image_read_history :=
      record_reference_advance (reference_records_epoch (reference_product authority)) steps
       (capture_reference_view authority) (image_read_history old)\<rparr>"

lemma a_ledger_advance_captures_the_view_of_its_actual_product:
  assumes "steps > 0"
  shows "reference_image_views_agree (record_reference_product_image authority steps old)"
  using assms by (simp add: reference_image_views_agree_def record_reference_product_image_def
    record_reference_advance_def last_append last_replicate)

lemma a_metadata_only_update_needs_the_same_ledger_view_and_epoch:
  assumes coherent: "reference_image_views_agree old"
    and view: "capture_reference_view authority = capture_reference_view (image_authority old)"
    and epoch: "reference_records_epoch (reference_product authority) =
      reference_records_epoch (reference_product (image_authority old))"
  shows "reference_image_views_agree (record_reference_product_image authority 0 old)"
  using coherent view epoch by (simp add: reference_image_views_agree_def record_reference_product_image_def
    record_reference_advance_def)

definition current_read_from_reference_image where
  "current_read_from_reference_image directory policy authenticate verify_read token proof target query expected connection frame =
    (let reply = reference_current_read directory policy authenticate verify_read token proof target query expected
        connection (image_authority frame) (\<lambda>row q. stored_query q row) (image_read_history frame)
     in case reply of Authorized_Data (Current_Cut_Value actual value) \<Rightarrow>
          if snapshot_query_ready query (last (reference_history_prefixes (image_read_history frame)))
          then reply else Authorized_Data Product_Read_Busy
      | _ \<Rightarrow> reply)"

theorem the_current_image_read_consumes_its_actual_current_authority_view:
  assumes coherent: "reference_image_views_agree frame"
    and read: "current_read_from_reference_image directory policy authenticate verify_read token proof target query expected connection frame =
      Authorized_Data (Current_Cut_Value actual value)"
  shows "actual = reference_observed_cut (image_read_history frame)"
    "snapshot_query_ready query (capture_reference_view (image_authority frame))"
    "value = stored_query query (capture_reference_view (image_authority frame))"
    "identity_read_allowed directory policy authenticate verify_read token proof target
      (Current_Data query expected) (identity_source (reference_read_source connection (image_authority frame)))"
proof -
  let ?reply = "reference_current_read directory policy authenticate verify_read token proof target query expected
        connection (image_authority frame) (\<lambda>row q. stored_query q row) (image_read_history frame)"
  have actual: "?reply = Authorized_Data (Current_Cut_Value actual value)"
    and ready: "snapshot_query_ready query (last (reference_history_prefixes (image_read_history frame)))"
    using read by (cases ?reply; auto simp: current_read_from_reference_image_def Let_def split: product_read_reply.splits if_splits)+
  have last_view: "last (reference_history_prefixes (image_read_history frame)) = capture_reference_view (image_authority frame)"
    using coherent by (simp add: reference_image_views_agree_def)
  show "actual = reference_observed_cut (image_read_history frame)"
    by (rule the_reference_endpoint_current_value_consumes_current_identity_and_exact_cut(3)[OF actual])
  show "snapshot_query_ready query (capture_reference_view (image_authority frame))"
    using ready last_view by simp
  show "value = stored_query query (capture_reference_view (image_authority frame))"
    using the_reference_endpoint_current_value_consumes_current_identity_and_exact_cut(4)[OF actual] last_view by simp
  show "identity_read_allowed directory policy authenticate verify_read token proof target
      (Current_Data query expected) (identity_source (reference_read_source connection (image_authority frame)))"
    by (rule the_reference_endpoint_current_value_consumes_current_identity_and_exact_cut(1)[OF actual])
qed

definition commit_reference_debit where
  "commit_reference_debit observed frame request candidate_head after_authority =
    (let current = image_ordered_control frame;
         decided = reference_publish_applied observed current request candidate_head in
       if decided = current then frame else
       case decode_wire_packet (original_packet request) of None \<Rightarrow> frame
        | Some packet \<Rightarrow>
          (record_reference_product_image after_authority 1 frame)\<lparr>image_ordered_control := decided,
            image_transport := (image_transport frame)
              (original_transport request := Some (encode_wire_core (packet_core packet)))\<rparr>)"

lemma a_stale_control_observation_preserves_the_entire_reference_image:
  assumes "observed \<noteq> image_ordered_control frame"
  shows "commit_reference_debit observed frame request candidate_head after_authority = frame"
  using assms by (simp add: commit_reference_debit_def reference_publish_applied_def Let_def)

theorem an_ordered_debit_publishes_the_exact_input_and_product_view_together:
  assumes observed: "observed = image_ordered_control frame"
    and pending: "control_decisions observed (original_call request) = Some (request, Ref_Pending)"
    and decoded: "decode_wire_packet (original_packet request) = Some packet"
  shows "let after = commit_reference_debit observed frame request candidate_head after_authority
    in control_head (image_ordered_control after) = Some candidate_head \<and>
       image_authority after = after_authority \<and> reference_image_views_agree after \<and>
       image_transport after (original_transport request) = Some (encode_wire_core (packet_core packet))"
proof -
  let ?decision = "reference_publish_applied observed (image_ordered_control frame) request candidate_head"
  have advanced: "control_revision ?decision = Suc (control_revision (image_ordered_control frame))"
    using observed pending by (simp add: reference_publish_applied_def)
  have differs: "?decision \<noteq> image_ordered_control frame"
  proof
    assume "?decision = image_ordered_control frame"
    then show False using advanced by simp
  qed
  show ?thesis using observed pending decoded differs
    by (simp add: commit_reference_debit_def reference_publish_applied_def reference_image_views_agree_def
      record_reference_product_image_def record_reference_advance_def Let_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms a_ledger_advance_captures_the_view_of_its_actual_product
      a_metadata_only_update_needs_the_same_ledger_view_and_epoch
      the_current_image_read_consumes_its_actual_current_authority_view
      a_stale_control_observation_preserves_the_entire_reference_image
      an_ordered_debit_publishes_the_exact_input_and_product_view_together})
  then () else error "Unexpected oracle in reference product frame"
\<close>

end
