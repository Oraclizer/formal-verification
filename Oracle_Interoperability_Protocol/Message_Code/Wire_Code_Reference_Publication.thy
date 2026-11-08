theory Wire_Code_Reference_Publication
  imports Wire_Code_Reference_Admission Wire_Code_Operand_Tree "OIP_Reference_Profile.Reference_Product_Image"
begin

definition code_reauthorize_debit_publication ::
  "registered_identity \<Rightarrow> registered_identity option \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow>
    endpoint_policy \<Rightarrow> nat \<Rightarrow> product_asset \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> code_path_refusal option" where
  "code_reauthorize_debit_publication expected current credential_packet bytes
      policy target asset epoch retained =
    (if current \<noteq> Some expected \<or> \<not> code_matches_signed_packet bytes credential_packet
     then Some (Code_Path_Validation Invalid_Wire_Source)
     else if \<not> policy expected target asset Execute_Ordinary epoch \<or>
       (retained \<and> \<not> policy expected target asset Read_Receipt epoch)
     then Some Code_Path_Product_Rejected else None)"

lemma a_changed_current_identity_refuses_debit_publication:
  assumes "current \<noteq> Some expected"
  shows "code_reauthorize_debit_publication expected current credential_packet bytes
      policy target asset epoch retained = Some (Code_Path_Validation Invalid_Wire_Source)"
  using assms by (simp add: code_reauthorize_debit_publication_def)

lemma an_authorized_retained_debit_has_both_current_execute_and_receipt_permissions:
  assumes "code_reauthorize_debit_publication expected current credential_packet bytes
      policy target asset epoch True = None"
  shows "policy expected target asset Execute_Ordinary epoch \<and> policy expected target asset Read_Receipt epoch"
  using assms by (auto simp: code_reauthorize_debit_publication_def split: if_splits)

datatype code_debit_publication_result =
    Code_Debit_Publication_Refused code_path_refusal
  | Code_Debit_Publication_Ready wire_boundary wire_bytes
  | Code_Debit_Publication_Pending

definition code_debit_publication_guard ::
  "negotiated_wire_profile \<Rightarrow> code_source_selected_boundary option \<Rightarrow> code_channel_guard \<Rightarrow>
    nat \<Rightarrow> product_cut \<Rightarrow> nat \<Rightarrow> registered_identity \<Rightarrow> registered_identity option \<Rightarrow>
    wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> endpoint_policy \<Rightarrow> product_asset \<Rightarrow> bool \<Rightarrow>
    (wire_bytes \<Rightarrow> wire_core \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> bool) \<Rightarrow>
    wire_packet \<Rightarrow> code_debit_publication_result" where
  "code_debit_publication_guard profile selected channel deployment (current_cut::product_cut) admitted_at expected current
      credential_packet bytes policy asset retained verify_key (packet::wire_packet) =
    (case code_boundary_at (code_attach_channel_profile profile (code_source_selected_pair selected)) channel deployment current_cut (Some admitted_at) False of
       Inl reason \<Rightarrow> Code_Debit_Publication_Refused reason
     | Inr (scope,key) \<Rightarrow>
       (case code_reauthorize_debit_publication expected current credential_packet bytes policy
          (boundary_target scope) asset (cut_authority_epoch current_cut) retained of
          Some reason \<Rightarrow> Code_Debit_Publication_Refused reason
        | None \<Rightarrow>
          let publication_scope = scope\<lparr>boundary_now := admitted_at\<rparr> in
          if length bytes > boundary_max_frame publication_scope then Code_Debit_Publication_Refused (Code_Path_Validation Invalid_Wire_Format)
          else (case decode_wire_packet bytes of None \<Rightarrow> Code_Debit_Publication_Refused (Code_Path_Validation Invalid_Wire_Format)
           | Some reread \<Rightarrow>
             (case code_admit_packet (verify_key key) reread publication_scope of
                Some reason \<Rightarrow> Code_Debit_Publication_Refused (Code_Path_Validation reason)
              | None \<Rightarrow>
                (case code_decode_operand_tree (code_source_selected_nesting selected) (packet_core packet) of
                   Code_Tree_Refused reason \<Rightarrow> Code_Debit_Publication_Refused (Code_Path_Validation reason)
                 | Code_Tree_Pending \<Rightarrow> Code_Debit_Publication_Pending
                 | Code_Tree_Ready decoded \<Rightarrow> Code_Debit_Publication_Ready publication_scope key)))))"

text \<open>
  This is publication_guard specialized to an ordered ordinary Debit.
  Its CheckedInput has debit_scope=Some(Asset asset,Execute,retained) and
  no ACK maintainer, handover maintainer or recovery endorsement. Those
  variants require separate source branches and are not silently assumed.
  The original packet argument is the already decoded CheckedInput core;
  its correspondence with the reread packet must come from the consume
  construction. This function does not replace that provenance obligation.
\<close>

theorem a_ready_debit_publication_keeps_its_admission_clock_and_peer_key:
  assumes ready: "code_debit_publication_guard profile selected channel deployment current_cut admitted_at expected current
      credential_packet bytes policy asset retained verify_key packet = Code_Debit_Publication_Ready scope key"
  shows "boundary_now scope = admitted_at"
    "key = guard_channel_peer_key channel"
    "policy expected (boundary_target scope) asset Execute_Ordinary (cut_authority_epoch current_cut)"
    "retained \<longrightarrow> policy expected (boundary_target scope) asset Read_Receipt (cut_authority_epoch current_cut)"
proof -
  obtain selected_scope where boundary: "code_boundary_at (code_attach_channel_profile profile (code_source_selected_pair selected))
      channel deployment current_cut (Some admitted_at) False = Inr (selected_scope,key)"
    and scope: "scope = selected_scope\<lparr>boundary_now := admitted_at\<rparr>"
    and authorized: "code_reauthorize_debit_publication expected current credential_packet bytes policy
      (boundary_target selected_scope) asset (cut_authority_epoch current_cut) retained = None"
    using ready by (auto simp: code_debit_publication_guard_def Let_def
      split: sum.splits option.splits code_operand_tree_result.splits if_splits)
  show "boundary_now scope = admitted_at" by (simp add: scope)
  show "key = guard_channel_peer_key channel"
    by (rule every_source_boundary_uses_the_channel_peer_key_and_exact_live_cut(1)[OF boundary])
  show "policy expected (boundary_target scope) asset Execute_Ordinary (cut_authority_epoch current_cut)"
    using authorized by (auto simp: code_reauthorize_debit_publication_def scope split: if_splits)
  show "retained \<longrightarrow> policy expected (boundary_target scope) asset Read_Receipt (cut_authority_epoch current_cut)"
    using authorized by (auto simp: code_reauthorize_debit_publication_def scope split: if_splits)
qed

theorem a_ready_debit_publication_uses_depth_from_the_same_source_selection:
  assumes ready: "code_debit_publication_guard profile selected channel deployment current_cut admitted_at expected current
      credential_packet bytes policy asset retained verify_key packet = Code_Debit_Publication_Ready scope key"
  obtains source_scope source_key max_nesting decoded
  where "selected = Some (source_scope,source_key,max_nesting)"
    "code_source_selected_pair selected = Some (source_scope,source_key)"
    "code_source_selected_nesting selected = max_nesting"
    "code_decode_operand_tree max_nesting (packet_core packet) = Code_Tree_Ready decoded"
  using ready by (auto simp: code_debit_publication_guard_def code_source_selected_pair_def
    code_source_selected_nesting_def Let_def split: sum.splits option.splits prod.splits
    code_operand_tree_result.splits if_splits)

definition code_publish_checked_debit where
  "code_publish_checked_debit guarded observed frame request head candidate =
    (case guarded of Code_Debit_Publication_Ready scope key \<Rightarrow>
       commit_reference_debit observed frame request head candidate
     | _ \<Rightarrow> frame)"

lemma a_refused_debit_publication_preserves_the_entire_product_image:
  "code_publish_checked_debit (Code_Debit_Publication_Refused reason) observed frame request head candidate = frame"
  by (simp add: code_publish_checked_debit_def)

lemma a_pending_model_publication_cannot_commit_a_product_image:
  "code_publish_checked_debit Code_Debit_Publication_Pending observed frame request head candidate = frame"
  by (simp add: code_publish_checked_debit_def)

theorem the_ready_source_debit_publishes_the_exact_existing_product_image_atomically:
  assumes ready: "guarded = Code_Debit_Publication_Ready scope key"
    and observed: "observed = image_ordered_control frame"
    and pending: "control_decisions observed (original_call request) = Some (request,Ref_Pending)"
    and decoded: "decode_wire_packet (original_packet request) = Some packet"
  shows "code_publish_checked_debit guarded observed frame request head candidate =
      commit_reference_debit observed frame request head candidate"
    "image_authority (code_publish_checked_debit guarded observed frame request head candidate) = candidate"
    "control_head (image_ordered_control (code_publish_checked_debit guarded observed frame request head candidate)) = Some head"
    "image_transport (code_publish_checked_debit guarded observed frame request head candidate)
      (original_transport request) = Some (encode_wire_core (packet_core packet))"
proof -
  have same: "code_publish_checked_debit guarded observed frame request head candidate =
      commit_reference_debit observed frame request head candidate"
    by (simp add: code_publish_checked_debit_def ready)
  show "code_publish_checked_debit guarded observed frame request head candidate =
      commit_reference_debit observed frame request head candidate" by (rule same)
  note atomic = an_ordered_debit_publishes_the_exact_input_and_product_view_together[OF observed pending decoded]
  show "image_authority (code_publish_checked_debit guarded observed frame request head candidate) = candidate"
    using atomic same by (auto simp: Let_def)
  show "control_head (image_ordered_control (code_publish_checked_debit guarded observed frame request head candidate)) = Some head"
    using atomic same by (auto simp: Let_def)
  show "image_transport (code_publish_checked_debit guarded observed frame request head candidate)
      (original_transport request) = Some (encode_wire_core (packet_core packet))"
    using atomic same by (auto simp: Let_def)
qed

end
