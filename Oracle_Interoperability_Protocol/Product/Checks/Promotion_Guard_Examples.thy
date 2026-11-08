theory Promotion_Guard_Examples
  imports Recovery_Examples
begin

definition endpoint_without_call_partition where
  "endpoint_without_call_partition directory policy authenticate verify token proof target operation actor call_id payload source \<longleftrightarrow>
    (let envelope = payload_envelope payload in
     proof_epoch proof = cut_authority_epoch (envelope_cut envelope) \<and>
     (\<exists>identity. authenticate token = Some identity \<and> identity_principal identity = actor \<and>
       active_identity directory identity proof source \<and> proof_session proof = envelope_session envelope \<and>
       product_identity_bound actor (actor, snd call_id) envelope source \<and>
       command_target envelope (envelope_command envelope) = target \<and>
       verify identity proof target operation call_id payload \<and>
       policy identity target (envelope_asset envelope) operation (proof_epoch proof)))"

lemma removing_only_the_call_id_partition_admits_the_same_signed_foreign_namespace:
  fixes verify :: "registered_identity \<Rightarrow> session_proof \<Rightarrow> nat \<Rightarrow> endpoint_use \<Rightarrow> client_call_id \<Rightarrow> product_call_payload \<Rightarrow> bool"
  defines "verify \<equiv> \<lambda>_ _ _ _ call_id _. call_id = (8,1)"
  shows "\<not> endpoint_call_allowed identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory verify
      7 (identity_case_proof 1 9) 0 Execute_Ordinary 7 (8,1) identity_case_payload handover_case_source \<and>
    endpoint_without_call_partition identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory verify
      7 (identity_case_proof 1 9) 0 Execute_Ordinary 7 (8,1) identity_case_payload handover_case_source"
proof -
  have source: "product_identity_bound 7 (7,1) (payload_envelope identity_case_payload) handover_case_source"
    using current_identity_can_submit_the_bound_request
    by (auto simp: endpoint_call_allowed_def endpoint_call_identity_def Let_def)
  have denied: "\<not> endpoint_call_allowed identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory verify
      7 (identity_case_proof 1 9) 0 Execute_Ordinary 7 (8,1) identity_case_payload handover_case_source"
    by (simp add: endpoint_call_allowed_def endpoint_call_identity_def product_identity_bound_def Let_def)
  have weakened: "endpoint_without_call_partition identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory verify
      7 (identity_case_proof 1 9) 0 Execute_Ordinary 7 (8,1) identity_case_payload handover_case_source"
    using source by (simp add: endpoint_without_call_partition_def verify_def active_identity_def product_identity_bound_def current_product_cut_def
      identity_case_payload_def lock_example_envelope_def lock_example_dispatch_def sample_request_def handover_case_defs)
  show ?thesis by (rule conjI[OF denied weakened])
qed

definition without_successor_approval where
  "without_successor_approval approve identity proposal \<longleftrightarrow>
    identity_principal identity = transfer_successor proposal \<or> approve identity proposal"

lemma removing_only_the_successor_approval_admits_the_same_unconsented_transfer:
  "let approve = (\<lambda>identity (_::ownership_transfer). identity_principal identity = 7) in
   \<not> handover_is_authorized identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory approve
     7 8 99 {99} {0,2} handover_case_proposal handover_case_source \<and>
   handover_is_authorized identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory
     (without_successor_approval approve) 7 8 99 {99} {0,2} handover_case_proposal handover_case_source"
  using handover_needs_the_successor_consent
  by (simp add: without_successor_approval_def handover_is_authorized_def handover_case_defs owner_of_product_def
    current_product_cut_def lock_context_batch_is_newer_def active_identity_def)

definition reopen_without_record_binding where
  "reopen_without_record_binding profile attachment store =
    (case (attachment, committed_head store) of (Some current, Some head) \<Rightarrow>
       if attachment_profile current \<noteq> profile \<or> head_profile head \<noteq> profile then None
       else map_option (\<lambda>record. reopen_retained_product (attachment_connection current) (image_records record))
              (flushed_records store head)
     | _ \<Rightarrow> None)"

lemma removing_only_the_record_binding_reopens_changed_bytes_at_the_current_sequence:
  "let digest = (\<lambda>record. case image_parent record of None \<Rightarrow> 0 | Some parent \<Rightarrow> Suc parent);
       current = head_for_record digest recovery_case_current;
       replaced = recovery_case_old\<lparr>image_sequence := 1, image_parent := Some 2\<rparr>;
       store = \<lparr>flushed_records = (\<lambda>head. if head = current then Some replaced else None),
                committed_head = Some current\<rparr>
   in reopen_from_authenticated_head digest recovery_case_profile (Some recovery_case_attachment) store = None \<and>
      reopen_without_record_binding recovery_case_profile (Some recovery_case_attachment) store =
        Some (reopen_retained_product Authority_Connected (image_records recovery_case_old))"
  by (simp add: reopen_from_authenticated_head_def reopen_without_record_binding_def head_for_record_def
    recovery_case_current_def recovery_case_old_def recovery_case_attachment_def Let_def)

end
