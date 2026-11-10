theory Sync_V061_ID_Guard_ABI
  imports "OIP_Sync_V061_Product_ABI.Sync_V061_Product_ABI"
begin

definition sync_id_guard_state ::
  "nat \<Rightarrow> nat \<Rightarrow> product_cut \<Rightarrow> product_session_id \<Rightarrow> product_principal \<Rightarrow>
   nat \<Rightarrow> product_asset \<Rightarrow> sync_abi_receiver" where
  "sync_id_guard_state row_deployment row_target row_live_cut row_session row_principal row_domain row_asset =
    (let row_snapshot = \<lparr>sync_entries = (\<lambda>_. None), sync_product_value = ()\<rparr>;
         row_epoch = cut_authority_epoch row_live_cut;
         row_policy = sync_abi_policy row_deployment [(row_session,row_principal,row_epoch,row_domain)] [(row_session,row_asset)] [] [] []
     in \<lparr>sync_deployment_at = row_deployment, sync_target_at = row_target, sync_receiver_epoch = row_epoch,
          sync_genesis = row_snapshot, sync_revision_tail = replicate (cut_revision row_live_cut) row_snapshot,
          sync_selected_policy = row_policy, sync_used_events = (\<lambda>_. None),
          sync_outcome_table = (\<lambda>_. None)\<rparr>)"

definition sync_id_guard_gate where
  "sync_id_guard_gate row_call_id row_session row_asset row_receipt_allowed row_connected row_other row_ordered =
    \<lparr>sync_endpoint_up = True, sync_source_connected = row_connected, sync_registered_asset = (\<lambda>row_a. row_a = row_asset),
     sync_other_claimed = (\<lambda>row_id. row_id = row_call_id \<and> row_other),
     sync_ordered_debit = (\<lambda>row_id. row_id = row_call_id \<and> row_ordered),
     sync_receipt_granted = (\<lambda>row_s row_a. row_s = row_session \<and> row_a = row_asset \<and> row_receipt_allowed)\<rparr>"

fun sync_id_guard_status :: "sync_reference_result \<Rightarrow> nat list" where
  "sync_id_guard_status (Sync_Transport_Refusal row_reason) = [0,code_transport_refusal_number row_reason]"
| "sync_id_guard_status Sync_Product_Refusal = [1,77]"
| "sync_id_guard_status (Sync_Reference_Outcome row_outcome) = [2,fst (sync_outcome_wire row_outcome)]"

definition sync_id_guard_observe where
  "sync_id_guard_observe row_request row_state row_result =
    sync_id_guard_status row_result @ sync_abi_cut_words (sync_current_cut row_state) @
      [if sync_outcome_table row_state (sync_call row_request) = None then 0 else 1,
       if sync_retained row_state (sync_key row_request) = None then 0 else 1]"

definition sync_id_guard_octets :: "integer list \<Rightarrow> bool" where
  "sync_id_guard_octets row_raw = list_all (\<lambda>row_octet. 0 \<le> row_octet \<and> row_octet < 256) row_raw"

text \<open>Inputs are already admitted by the reference transport. The comparison
  repeats canonical decoding and then supplies None to the parent boundary.\<close>

definition sync_id_guard_after_admission ::
  "integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> bool list \<Rightarrow> integer list option" where
  "sync_id_guard_after_admission row_raw row_original row_metadata row_flags =
    (if \<not> sync_id_guard_octets row_raw \<or> \<not> sync_id_guard_octets row_original \<or>
        \<not> list_all (\<lambda>row_word. 0 \<le> row_word \<and> row_word < 2^64) row_metadata then None
     else case (map nat_of_integer row_metadata,row_flags) of
       ([row_deployment,row_target,row_epoch,row_revision,row_principal,row_domain,row_session,row_asset,row_origin,row_namespace,row_sequence,row_signed_epoch,row_signed_revision],
        [row_execute_allowed,row_receipt_allowed,row_connected,row_other,row_ordered]) \<Rightarrow>
         if \<not> row_execute_allowed \<or> \<not> (row_other \<or> row_ordered) then None
         else Option.bind (sync_decode_packet (map nat_of_integer row_raw)) (\<lambda>row_packet.
           let row_core = packet_core row_packet in
           if encode_wire_core row_core \<noteq> map nat_of_integer row_original then None
           else Option.bind (sync_read_operands row_core) (\<lambda>row_request.
             let row_call_id = (row_namespace,row_sequence);
                 row_signed_cut = \<lparr>cut_authority_epoch = row_signed_epoch,cut_revision = row_signed_revision\<rparr>;
                 row_live_cut = \<lparr>cut_authority_epoch = row_epoch,cut_revision = row_revision\<rparr>;
                 row_state = sync_id_guard_state row_deployment row_target row_live_cut row_session row_principal row_domain row_asset;
                 row_gate = sync_id_guard_gate row_call_id row_session row_asset row_receipt_allowed row_connected row_other row_ordered
             in if sync_call row_request \<noteq> row_call_id \<or> sync_key row_request \<noteq> (row_asset,row_origin) \<or>
                   sync_signed_cut row_request \<noteq> row_signed_cut \<or> \<not> sync_execute_allowed row_state row_core row_request then None
                else case sync_reference_product None row_gate (\<lambda>_ _ _. False) row_core row_state of
                  (row_updated,row_result) \<Rightarrow> Some (map integer_of_nat (sync_id_guard_observe row_request row_updated row_result))))
      | _ \<Rightarrow> None)"

lemma sync_id_guard_state_uses_the_live_cut:
  "sync_current_cut (sync_id_guard_state row_deployment row_target row_live_cut row_session row_principal row_domain row_asset) = row_live_cut"
  by (cases row_live_cut) (simp add: sync_id_guard_state_def sync_reference_history_def reference_observed_cut_def Let_def)

lemma sync_id_guard_absence_projection_is_exact:
  "sync_outcome_table (sync_id_guard_state row_deployment row_target row_live_cut row_session row_principal row_domain row_asset) row_call_id = None"
  "sync_retained (sync_id_guard_state row_deployment row_target row_live_cut row_session row_principal row_domain row_asset) stream = None"
proof -
  show "sync_outcome_table (sync_id_guard_state row_deployment row_target row_live_cut row_session row_principal row_domain row_asset) row_call_id = None"
    by (simp add: sync_id_guard_state_def Let_def)
  show "sync_retained (sync_id_guard_state row_deployment row_target row_live_cut row_session row_principal row_domain row_asset) stream = None"
    by (cases "cut_revision row_live_cut") (simp_all add: sync_id_guard_state_def sync_reference_history_def Let_def)
qed

lemma sync_id_guard_verifier_is_irrelevant_after_either_claim:
  assumes row_parsed: "sync_read_operands row_core = Some row_request"
    and row_claim: "sync_ordered_debit row_gate (sync_call row_request) \<or>
      (sync_other_claimed row_gate (sync_call row_request) \<and> sync_outcome_table row_state (sync_call row_request) = None)"
  shows "sync_reference_product None row_gate row_verify row_core row_state = sync_reference_product None row_gate row_alternative row_core row_state"
proof (cases "sync_ordered_debit row_gate (sync_call row_request)")
  case True
  then show ?thesis
    by (simp add: sync_reference_reserved_debit_id_refuses_before_execution[OF row_parsed True])
next
  case False
  have row_absent: "sync_outcome_table row_state (sync_call row_request) = None"
    and row_other: "sync_other_claimed row_gate (sync_call row_request)" using row_claim False by auto
  show ?thesis
    by (simp add: sync_reference_other_call_collision_is_refused_without_record[OF row_parsed False row_absent row_other])
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_id_guard_state_uses_the_live_cut sync_id_guard_absence_projection_is_exact
    sync_id_guard_verifier_is_irrelevant_after_either_claim})
  then () else error "Unexpected oracle in the SyncCommitment ID guard ABI"
\<close>

export_code sync_id_guard_after_admission
  in SML module_name OIP_Sync_ID_Guard_ABI file_prefix "oip_sync_id_guard_abi"

end
