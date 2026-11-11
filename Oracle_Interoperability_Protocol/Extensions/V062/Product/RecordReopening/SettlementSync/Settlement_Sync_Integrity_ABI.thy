theory Settlement_Sync_Integrity_ABI
  imports Settlement_Sync_Integrity_Link
begin

fun ssi_collect :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "ssi_collect ssi_f [] = Some []"
| "ssi_collect ssi_f (ssi_x # ssi_xs) = Option.bind (ssi_f ssi_x) (\<lambda>ssi_y. map_option (Cons ssi_y) (ssi_collect ssi_f ssi_xs))"

fun ssi_pair_words :: "nat list \<Rightarrow> (nat \<times> nat) option" where
  "ssi_pair_words [ssi_a,ssi_b] = Some (ssi_a,ssi_b)"
| "ssi_pair_words _ = None"

fun ssi_binding_words :: "nat list \<Rightarrow> code_source_binding option" where
  "ssi_binding_words [ssi_domain,ssi_event,ssi_asset,ssi_owner,ssi_dst,ssi_recipient,ssi_amount] =
     Some \<lparr>source_binding_origin = (ssi_domain,ssi_event),source_binding_asset = ssi_asset,source_binding_owner = ssi_owner,
       source_binding_destination = ssi_dst,source_binding_recipient = ssi_recipient,source_binding_amount = ssi_amount\<rparr>"
| "ssi_binding_words _ = None"

fun ssi_item_words where
  "ssi_item_words [ssi_ns,ssi_seq,ssi_target,ssi_position] =
     Some \<lparr>ssi_item_id = (ssi_ns,ssi_seq),ssi_item_target = ssi_target,ssi_item_position = ssi_position\<rparr>"
| "ssi_item_words _ = None"

fun ssi_credit_words where
  "ssi_credit_words [ssi_ns,ssi_seq,ssi_domain,ssi_event,ssi_asset,ssi_owner,ssi_dst,ssi_recipient,ssi_amount,
       ssi_epoch,ssi_revision,ssi_target,ssi_present,ssi_position,ssi_reference] =
    (if ssi_present \<le> 1 then
       map_option (\<lambda>ssi_b. ((ssi_ns,ssi_seq),\<lparr>ssi_credit_id = (ssi_ns,ssi_seq),ssi_credit_binding = ssi_b,
         ssi_credit_epoch = ssi_epoch,ssi_credit_signed_revision = ssi_revision,ssi_credit_endpoint = ssi_target,
         ssi_credit_position = (if ssi_present = 1 then Some ssi_position else None),ssi_credit_reference = ssi_reference\<rparr>))
         (ssi_binding_words [ssi_domain,ssi_event,ssi_asset,ssi_owner,ssi_dst,ssi_recipient,ssi_amount])
     else None)"
| "ssi_credit_words _ = None"

fun ssi_slot_words where
  "ssi_slot_words [ssi_key_domain,ssi_key_event,ssi_domain,ssi_event,ssi_asset,ssi_owner,ssi_dst,ssi_recipient,ssi_amount,
       ssi_epoch,ssi_confirmed,ssi_present,ssi_position] =
    (if ssi_confirmed \<le> 1 \<and> ssi_present \<le> 1 then
      map_option (\<lambda>ssi_b. ((ssi_key_domain,ssi_key_event),\<lparr>ssi_slot_binding = ssi_b,
        ssi_slot_epoch = ssi_epoch,ssi_slot_confirmed = (ssi_confirmed = 1),
        ssi_slot_settled = (if ssi_present = 1 then Some ssi_position else None)\<rparr>))
        (ssi_binding_words [ssi_domain,ssi_event,ssi_asset,ssi_owner,ssi_dst,ssi_recipient,ssi_amount])
     else None)"
| "ssi_slot_words _ = None"

fun ssi_evidence_words where
  "ssi_evidence_words (ssi_reference # ssi_confirmed # ssi_binding) =
    (if ssi_confirmed \<le> 1 then
      map_option (\<lambda>ssi_b. (ssi_reference,(ssi_b,ssi_confirmed = 1))) (ssi_binding_words ssi_binding) else None)"
| "ssi_evidence_words _ = None"

fun ssi_credit_input :: "nat list list list \<Rightarrow> nat list option" where
  "ssi_credit_input [[[ssi_revision]],ssi_journal,ssi_credits,ssi_slots,ssi_settled,ssi_evidence] =
    (case (ssi_collect ssi_item_words ssi_journal,ssi_collect ssi_credit_words ssi_credits,
       ssi_collect ssi_slot_words ssi_slots,ssi_collect ssi_pair_words ssi_settled,ssi_collect ssi_evidence_words ssi_evidence) of
       (Some ssi_items,Some ssi_calls,Some ssi_origin_slots,Some ssi_settled_keys,Some ssi_terminal) \<Rightarrow>
         Some (ssi_credit_guard ssi_revision ssi_items ssi_calls ssi_origin_slots ssi_settled_keys ssi_terminal)
      | _ \<Rightarrow> None)"
| "ssi_credit_input _ = None"

fun ssi_entry_words :: "nat list \<Rightarrow> (sync_stream \<times> sync_entry) option" where
  "ssi_entry_words (ssi_asset # ssi_origin # ssi_position # ssi_epoch # ssi_event # ssi_commitment) =
     (if length ssi_commitment = 32 \<and> rti_octets ssi_commitment then
       Some ((ssi_asset,ssi_origin),\<lparr>sync_commitment = ssi_commitment,sync_position = ssi_position,
          sync_origin_epoch = ssi_epoch,sync_event = ssi_event\<rparr>) else None)"
| "ssi_entry_words _ = None"

fun ssi_transport_words where
  "ssi_transport_words [[ssi_dep,ssi_source,ssi_principal],ssi_uuid,ssi_core] =
    (if length ssi_uuid = 16 then Some ((ssi_dep,ssi_source,ssi_principal,ssi_uuid),ssi_core) else None)"
| "ssi_transport_words _ = None"

fun ssi_synced_words where
  "ssi_synced_words [[ssi_ns,ssi_seq,ssi_position],ssi_exact] = Some ((ssi_ns,ssi_seq),(ssi_position,ssi_exact))"
| "ssi_synced_words _ = None"

fun ssi_sync_input :: "nat list list list list \<Rightarrow> nat list option" where
  "ssi_sync_input [[[[ssi_dep,ssi_epoch,ssi_revision],ssi_endpoints,ssi_assets]],[ssi_journal],[ssi_claimed],
       ssi_transports,ssi_retained,ssi_history,[ssi_entries],[ssi_events]] =
    (case (ssi_collect ssi_item_words ssi_journal,ssi_collect ssi_pair_words ssi_claimed,
       ssi_collect ssi_transport_words ssi_transports,ssi_collect ssi_synced_words ssi_retained,
       ssi_collect (ssi_collect ssi_entry_words) ssi_history,
       ssi_collect ssi_entry_words ssi_entries,ssi_collect ssi_pair_words ssi_events) of
       (Some ssi_items,Some ssi_ids,Some ssi_bindings,Some ssi_calls,Some ssi_prefixes,Some ssi_tips,Some ssi_seen) \<Rightarrow>
         let ssi_context = \<lparr>ssi_sync_deployment = ssi_dep,
            ssi_sync_current_cut = \<lparr>cut_authority_epoch = ssi_epoch,cut_revision = ssi_revision\<rparr>,
            ssi_sync_endpoints = ssi_endpoints,ssi_sync_assets = ssi_assets,ssi_other_claims = ssi_ids,
            ssi_sync_bindings = ssi_bindings,ssi_sync_journal = ssi_items,ssi_sync_history = ssi_prefixes\<rparr>
         in Some (ssi_sync_guard ssi_context ssi_calls ssi_tips ssi_seen)
      | _ \<Rightarrow> None)"
| "ssi_sync_input _ = None"

fun ssi_hash_words where
  "ssi_hash_words [ssi_raw,ssi_sha] = (if length ssi_sha = 32 then Some (ssi_raw,ssi_sha) else None)"
| "ssi_hash_words _ = None"

definition ssi_exact_extents where
  "ssi_exact_extents ssi_hash ssi_raw_header =
    (case ssi_raw_header of [[ssi_seq,ssi_offset,ssi_len,ssi_prev_seq,ssi_prev_offset,ssi_prev_len,ssi_file_len],
        ssi_candidate,ssi_previous,ssi_candidate_sha,ssi_previous_sha] \<Rightarrow>
       0 < ssi_len \<and> 0 < ssi_prev_len \<and>
       length ssi_candidate = ssi_len \<and> length ssi_previous = ssi_prev_len \<and>
       ssi_offset + ssi_len \<le> ssi_file_len \<and> ssi_prev_offset + ssi_prev_len \<le> ssi_offset \<and>
       Suc ssi_prev_seq = ssi_seq \<and> ssi_hash ssi_candidate = Some ssi_candidate_sha \<and>
       ssi_hash ssi_previous = Some ssi_previous_sha
     | _ \<Rightarrow> False)"

definition ssi_nat_abi ::
  "nat list list \<Rightarrow> nat list list list \<Rightarrow> nat list list list \<Rightarrow> nat list list list \<Rightarrow>
    nat list list list list \<Rightarrow> nat list list \<Rightarrow> nat list list \<Rightarrow> nat list list" where
  "ssi_nat_abi ssi_raw_header ssi_hash_rows ssi_previous_credit ssi_candidate_credit ssi_sync_rows_value ssi_old_prefixes ssi_next_prefixes =
    (case ssi_collect ssi_hash_words ssi_hash_rows of None \<Rightarrow> [[0]] | Some ssi_hashes \<Rightarrow>
      if \<not> ssi_exact_extents (map_of ssi_hashes) ssi_raw_header then [[0]]
      else (case (ssi_credit_input ssi_previous_credit,ssi_credit_input ssi_candidate_credit,ssi_sync_input ssi_sync_rows_value) of
        (Some ssi_prior_credit,Some ssi_credit_result,Some ssi_sync_result) \<Rightarrow>
          let ssi_history_result = ssi_later_history ssi_old_prefixes ssi_next_prefixes;
              ssi_first = (if ssi_credit_result \<noteq> [1] then 2 else if ssi_sync_result \<noteq> [1] then 3
                else if ssi_prior_credit \<noteq> [1] then 4 else if \<not> ssi_history_result then 5 else 1)
          in [[ssi_first,if ssi_history_result then 1 else 0],ssi_credit_result,ssi_sync_result,ssi_prior_credit]
       | _ \<Rightarrow> [[0]]))"

definition ssi_integer_abi ::
  "integer list list \<Rightarrow> integer list list list \<Rightarrow> integer list list list \<Rightarrow> integer list list list \<Rightarrow>
    integer list list list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list" where
  "ssi_integer_abi ssi_raw_header ssi_hash_rows ssi_previous_credit ssi_candidate_credit ssi_sync_rows_value ssi_old_prefixes ssi_next_prefixes =
    (if list_all (list_all (list_all rti_u64)) [ssi_raw_header,ssi_old_prefixes,ssi_next_prefixes] \<and>
        list_all (list_all (list_all (list_all rti_u64))) [ssi_hash_rows,ssi_previous_credit,ssi_candidate_credit] \<and>
        list_all (list_all (list_all (list_all rti_u64))) ssi_sync_rows_value
     then map (map integer_of_nat) (ssi_nat_abi (map (map nat_of_integer) ssi_raw_header)
        (map (map (map nat_of_integer)) ssi_hash_rows) (map (map (map nat_of_integer)) ssi_previous_credit)
        (map (map (map nat_of_integer)) ssi_candidate_credit) (map (map (map (map nat_of_integer))) ssi_sync_rows_value)
        (map (map nat_of_integer) ssi_old_prefixes) (map (map nat_of_integer) ssi_next_prefixes))
     else [[0]])"

export_code ssi_integer_abi in SML
  module_name OIP_Settlement_Sync_Integrity_ABI file_prefix "oip_settlement_sync_integrity_abi"

end
