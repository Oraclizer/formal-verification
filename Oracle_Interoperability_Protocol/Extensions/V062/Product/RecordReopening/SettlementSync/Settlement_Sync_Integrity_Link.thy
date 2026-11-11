theory Settlement_Sync_Integrity_Link
  imports "OIP_Retained_Transition_Integrity_Model_Link.Retained_Transition_Integrity_Model_Link"
    "OIP_Sync_V061_Position_Definitions.Sync_V061_Product"
    "OIP_Message_Code.Wire_Code_Fixed_Call_Request"
    "HOL-Library.Code_Target_Nat"
begin

text \<open>Scoped retained-image checks for the Credited and Synced inputs.
  Exact CommitRecord extents and canonical typed projections are supplied
  by the adapter. Credit covers the confirmed settlement shape. Sync
  reopens each exact Core and uses its named historical prefix. The
  preceding-history check is reported independently of first-path refusal.\<close>

record ssi_item =
  ssi_item_id :: client_call_id
  ssi_item_target :: nat
  ssi_item_position :: nat

record ssi_credit =
  ssi_credit_id :: client_call_id
  ssi_credit_binding :: code_source_binding
  ssi_credit_epoch :: nat
  ssi_credit_signed_revision :: nat
  ssi_credit_endpoint :: nat
  ssi_credit_position :: "nat option"
  ssi_credit_reference :: nat

record ssi_origin_slot =
  ssi_slot_binding :: code_source_binding
  ssi_slot_epoch :: nat
  ssi_slot_confirmed :: bool
  ssi_slot_settled :: "nat option"

definition ssi_credit_item_exact where
  "ssi_credit_item_exact ssi_saved ssi_item \<longleftrightarrow>
     ssi_credit_id ssi_saved = ssi_item_id ssi_item \<and>
     ssi_credit_position ssi_saved = Some (ssi_item_position ssi_item) \<and>
     ssi_credit_signed_revision ssi_saved = ssi_item_position ssi_item \<and>
     ssi_credit_endpoint ssi_saved = ssi_item_target ssi_item"

fun ssi_credit_effects where
  "ssi_credit_effects ssi_saved [] = []"
| "ssi_credit_effects ssi_saved (ssi_item # ssi_items) =
    (case map_of ssi_saved (ssi_item_id ssi_item) of None \<Rightarrow> ssi_credit_effects ssi_saved ssi_items
     | Some ssi_credit \<Rightarrow>
       (source_binding_origin (ssi_credit_binding ssi_credit),(ssi_credit,ssi_item)) # ssi_credit_effects ssi_saved ssi_items)"

definition ssi_credit_receipt_exact where
  "ssi_credit_receipt_exact ssi_effects ssi_slots ssi_settled ssi_evidence ssi_credit \<longleftrightarrow>
    (let ssi_binding = ssi_credit_binding ssi_credit; ssi_origin = source_binding_origin ssi_binding in
      case (map_of ssi_effects ssi_origin,map_of ssi_slots ssi_origin) of
        (Some (ssi_saved,ssi_item),Some ssi_slot) \<Rightarrow>
          List.member ssi_settled ssi_origin \<and> ssi_slot_binding ssi_slot = ssi_binding \<and>
          ssi_slot_epoch ssi_slot = ssi_credit_epoch ssi_credit \<and> ssi_slot_confirmed ssi_slot \<and>
          ssi_credit_position ssi_credit = Some (ssi_item_position ssi_item) \<and> ssi_item_id ssi_item = ssi_credit_id ssi_credit \<and>
          map_of ssi_evidence (ssi_credit_reference ssi_credit) = Some (ssi_binding,True)
       | _ \<Rightarrow> False)"

definition ssi_credit_guard where
  "ssi_credit_guard ssi_revision ssi_journal ssi_credits ssi_slots ssi_settled ssi_evidence =
    (if \<not> sorted_wrt (<) (map ssi_item_position ssi_journal) \<or>
        \<not> list_all (\<lambda>ssi_item. ssi_item_position ssi_item < ssi_revision) ssi_journal then [2]
     else let ssi_effects = ssi_credit_effects ssi_credits ssi_journal in
       case List.find (\<lambda>(ssi_origin,(ssi_saved,ssi_item)). \<not> ssi_credit_item_exact ssi_saved ssi_item) ssi_effects of
         Some (ssi_origin,(ssi_saved,ssi_item)) \<Rightarrow>
           [3,fst (ssi_item_id ssi_item),snd (ssi_item_id ssi_item),
             (case ssi_credit_position ssi_saved of None \<Rightarrow> 0 | Some ssi_pos \<Rightarrow> Suc ssi_pos),
             ssi_credit_signed_revision ssi_saved,ssi_item_position ssi_item,ssi_credit_endpoint ssi_saved,ssi_item_target ssi_item]
       | None \<Rightarrow>
         if distinct (map fst ssi_effects) \<and> list_all (\<lambda>ssi_origin. List.member (map fst ssi_effects) ssi_origin) ssi_settled \<and>
           list_all (\<lambda>(ssi_origin,ssi_slot). ssi_slot_settled ssi_slot =
             map_option (\<lambda>(ssi_saved,ssi_item). ssi_item_position ssi_item) (map_of ssi_effects ssi_origin)) ssi_slots \<and>
           list_all (ssi_credit_receipt_exact ssi_effects ssi_slots ssi_settled ssi_evidence) (map snd ssi_credits)
         then [1] else [4])"

lemma ssi_credit_item_requires_both_exact_commit_coordinates:
  assumes "ssi_credit_item_exact ssi_saved ssi_item"
  shows "ssi_credit_position ssi_saved = Some (ssi_item_position ssi_item)"
    "ssi_credit_signed_revision ssi_saved = ssi_item_position ssi_item"
    "ssi_credit_id ssi_saved = ssi_item_id ssi_item"
    "ssi_credit_endpoint ssi_saved = ssi_item_target ssi_item"
  using assms by (simp_all add: ssi_credit_item_exact_def)

type_synonym ssi_entries = "(sync_stream \<times> sync_entry) list"

record ssi_sync_context =
  ssi_sync_deployment :: nat
  ssi_sync_current_cut :: product_cut
  ssi_sync_endpoints :: "nat list"
  ssi_sync_assets :: "nat list"
  ssi_other_claims :: "client_call_id list"
  ssi_sync_bindings :: "(authenticated_message_id \<times> wire_bytes) list"
  ssi_sync_journal :: "ssi_item list"
  ssi_sync_history :: "ssi_entries list"

definition ssi_mode_ok where
  "ssi_mode_ok ssi_request ssi_prior \<longleftrightarrow>
    (case (sync_mode ssi_request,ssi_prior) of
       (Sync_Initial,None) \<Rightarrow> sync_claimed_prior ssi_request = None
     | (Sync_Incremental,Some ssi_entry) \<Rightarrow> sync_claimed_prior ssi_request = Some (sync_commitment ssi_entry)
     | (Sync_Full,Some ssi_entry) \<Rightarrow> sync_claimed_prior ssi_request = None
     | _ \<Rightarrow> False)"

lemma ssi_mode_is_existing_sync_mode_with_full_resync_assumed_at_reopening:
  assumes "sync_predecessor ssi_statement = sync_claimed_prior ssi_request"
    "(sync_session ssi_request,sync_key ssi_request) \<in> sync_full_scope ssi_policy"
  shows "ssi_mode_ok ssi_request ssi_prior = sync_mode_ok ssi_policy ssi_request ssi_statement ssi_prior"
  using assms by (cases ssi_prior; cases "sync_mode ssi_request") (simp_all add: ssi_mode_ok_def)

definition ssi_fresh where
  "ssi_fresh ssi_entries ssi_events ssi_request \<longleftrightarrow>
    \<not> List.member ssi_events (sync_event_key ssi_request) \<and>
    (case map_of ssi_entries (sync_key ssi_request) of None \<Rightarrow> True
       | Some ssi_prior \<Rightarrow> sync_position ssi_prior < sync_position (sync_requested ssi_request))"

lemma ssi_fresh_is_the_existing_sync_position_and_event_check:
  assumes "sync_retained ssi_receiver (sync_key ssi_request) = map_of ssi_entries (sync_key ssi_request)"
    "(sync_used_events ssi_receiver (sync_event_key ssi_request) = None) = (\<not> List.member ssi_events (sync_event_key ssi_request))"
  shows "ssi_fresh ssi_entries ssi_events ssi_request = sync_position_and_event_fresh ssi_receiver ssi_request"
  using assms by (cases "map_of ssi_entries (sync_key ssi_request)")
    (simp_all add: ssi_fresh_def sync_position_and_event_fresh_def)

definition ssi_commitment_at where
  "ssi_commitment_at ssi_prefixes ssi_position ssi_stream =
    (case native_history_read_value True (\<lambda>ssi_entries. map_of ssi_entries ssi_stream) (Suc ssi_position) ssi_prefixes of
       None \<Rightarrow> None | Some (ssi_index,ssi_value) \<Rightarrow> ssi_value)"

lemma ssi_commitment_lookup_uses_exact_next_prefix:
  assumes "Suc ssi_position < length ssi_prefixes"
  shows "ssi_commitment_at ssi_prefixes ssi_position ssi_stream =
         map_of (ssi_prefixes ! Suc ssi_position) ssi_stream"
  using assms by (simp add: ssi_commitment_at_def native_history_read_value_def)

definition ssi_sync_row where
  "ssi_sync_row ssi_context ssi_id ssi_position ssi_exact =
    (case sync_decode_core ssi_exact of None \<Rightarrow> Inl [2,fst ssi_id,snd ssi_id]
     | Some ssi_core \<Rightarrow>
       (case sync_read_operands ssi_core of None \<Rightarrow> Inl [2,fst ssi_id,snd ssi_id]
        | Some ssi_request \<Rightarrow>
          let ssi_current = ssi_sync_current_cut ssi_context; ssi_target = wire_target_domain ssi_core;
              ssi_signed_revision = cut_revision (sync_signed_cut ssi_request)
          in if sync_call ssi_request \<noteq> ssi_id \<or> wire_deployment ssi_core \<noteq> ssi_sync_deployment ssi_context \<or>
                \<not> List.member (ssi_sync_endpoints ssi_context) ssi_target \<or>
                \<not> List.member (ssi_sync_assets ssi_context) (fst (sync_key ssi_request)) \<or>
                cut_authority_epoch (sync_signed_cut ssi_request) > cut_authority_epoch ssi_current \<or>
                map_of (ssi_sync_bindings ssi_context) (authenticated_wire_message_id ssi_core) \<noteq> Some ssi_exact \<or>
                List.member (ssi_other_claims ssi_context) ssi_id
             then Inl [2,fst ssi_id,snd ssi_id]
             else if ssi_signed_revision \<noteq> ssi_position \<or> ssi_position \<ge> cut_revision ssi_current \<or>
                \<not> list_ex (\<lambda>ssi_item. ssi_item_position ssi_item = ssi_position \<and> ssi_item_id ssi_item = ssi_id \<and>
                   ssi_item_target ssi_item = ssi_target) (ssi_sync_journal ssi_context)
             then Inl [3,fst ssi_id,snd ssi_id,ssi_signed_revision,ssi_position,ssi_target]
             else Inr (ssi_position,ssi_request)))"

fun ssi_sync_rows where
  "ssi_sync_rows ssi_context [] = Inr []"
| "ssi_sync_rows ssi_context ((ssi_id,(ssi_position,ssi_exact)) # ssi_rows) =
    (case ssi_sync_row ssi_context ssi_id ssi_position ssi_exact of Inl ssi_failure \<Rightarrow> Inl ssi_failure
     | Inr ssi_call \<Rightarrow>
       (case ssi_sync_rows ssi_context ssi_rows of Inl ssi_failure \<Rightarrow> Inl ssi_failure
        | Inr ssi_calls \<Rightarrow> Inr (ssi_call # ssi_calls)))"

fun ssi_sync_replay where
  "ssi_sync_replay ssi_prefixes [] ssi_entries ssi_events = Inr (ssi_entries,ssi_events)"
| "ssi_sync_replay ssi_prefixes ((ssi_position,ssi_request) # ssi_calls) ssi_entries ssi_events =
    (let ssi_key = sync_key ssi_request; ssi_entry = sync_requested ssi_request in
       if \<not> ssi_mode_ok ssi_request (map_of ssi_entries ssi_key) \<or> \<not> ssi_fresh ssi_entries ssi_events ssi_request
       then Inl [5,ssi_position]
       else if ssi_commitment_at ssi_prefixes ssi_position ssi_key \<noteq> Some ssi_entry
       then Inl [6,ssi_position,Suc ssi_position,fst ssi_key,snd ssi_key]
       else ssi_sync_replay ssi_prefixes ssi_calls
         ((ssi_key,ssi_entry) # filter (\<lambda>ssi_pair. fst ssi_pair \<noteq> ssi_key) ssi_entries) (sync_event_key ssi_request # ssi_events))"

definition ssi_sync_guard where
  "ssi_sync_guard ssi_context ssi_retained ssi_entries ssi_events =
    (case ssi_sync_rows ssi_context ssi_retained of Inl ssi_failure \<Rightarrow> ssi_failure
     | Inr ssi_calls \<Rightarrow>
       if \<not> distinct (map fst ssi_calls) then [4]
       else case ssi_sync_replay (ssi_sync_history ssi_context) (sort_key fst ssi_calls) [] [] of
         Inl ssi_failure \<Rightarrow> ssi_failure
       | Inr (ssi_replayed,ssi_seen) \<Rightarrow>
         if length ssi_replayed = length ssi_entries \<and>
           list_all (\<lambda>(ssi_key,ssi_entry). map_of ssi_entries ssi_key = Some ssi_entry) ssi_replayed \<and>
           set ssi_seen = set ssi_events then [1] else [7])"

definition ssi_later_history where
  "ssi_later_history ssi_old ssi_current = rti_preceding_history ssi_old ssi_current"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ssi_credit_item_requires_both_exact_commit_coordinates
    ssi_mode_is_existing_sync_mode_with_full_resync_assumed_at_reopening ssi_fresh_is_the_existing_sync_position_and_event_check
    ssi_commitment_lookup_uses_exact_next_prefix rti_reference_advance_preserves_preceding_history
    sync_decoded_core_has_the_exact_bytes})
  then () else error "Unexpected oracle in settlement and Sync retained integrity"
\<close>

end
