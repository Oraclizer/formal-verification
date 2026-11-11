theory Unpublished_Read_ABI
  imports Unpublished_Read_Link
begin

fun ur_collect :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "ur_collect ur_f [] = Some []"
| "ur_collect ur_f (ur_x # ur_xs) =
     Option.bind (ur_f ur_x) (\<lambda>ur_y. map_option (Cons ur_y) (ur_collect ur_f ur_xs))"

fun ur_binding_from_words :: "nat list \<Rightarrow> code_source_binding option" where
  "ur_binding_from_words [ur_domain,ur_event,ur_asset,ur_owner,ur_dest,ur_recipient,ur_amount] =
    Some \<lparr>source_binding_origin = (ur_domain,ur_event),source_binding_asset = ur_asset,
      source_binding_owner = ur_owner,source_binding_destination = ur_dest,source_binding_recipient = ur_recipient,
      source_binding_amount = ur_amount\<rparr>"
| "ur_binding_from_words _ = None"

fun ur_publication_row :: "nat list \<Rightarrow> (code_source_binding \<times> bool) option" where
  "ur_publication_row (ur_published # ur_binding_words) =
    (if ur_published \<le> 1 then map_option (\<lambda>ur_b. (ur_b,ur_published = 1)) (ur_binding_from_words ur_binding_words)
     else None)"
| "ur_publication_row _ = None"

fun ur_asset_row :: "nat list \<Rightarrow> (nat \<times> nat) option" where
  "ur_asset_row [ur_asset,ur_units] = Some (ur_asset,ur_units)"
| "ur_asset_row _ = None"

fun ur_balance_row :: "nat list \<Rightarrow> (ur_account \<times> nat) option" where
  "ur_balance_row [ur_endpoint,ur_owner,ur_asset,ur_units] = Some ((ur_endpoint,ur_owner,ur_asset),ur_units)"
| "ur_balance_row _ = None"

fun ur_funding_row :: "nat list \<Rightarrow> ((source_key \<times> ur_account) \<times> nat) option" where
  "ur_funding_row [ur_domain,ur_event,ur_endpoint,ur_owner,ur_asset,ur_units] =
    Some (((ur_domain,ur_event),(ur_endpoint,ur_owner,ur_asset)),ur_units)"
| "ur_funding_row _ = None"

definition ur_mode_of :: "nat \<Rightarrow> reg_state option" where
  "ur_mode_of ur_tag =
    (if ur_tag = 1 then Some ACTIVE else if ur_tag = 2 then Some RESTRICTED
     else if ur_tag = 3 then Some FROZEN else if ur_tag = 4 then Some SEIZED
     else if ur_tag = 5 then Some CONFISCATED else None)"

fun ur_mode_row :: "nat list \<Rightarrow> ((nat \<times> nat) \<times> reg_state) option" where
  "ur_mode_row [ur_ep,ur_asset,ur_tag] = map_option (\<lambda>ur_state. ((ur_ep,ur_asset),ur_state)) (ur_mode_of ur_tag)"
| "ur_mode_row _ = None"

fun ur_prefix_from_tables :: "nat list list list \<Rightarrow> ur_prefix_input option" where
  "ur_prefix_from_tables [[ur_raw,ur_sha],ur_asset_rows,ur_balance_rows,ur_fund_rows,[ur_locks],
      ur_ordinary,ur_legal,ur_mode_rows] =
    (case (ur_collect ur_asset_row ur_asset_rows,ur_collect ur_balance_row ur_balance_rows,
       ur_collect ur_funding_row ur_fund_rows,ur_collect ur_publication_row ur_ordinary,
       ur_collect ur_publication_row ur_legal,ur_collect ur_mode_row ur_mode_rows) of
       (Some ur_assets,Some ur_total,Some ur_funds,Some ur_orders,Some ur_legal_orders,Some ur_regulation) \<Rightarrow>
         Some \<lparr>ur_prefix_raw = ur_raw,ur_prefix_digest = ur_sha,
           ur_prefix_view = \<lparr>ur_asset_values = ur_assets,ur_balances = ur_total,ur_root_funding = ur_funds,
             ur_locked_assets = ur_locks,ur_ordinary_rows = ur_orders,ur_legal_rows = ur_legal_orders,
             ur_modes = ur_regulation\<rparr>\<rparr>
       | _ \<Rightarrow> None)"
| "ur_prefix_from_tables _ = None"

fun ur_session_row :: "nat list \<Rightarrow> (nat \<times> (nat \<times> nat)) option" where
  "ur_session_row [ur_sid,ur_principal,ur_epoch] = Some (ur_sid,(ur_principal,ur_epoch))"
| "ur_session_row _ = None"

fun ur_hash_row :: "nat list list \<Rightarrow> (wire_bytes \<times> wire_bytes) option" where
  "ur_hash_row [ur_raw,ur_sha] =
    (if length ur_sha = 32 \<and> list_all (\<lambda>ur_b. ur_b < 256) ur_sha then Some (ur_raw,ur_sha) else None)"
| "ur_hash_row _ = None"

fun ur_mode_word :: "reg_state \<Rightarrow> nat" where
  "ur_mode_word ACTIVE = 1"
| "ur_mode_word RESTRICTED = 2"
| "ur_mode_word FROZEN = 3"
| "ur_mode_word SEIZED = 4"
| "ur_mode_word CONFISCATED = 5"

fun ur_value_words :: "application_value \<Rightarrow> nat list" where
  "ur_value_words (Units_Value ur_amount) = [1,ur_amount]"
| "ur_value_words (Regulatory_Value ur_mode) = [2,case ur_mode of None \<Rightarrow> 0 | Some ur_m \<Rightarrow> ur_mode_word ur_m]"
| "ur_value_words (Receipt_Value ur_receipt) = [0]"

fun ur_reply_words :: "product_read_reply \<Rightarrow> nat list" where
  "ur_reply_words (Current_Cut_Value ur_cut ur_result) =
    [1,cut_authority_epoch ur_cut,cut_revision ur_cut] @ ur_value_words ur_result"
| "ur_reply_words (Historical_Prefix_Value ur_index ur_result) = [2,ur_index] @ ur_value_words ur_result"
| "ur_reply_words Product_Read_Busy = [3]"
| "ur_reply_words Product_Read_Unavailable = [4]"
| "ur_reply_words Product_Read_Rejected = [5]"

fun ur_query_words :: "ur_query \<Rightarrow> nat list" where
  "ur_query_words (UR_Application ur_asset) = [1,ur_asset]"
| "ur_query_words (UR_Source (ur_endpoint,ur_owner,ur_asset)) = [2,ur_endpoint,ur_owner,ur_asset]"
| "ur_query_words (UR_Destination (ur_endpoint,ur_owner,ur_asset)) = [3,ur_endpoint,ur_owner,ur_asset]"
| "ur_query_words (UR_Regulatory ur_endpoint ur_asset) = [4,ur_endpoint,ur_asset]"

definition ur_bool_word :: "bool \<Rightarrow> nat" where
  "ur_bool_word ur_bool = (if ur_bool then 1 else 0)"

fun ur_case :: "(wire_bytes \<Rightarrow> wire_bytes option) \<Rightarrow> ur_capture \<Rightarrow> nat list list \<Rightarrow> nat list list" where
  "ur_case ur_hash ur_capture [ur_raw_query,ur_sha,[ur_expected_epoch,ur_expected_revision,ur_historical_index]] =
    (if ur_hash ur_raw_query \<noteq> Some ur_sha then [[0]]
     else case ur_decode_query ur_raw_query of None \<Rightarrow> [[0]]
       | Some ur_q \<Rightarrow>
         let ur_actual = ur_actual_cut ur_capture;
             ur_expected = \<lparr>cut_authority_epoch = ur_expected_epoch,cut_revision = ur_expected_revision\<rparr>;
             ur_views = map ur_prefix_view (ur_prefixes ur_capture);
             ur_bound = ur_session_bound ur_capture;
             ur_current = ur_native_current (ur_bound \<and> ur_current_permission ur_capture)
               (ur_observed_available ur_capture) ur_q ur_expected (cut_authority_epoch ur_actual) (cut_revision ur_actual) ur_views;
             ur_historical = ur_native_historical (ur_bound \<and> ur_historical_permission ur_capture)
               (ur_observed_available ur_capture) ur_q ur_historical_index ur_views
         in [ur_query_words ur_q,
             [ur_bool_word (ur_touches ur_q (ur_fixture_binding ur_capture)),
              ur_bool_word (ur_unpublished_touch ur_q (ur_views ! cut_revision ur_actual)),ur_bool_word ur_bound],
             ur_reply_words ur_current,ur_reply_words ur_historical])"
| "ur_case ur_hash ur_capture _ = [[0]]"

definition ur_nat_abi ::
  "nat list list \<Rightarrow> nat list list list list \<Rightarrow> nat list list \<Rightarrow>
   nat list list list \<Rightarrow> nat list list list \<Rightarrow> nat list list list" where
  "ur_nat_abi ur_header ur_prefix_tables ur_session_table ur_hash_table ur_calls =
    (case ur_header of
       [[ur_epoch,ur_revision,ur_who,ur_sid,ur_available,ur_permit_current,ur_permit_historical,ur_cache],
        ur_binding_words,ur_snapshot,ur_snapshot_canon,ur_snapshot_sha,ur_prefix,ur_prefix_sha,ur_context,ur_context_sha] \<Rightarrow>
       (case (ur_binding_from_words ur_binding_words,ur_collect ur_prefix_from_tables ur_prefix_tables,
          ur_collect ur_session_row ur_session_table,ur_collect ur_hash_row ur_hash_table) of
          (Some ur_b,Some ur_rows,Some ur_session_rows,Some ur_hash_rows) \<Rightarrow>
            let ur_snapshot_view = \<lparr>ur_snapshot_raw = ur_snapshot,ur_snapshot_reencoded = ur_snapshot_canon,
                ur_snapshot_digest = ur_snapshot_sha,ur_selected_raw = ur_prefix,ur_selected_digest = ur_prefix_sha,
                ur_context_raw = ur_context,ur_context_digest = ur_context_sha,
                ur_actual_cut = \<lparr>cut_authority_epoch = ur_epoch,cut_revision = ur_revision\<rparr>,
                ur_fixture_binding = ur_b,ur_sessions = ur_session_rows,ur_actor = ur_who,ur_session = ur_sid,
                ur_observed_available = (ur_available = 1),ur_current_permission = (ur_permit_current = 1),
                ur_historical_permission = (ur_permit_historical = 1),ur_has_cache = (ur_cache = 1),ur_prefixes = ur_rows\<rparr>;
                ur_hash = map_of ur_hash_rows
            in if list_all (\<lambda>ur_bit. ur_bit \<le> 1) [ur_available,ur_permit_current,ur_permit_historical,ur_cache]
                  \<and> ur_capture_bound ur_hash ur_snapshot_view
               then map (ur_case ur_hash ur_snapshot_view) ur_calls else [[[0]]]
        | _ \<Rightarrow> [[[0]]])
      | _ \<Rightarrow> [[[0]]])"

definition ur_external_word :: "integer \<Rightarrow> bool" where
  "ur_external_word ur_input \<longleftrightarrow> 0 \<le> ur_input \<and> ur_input < 18446744073709551616"

definition ur_integer_abi ::
  "integer list list \<Rightarrow> integer list list list list \<Rightarrow> integer list list \<Rightarrow>
   integer list list list \<Rightarrow> integer list list list \<Rightarrow> integer list list list" where
  "ur_integer_abi ur_header ur_prefix_tables ur_session_table ur_hash_table ur_calls =
    (if list_all (list_all ur_external_word) ur_header \<and>
        list_all (list_all (list_all (list_all ur_external_word))) ur_prefix_tables \<and>
        list_all (list_all ur_external_word) ur_session_table \<and>
        list_all (list_all (list_all ur_external_word)) ur_hash_table \<and>
        list_all (list_all (list_all ur_external_word)) ur_calls
     then map (map (map integer_of_nat))
       (ur_nat_abi (map (map nat_of_integer) ur_header)
         (map (map (map (map nat_of_integer))) ur_prefix_tables)
         (map (map nat_of_integer) ur_session_table) (map (map (map nat_of_integer)) ur_hash_table)
         (map (map (map nat_of_integer)) ur_calls))
     else [[[0]]])"

export_code ur_integer_abi in SML
  module_name OIP_Unpublished_Typed_Read_ABI file_prefix "oip_unpublished_typed_read_abi"

end
