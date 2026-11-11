theory Unpublished_Read_Link
  imports "OIP_Historical_Read_G0.Historical_Read_G0"
    "OIP_Message_Code.Wire_Code_JSON_Primitives"
    "OIP_Message_Code.Wire_Code_Fixed_Call_Request"
    "HOL-Library.Code_Target_Nat"
begin

text \<open>The Rust typed account has endpoint, owner and asset. The source
  balance below uses all three coordinates. Snapshot JSON decoding and the
  availability and permission facts are supplied at the observed boundary.\<close>

type_synonym ur_account = "nat \<times> nat \<times> nat"

datatype ur_query =
    UR_Application nat
  | UR_Source ur_account
  | UR_Destination ur_account
  | UR_Regulatory nat nat

fun ur_account_asset :: "ur_account \<Rightarrow> nat" where
  "ur_account_asset (ur_ep,ur_owner,ur_asset) = ur_asset"

fun ur_touches :: "ur_query \<Rightarrow> code_source_binding \<Rightarrow> bool" where
  "ur_touches (UR_Application ur_asset) ur_binding = (source_binding_asset ur_binding = ur_asset)"
| "ur_touches (UR_Source ur_account) ur_binding =
     (ur_account = (fst (source_binding_origin ur_binding),source_binding_owner ur_binding,source_binding_asset ur_binding))"
| "ur_touches (UR_Destination (ur_ep,ur_owner,ur_asset)) ur_binding =
     (source_binding_destination ur_binding = ur_ep \<and> source_binding_asset ur_binding = ur_asset)"
| "ur_touches (UR_Regulatory ur_ep ur_asset) ur_binding = (source_binding_asset ur_binding = ur_asset)"

lemma ur_source_balance_compares_the_exact_account_owner:
  "ur_touches (UR_Source (fst (source_binding_origin ur_binding),ur_holder,source_binding_asset ur_binding)) ur_binding
    \<longleftrightarrow> ur_holder = source_binding_owner ur_binding"
  by simp

lemma ur_destination_and_regulatory_touch_coordinates:
  "ur_touches (UR_Destination (ur_ep,ur_holder,ur_asset)) ur_binding
     \<longleftrightarrow> source_binding_destination ur_binding = ur_ep \<and> source_binding_asset ur_binding = ur_asset"
  "ur_touches (UR_Regulatory ur_ep ur_asset) ur_binding \<longleftrightarrow> source_binding_asset ur_binding = ur_asset"
  by simp_all

definition ur_uint_after where
  "ur_uint_after ur_token ur_bytes = Option.bind (code_json_expect ur_token ur_bytes) code_json_u64"

definition ur_parse_account :: "wire_bytes \<Rightarrow> (ur_account \<times> wire_bytes) option" where
  "ur_parse_account ur_bytes =
    Option.bind (ur_uint_after (code_json_open_key ''endpoint'') ur_bytes) (\<lambda>(ur_ep,ur_r0).
      Option.bind (ur_uint_after (code_json_next_key ''owner'') ur_r0) (\<lambda>(ur_owner,ur_r1).
        Option.bind (ur_uint_after (code_json_next_key ''asset'') ur_r1) (\<lambda>(ur_asset,ur_r2).
          map_option (\<lambda>ur_rest. ((ur_ep,ur_owner,ur_asset),ur_rest)) (code_json_expect [125] ur_r2))))"

definition ur_json_query where
  "ur_json_query ur_name ur_parse ur_constructor ur_bytes =
    Option.bind (code_json_expect (code_json_open_key ur_name) ur_bytes) (\<lambda>ur_rest.
      Option.bind (ur_parse ur_rest) (\<lambda>(ur_argument,ur_end).
        map_option (\<lambda>ur_trailing. (ur_constructor ur_argument,ur_trailing)) (code_json_expect [125] ur_end)))"

fun ur_first_parse :: "(wire_bytes \<Rightarrow> ur_query option) list \<Rightarrow> wire_bytes \<Rightarrow> ur_query option" where
  "ur_first_parse [] ur_bytes = None"
| "ur_first_parse (ur_parse # ur_more) ur_bytes =
     (case ur_parse ur_bytes of None \<Rightarrow> ur_first_parse ur_more ur_bytes | Some ur_query \<Rightarrow> Some ur_query)"

definition ur_decode_query :: "wire_bytes \<Rightarrow> ur_query option" where
  "ur_decode_query ur_bytes = ur_first_parse
    [code_json_complete (ur_json_query ''ApplicationValue'' code_json_u64 UR_Application),
     code_json_complete (ur_json_query ''SourceBalance'' ur_parse_account UR_Source),
     code_json_complete (ur_json_query ''DestinationBalance'' ur_parse_account UR_Destination),
     code_json_complete (ur_json_query ''RegulatoryState'' (code_json_pair code_json_u64 code_json_u64)
       (\<lambda>(ur_domain,ur_asset). UR_Regulatory ur_domain ur_asset))]
    ur_bytes"

lemma ur_decoded_source_balance_keeps_its_typed_owner:
  "ur_decode_query (code_json_open_key ''SourceBalance'' @ code_json_open_key ''endpoint'' @ [48] @
     code_json_next_key ''owner'' @ [56] @ code_json_next_key ''asset'' @ [49,55,125,125]) =
     Some (UR_Source (0,8,17))"
  by code_simp

record ur_projection =
  ur_asset_values :: "(nat \<times> nat) list"
  ur_balances :: "(ur_account \<times> nat) list"
  ur_root_funding :: "((source_key \<times> ur_account) \<times> nat) list"
  ur_locked_assets :: "nat list"
  ur_ordinary_rows :: "(code_source_binding \<times> bool) list"
  ur_legal_rows :: "(code_source_binding \<times> bool) list"
  ur_modes :: "((nat \<times> nat) \<times> reg_state) list"

definition ur_unpublished_touch where
  "ur_unpublished_touch ur_query ur_view \<longleftrightarrow>
    (let ur_matches = (\<lambda>(ur_binding,ur_published). \<not> ur_published \<and> ur_touches ur_query ur_binding)
     in list_ex ur_matches (ur_ordinary_rows ur_view) \<or> list_ex ur_matches (ur_legal_rows ur_view))"

definition ur_funded where
  "ur_funded ur_account ur_view =
    sum_list (map snd (filter (\<lambda>((ur_root,ur_owner),ur_amount). ur_owner = ur_account) (ur_root_funding ur_view)))"

definition ur_account_value where
  "ur_account_value ur_destination ur_account ur_view =
    (if map_of (ur_asset_values ur_view) (ur_account_asset ur_account) = None then Historical_Missing
     else let ur_allocated = ur_funded ur_account ur_view;
              ur_total = (case map_of (ur_balances ur_view) ur_account of None \<Rightarrow> 0 | Some ur_value \<Rightarrow> ur_value)
          in if ur_allocated \<ge> 2^64 then Historical_Missing
             else if ur_destination then Historical_Visible (Units_Value ur_allocated)
             else if ur_allocated > ur_total then Historical_Missing
             else Historical_Visible (Units_Value (ur_total - ur_allocated)))"

definition ur_app_projection where
  "ur_app_projection ur_asset ur_view =
    (let ur_units = map_of (ur_asset_values ur_view) ur_asset in
      \<lparr>historical_units = (case ur_units of None \<Rightarrow> 0 | Some ur_value \<Rightarrow> ur_value),
       historical_locked = List.member (ur_locked_assets ur_view) ur_asset,
       historical_unpublished_touch = ur_unpublished_touch (UR_Application ur_asset) ur_view,
       historical_registered = (ur_units \<noteq> None)\<rparr>)"

fun ur_value :: "ur_query \<Rightarrow> ur_projection \<Rightarrow> historical_snapshot_reply" where
  "ur_value (UR_Application ur_asset) ur_view = historical_project_value (ur_app_projection ur_asset ur_view)"
| "ur_value (UR_Source ur_account) ur_view =
    (if ur_unpublished_touch (UR_Source ur_account) ur_view then Historical_Hidden else ur_account_value False ur_account ur_view)"
| "ur_value (UR_Destination ur_account) ur_view =
    (if ur_unpublished_touch (UR_Destination ur_account) ur_view then Historical_Hidden else ur_account_value True ur_account ur_view)"
| "ur_value (UR_Regulatory ur_ep ur_asset) ur_view =
    (if ur_unpublished_touch (UR_Regulatory ur_ep ur_asset) ur_view then Historical_Hidden
     else Historical_Visible (Regulatory_Value (map_of (ur_modes ur_view) (ur_ep,ur_asset))))"

lemma ur_a_touching_unpublished_entry_blocks_every_supported_read:
  assumes "ur_unpublished_touch ur_query ur_view"
  shows "ur_value ur_query ur_view = Historical_Hidden"
  using assms by (cases ur_query) (simp_all add: ur_app_projection_def historical_project_value_def Let_def)

definition ur_native_current where
  "ur_native_current ur_access ur_available ur_query ur_expected ur_epoch ur_revision ur_views =
    (if \<not> ur_access then Product_Read_Rejected
     else if \<not> ur_available then Product_Read_Unavailable
     else historical_current_reply
       (native_current_read_value True (ur_value ur_query) ur_expected ur_epoch ur_revision ur_views))"

definition ur_native_historical where
  "ur_native_historical ur_access ur_available ur_query ur_index ur_views =
    (if \<not> ur_access then Product_Read_Rejected
     else if \<not> ur_available then Product_Read_Unavailable
     else historical_labelled_reply (native_history_read_value True (ur_value ur_query) ur_index ur_views))"

lemma ur_selected_native_cut_and_index_reuse_the_reference_reads:
  assumes related: "native_read_history_related ur_epoch ur_revision ur_views ur_history"
  shows "ur_native_current True True ur_query ur_expected ur_epoch ur_revision ur_views =
      historical_current_reply (current_reference_observation True (ur_value ur_query) ur_expected ur_history)"
    "ur_native_historical True True ur_query ur_index ur_views =
      historical_labelled_reply (historical_reference_observation True (ur_value ur_query) ur_index ur_history)"
proof -
  have ur_current_same:
    "native_current_read_value True (ur_value ur_query) ur_expected ur_epoch ur_revision ur_views =
      current_reference_observation True (ur_value ur_query) ur_expected ur_history"
    by (rule the_native_cut_and_its_selected_prefixes_give_the_same_model_values(1)[OF related])
  have ur_history_same:
    "native_history_read_value True (ur_value ur_query) ur_index ur_views =
      historical_reference_observation True (ur_value ur_query) ur_index ur_history"
    by (rule the_native_cut_and_its_selected_prefixes_give_the_same_model_values(2)[OF related])
  show "ur_native_current True True ur_query ur_expected ur_epoch ur_revision ur_views =
      historical_current_reply (current_reference_observation True (ur_value ur_query) ur_expected ur_history)"
    by (simp add: ur_native_current_def ur_current_same)
  show "ur_native_historical True True ur_query ur_index ur_views =
      historical_labelled_reply (historical_reference_observation True (ur_value ur_query) ur_index ur_history)"
    by (simp add: ur_native_historical_def ur_history_same)
qed

record ur_prefix_input =
  ur_prefix_raw :: wire_bytes
  ur_prefix_digest :: wire_bytes
  ur_prefix_view :: ur_projection

record ur_capture =
  ur_snapshot_raw :: wire_bytes
  ur_snapshot_reencoded :: wire_bytes
  ur_snapshot_digest :: wire_bytes
  ur_selected_raw :: wire_bytes
  ur_selected_digest :: wire_bytes
  ur_context_raw :: wire_bytes
  ur_context_digest :: wire_bytes
  ur_actual_cut :: product_cut
  ur_fixture_binding :: code_source_binding
  ur_sessions :: "(nat \<times> (nat \<times> nat)) list"
  ur_actor :: nat
  ur_session :: nat
  ur_observed_available :: bool
  ur_current_permission :: bool
  ur_historical_permission :: bool
  ur_has_cache :: bool
  ur_prefixes :: "ur_prefix_input list"

definition ur_capture_bound where
  "ur_capture_bound ur_hash ur_capture \<longleftrightarrow>
    (let ur_rows = ur_prefixes ur_capture;
         ur_revision = cut_revision (ur_actual_cut ur_capture)
     in ur_snapshot_raw ur_capture = ur_snapshot_reencoded ur_capture \<and>
        ur_hash (ur_snapshot_raw ur_capture) = Some (ur_snapshot_digest ur_capture) \<and>
        ur_hash (ur_context_raw ur_capture) = Some (ur_context_digest ur_capture) \<and>
        ur_hash (ur_selected_raw ur_capture) = Some (ur_selected_digest ur_capture) \<and>
        length ur_rows = Suc ur_revision \<and>
        list_all (\<lambda>ur_row. ur_hash (ur_prefix_raw ur_row) = Some (ur_prefix_digest ur_row)) ur_rows \<and>
        ur_prefix_raw (ur_rows ! ur_revision) = ur_selected_raw ur_capture \<and>
        \<not> ur_has_cache ur_capture)"

lemma ur_capture_binds_the_exact_selected_prefix_and_snapshot:
  assumes "ur_capture_bound ur_hash ur_capture"
  shows "ur_hash (ur_snapshot_raw ur_capture) = Some (ur_snapshot_digest ur_capture)"
    "ur_hash (ur_selected_raw ur_capture) = Some (ur_selected_digest ur_capture)"
    "ur_prefix_raw (ur_prefixes ur_capture ! cut_revision (ur_actual_cut ur_capture)) = ur_selected_raw ur_capture"
  using assms unfolding ur_capture_bound_def Let_def by blast+

definition ur_session_bound where
  "ur_session_bound ur_capture \<longleftrightarrow>
    map_of (ur_sessions ur_capture) (ur_session ur_capture) =
      Some (ur_actor ur_capture,cut_authority_epoch (ur_actual_cut ur_capture))"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ur_source_balance_compares_the_exact_account_owner
      ur_destination_and_regulatory_touch_coordinates ur_decoded_source_balance_keeps_its_typed_owner
      ur_a_touching_unpublished_entry_blocks_every_supported_read ur_selected_native_cut_and_index_reuse_the_reference_reads
      ur_capture_binds_the_exact_selected_prefix_and_snapshot})
  then () else error "Unexpected oracle in unpublished typed read link"
\<close>

end
