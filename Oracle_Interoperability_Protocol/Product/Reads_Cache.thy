theory Reads_Cache
  imports Read_Cuts
begin

datatype product_read_kind = Read_Current | Read_Historical

datatype product_read_reply =
    Current_Cut_Value product_cut application_value
  | Historical_Prefix_Value nat application_value
  | Product_Read_Busy
  | Product_Read_Unavailable
  | Product_Read_Rejected

record product_cache_entry =
  cached_query :: application_query
  cached_provider :: nat
  cached_cut :: product_cut
  cached_value :: application_value

record product_read_world =
  read_authority :: settlement_world
  read_provider :: nat
  query_cache :: "application_query \<Rightarrow> product_cache_entry option"

definition initial_product_reads where
  "initial_product_reads provider s = \<lparr>read_authority = s, read_provider = provider, query_cache = (\<lambda>_. None)\<rparr>"

definition read_access_bound where
  "read_access_bound permitted kind who session query s \<longleftrightarrow>
    permitted who kind query \<and>
    product_sessions (product_durable (observed_product_source (read_authority s))) session =
      Some \<lparr>session_principal = who, session_epoch = cut_authority_epoch (observed_product_cut (read_authority s))\<rparr>"

definition read_authority_available where
  "read_authority_available s \<longleftrightarrow>
    call_local_status (exact_calls (read_authority s)) = Endpoint_Up \<and>
    call_connection (exact_calls (read_authority s)) = Authority_Connected"

lemma query_cache_update_keeps_read_access [simp]:
  "read_access_bound permitted kind who session query (s\<lparr>query_cache := cache\<rparr>) =
    read_access_bound permitted kind who session query s"
  by (simp add: read_access_bound_def)

lemma query_cache_update_keeps_read_availability [simp]:
  "read_authority_available (s\<lparr>query_cache := cache\<rparr>) = read_authority_available s"
  by (simp add: read_authority_available_def)

fun registration_sensitive_asset :: "application_query \<Rightarrow> product_asset option" where
  "registration_sensitive_asset (Application_Value asset) = Some asset"
| "registration_sensitive_asset (Source_Balance (endpoint_key, asset)) = Some asset"
| "registration_sensitive_asset (Destination_Balance (endpoint_key, asset, holder)) = Some asset"
| "registration_sensitive_asset query = None"

definition read_asset_registered where
  "read_asset_registered query s \<longleftrightarrow>
    (case registration_sensitive_asset query of None \<Rightarrow> True
     | Some asset \<Rightarrow> product_owners (product_durable (observed_product_source (read_authority s))) asset \<noteq> None)"

lemma query_cache_update_keeps_asset_registration [simp]:
  "read_asset_registered query (s\<lparr>query_cache := cache\<rparr>) = read_asset_registered query s"
  by (cases "registration_sensitive_asset query") (simp_all add: read_asset_registered_def)

definition cache_is_current_for where
  "cache_is_current_for entry query s \<longleftrightarrow>
    cached_query entry = query \<and> cached_provider entry = read_provider s \<and>
    cached_cut entry = observed_product_cut (read_authority s)"

definition read_current_product where
  "read_current_product permitted who session query expected s =
    (let cut = observed_product_cut (read_authority s);
         snapshot = capture_snapshot (authoritative_read_core (read_authority s)) in
      if \<not> read_access_bound permitted Read_Current who session query s then Product_Read_Rejected
      else if \<not> read_authority_available s then Product_Read_Unavailable
      else if expected \<noteq> cut \<or> \<not> snapshot_query_ready query snapshot then Product_Read_Busy
      else if \<not> read_asset_registered query s then Product_Read_Unavailable
      else case query_cache s query of None \<Rightarrow> Current_Cut_Value cut (stored_query query snapshot)
      | Some entry \<Rightarrow> if cache_is_current_for entry query s
        then Current_Cut_Value cut (cached_value entry) else Product_Read_Busy)"

context source_attestation
begin

definition capture_product_cache where
  "capture_product_cache permitted who session query s =
    (let cut = observed_product_cut (read_authority s) in
      if read_access_bound permitted Read_Current who session query s \<and> read_authority_available s then
        case authority_prefix_snapshot (cut_revision cut) (read_authority s) of None \<Rightarrow> s
        | Some snapshot \<Rightarrow> if snapshot_query_ready query snapshot \<and> read_asset_registered query s then
          s\<lparr>query_cache := (query_cache s)(query := Some \<lparr>cached_query = query, cached_provider = read_provider s,
            cached_cut = cut, cached_value = stored_query query snapshot\<rparr>)\<rparr> else s
      else s)"

definition cache_has_source_value where
  "cache_has_source_value s entry \<longleftrightarrow>
    (\<exists>snapshot. authority_prefix_snapshot (cut_revision (cached_cut entry)) (read_authority s) = Some snapshot \<and>
      cached_value entry = stored_query (cached_query entry) snapshot)"

definition read_historical_product where
  "read_historical_product permitted who session query revision s =
    (if \<not> read_access_bound permitted Read_Historical who session query s then Product_Read_Rejected
     else if \<not> read_authority_available s then Product_Read_Unavailable
     else case authority_prefix_snapshot revision (read_authority s) of None \<Rightarrow> Product_Read_Unavailable
      | Some snapshot \<Rightarrow> if \<not> snapshot_query_ready query snapshot then Product_Read_Busy
        else if read_asset_registered query s then Historical_Prefix_Value revision (stored_query query snapshot)
        else Product_Read_Unavailable)"

lemma unregistered_read_cannot_expose_a_value_or_create_a_cache_entry:
  assumes "\<not> read_asset_registered query s"
  shows "read_current_product permitted who session query expected s \<noteq> Current_Cut_Value observed result"
    "read_historical_product permitted who session query requested s \<noteq> Historical_Prefix_Value revision result"
    "capture_product_cache permitted who session query s = s"
  using assms by (auto simp: read_current_product_def read_historical_product_def capture_product_cache_def Let_def
      split: option.splits if_splits)

lemma a_current_source_bound_cache_has_the_actual_value:
  assumes current: "cache_is_current_for entry query s" and source: "cache_has_source_value s entry"
    and replay: "finality_calls.authority_replay_contract (exact_calls (read_authority s))"
  shows "cached_value entry = stored_query query (capture_snapshot (authoritative_read_core (read_authority s)))"
proof -
  have prefix: "authority_prefix_snapshot (cut_revision (observed_product_cut (read_authority s))) (read_authority s) =
    Some (capture_snapshot (authoritative_read_core (read_authority s)))"
    using full_authority_prefix_equals_the_current_core[OF replay]
    by (simp add: authority_prefix_snapshot_def)
  show ?thesis using current source prefix
    by (simp add: cache_has_source_value_def cache_is_current_for_def)
qed

theorem successful_current_product_read_comes_from_the_actual_cut:
  assumes reply: "read_current_product permitted who session query expected s = Current_Cut_Value reply_cut value"
    and replay: "finality_calls.authority_replay_contract (exact_calls (read_authority s))"
    and authentic: "\<And>entry. query_cache s query = Some entry \<Longrightarrow> cache_has_source_value s entry"
  shows "reply_cut = expected \<and> reply_cut = observed_product_cut (read_authority s) \<and>
    value = stored_query query (capture_snapshot (authoritative_read_core (read_authority s)))"
proof (cases "query_cache s query")
  case None
  with reply show ?thesis by (auto simp: read_current_product_def Let_def split: if_splits)
next
  case (Some entry)
  have ready: "cache_is_current_for entry query s \<and> reply_cut = expected \<and> reply_cut = observed_product_cut (read_authority s) \<and>
      value = cached_value entry"
    using reply Some by (auto simp: read_current_product_def Let_def split: if_splits)
  have source: "cache_has_source_value s entry" by (rule authentic[OF Some])
  have current: "cache_is_current_for entry query s" by (rule conjunct1[OF ready])
  have actual: "cached_value entry = stored_query query (capture_snapshot (authoritative_read_core (read_authority s)))"
    by (rule a_current_source_bound_cache_has_the_actual_value[OF current source replay])
  have cached_eq: "value = cached_value entry"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF ready]]])
  have actual_eq: "value = stored_query query (capture_snapshot (authoritative_read_core (read_authority s)))"
    by (rule trans[OF cached_eq actual])
  show ?thesis using ready actual_eq by blast
qed

theorem successful_historical_product_read_is_the_named_prefix:
  assumes "read_historical_product permitted who session query requested s = Historical_Prefix_Value revision value"
  shows "revision = requested \<and> (\<exists>snapshot. authority_prefix_snapshot requested (read_authority s) = Some snapshot \<and>
    value = stored_query query snapshot)"
  using assms by (auto simp: read_historical_product_def split: option.splits if_splits)

lemma stale_current_request_is_closed:
  assumes "read_access_bound permitted Read_Current who session query s" "read_authority_available s"
    "expected \<noteq> observed_product_cut (read_authority s)"
  shows "read_current_product permitted who session query expected s = Product_Read_Busy"
  using assms by (simp add: read_current_product_def Let_def)

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms query_cache_update_keeps_asset_registration
    source_attestation.unregistered_read_cannot_expose_a_value_or_create_a_cache_entry
    source_attestation.successful_current_product_read_comes_from_the_actual_cut
    source_attestation.successful_historical_product_read_is_the_named_prefix})
  then () else error "Unexpected oracle in registered read boundary"
\<close>

end
