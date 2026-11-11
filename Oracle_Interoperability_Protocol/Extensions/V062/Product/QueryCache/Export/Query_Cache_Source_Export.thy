theory Query_Cache_Source_Export
  imports "OIP_Query_Cache_Source_G0.Query_Cache_Source_G0" "HOL-Library.Code_Target_Nat"
begin

text \<open>
  Standalone consumer export. The checked parent is unchanged.
  The external source-only driver verifies native-cache-inputs.json SHA-256
  3368f56c91aaccc495393b558d0296bb552c78f6a7d9fba066a439bf147f02f0.
  It supplies explicit typed inputs, never expected outcomes. Integer lists
  form the public SML ABI; no large product tuple or raw-byte code_simp is used.
  The uncached upstream reply remains an input, not a wire authorization claim.
\<close>

fun query_cache_export_source_fields :: "query_cache_runtime_source \<Rightarrow> nat list" where
  "query_cache_export_source_fields (Inl instance) = [0, instance, 0, 0, 0]"
| "query_cache_export_source_fields (Inr profile) =
    [1, 0, recovery_deployment profile, recovery_format profile, recovery_authority_profile profile]"

fun query_cache_export_query_fields :: "application_query \<Rightarrow> nat list" where
  "query_cache_export_query_fields (Application_Value asset) = [1, asset]"
| "query_cache_export_query_fields _ = [0, 0]"

fun query_cache_export_value_fields :: "application_value \<Rightarrow> nat list" where
  "query_cache_export_value_fields (Units_Value units) = [1, units]"
| "query_cache_export_value_fields _ = [0, 0]"

fun query_cache_export_reply_fields :: "product_read_reply \<Rightarrow> nat list" where
  "query_cache_export_reply_fields (Current_Cut_Value selected_reply_cut (Units_Value units)) =
    [0, 1, cut_authority_epoch selected_reply_cut, cut_revision selected_reply_cut, 1, units]"
| "query_cache_export_reply_fields Product_Read_Busy = [1, 0, 0, 0, 0, 0]"
| "query_cache_export_reply_fields Product_Read_Unavailable = [2, 0, 0, 0, 0, 0]"
| "query_cache_export_reply_fields Product_Read_Rejected = [3, 0, 0, 0, 0, 0]"
| "query_cache_export_reply_fields _ = [4, 0, 0, 0, 0, 0]"

definition query_cache_export_replies where
  "query_cache_export_replies live_source candidate_source provider query exact candidate =
    query_cache_export_reply_fields
      (query_cache_source_consume live_source candidate_source provider query exact candidate) @
    query_cache_export_reply_fields
      (query_cache_source_removed live_source candidate_source provider query exact candidate)"

definition query_cache_export_view where
  "query_cache_export_view row_id candidate_allocation live_allocation live_source candidate_source
      provider query selected_cut exact candidate =
    [row_id, candidate_allocation, live_allocation] @
    query_cache_export_source_fields candidate_source @
    query_cache_export_source_fields live_source @
    [cached_provider candidate, provider] @
    query_cache_export_query_fields (cached_query candidate) @
    query_cache_export_query_fields query @
    [cut_authority_epoch (cached_cut candidate), cut_revision (cached_cut candidate)] @
    query_cache_export_value_fields (cached_value candidate) @
    [cut_authority_epoch selected_cut, cut_revision selected_cut] @
    query_cache_export_reply_fields exact @
    query_cache_export_replies live_source candidate_source provider query exact candidate"

definition query_cache_export_source ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> query_cache_runtime_source option" where
  "query_cache_export_source cache_source_tag_input cache_source_instance_input
      cache_source_deployment_input cache_source_format_input cache_source_authority_input =
    (if cache_source_tag_input = 0 then
       if cache_source_deployment_input = 0 \<and> cache_source_format_input = 0 \<and>
          cache_source_authority_input = 0 then Some (Inl cache_source_instance_input) else None
     else if cache_source_tag_input = 1 then Some (Inr \<lparr>recovery_deployment = cache_source_deployment_input,
       recovery_format = cache_source_format_input, recovery_authority_profile = cache_source_authority_input\<rparr>)
     else None)"

definition query_cache_export_upstream ::
  "nat \<Rightarrow> product_cut \<Rightarrow> application_value \<Rightarrow> product_read_reply option" where
  "query_cache_export_upstream tag selected_cut observed =
    (if tag = 0 then Some (Current_Cut_Value selected_cut observed)
     else if tag = 1 then Some Product_Read_Busy
     else if tag = 2 then Some Product_Read_Unavailable
     else if tag = 3 then Some Product_Read_Rejected
     else None)"

fun query_cache_export_observe_nat :: "nat list \<Rightarrow> nat list option" where
  "query_cache_export_observe_nat
    [row_id, cached_tag, cached_instance, cached_deployment, cached_format, cached_authority,
     live_tag, live_instance, live_deployment, live_format, live_authority,
     cached_provider_input, live_provider_input, cached_query_tag, cached_asset,
     requested_query_tag, requested_asset, cached_epoch, cached_revision, cached_value_tag,
     cached_units, selected_epoch, selected_revision, actual_value_tag, actual_units, upstream_tag] =
    (if cached_query_tag \<noteq> 1 \<or> requested_query_tag \<noteq> 1 \<or>
        cached_value_tag \<noteq> 1 \<or> actual_value_tag \<noteq> 1 then None
     else case (query_cache_export_source cached_tag cached_instance cached_deployment cached_format cached_authority,
                query_cache_export_source live_tag live_instance live_deployment live_format live_authority) of
       (Some candidate_source, Some live_source) \<Rightarrow>
         (let selected_cut = \<lparr>cut_authority_epoch = selected_epoch, cut_revision = selected_revision\<rparr>;
              candidate = \<lparr>cached_query = Application_Value cached_asset,
                cached_provider = cached_provider_input,
                cached_cut = \<lparr>cut_authority_epoch = cached_epoch, cut_revision = cached_revision\<rparr>,
                cached_value = Units_Value cached_units\<rparr>
          in case query_cache_export_upstream upstream_tag selected_cut (Units_Value actual_units) of
            None \<Rightarrow> None
          | Some exact \<Rightarrow> Some (query_cache_export_view row_id cached_instance live_instance
              live_source candidate_source live_provider_input (Application_Value requested_asset)
              selected_cut exact candidate))
     | _ \<Rightarrow> None)"
| "query_cache_export_observe_nat _ = None"

definition query_cache_export_observe :: "integer list \<Rightarrow> integer list option" where
  "query_cache_export_observe inputs =
    (if list_all (\<lambda>n. 0 \<le> n) inputs
     then map_option (map integer_of_nat) (query_cache_export_observe_nat (map nat_of_integer inputs))
     else None)"

lemma query_cache_export_normal_uses_the_checked_consumer:
  "query_cache_export_replies (Inl 11) (Inl 11) 100 (Application_Value 17)
      (Current_Cut_Value query_cache_g0_cut (Units_Value 0)) query_cache_g0_entry =
    [0,1,9,0,1,0,0,1,9,0,1,0]"
  unfolding query_cache_export_replies_def
  apply (subst query_cache_g0_normal)
  by (simp add: query_cache_source_removed_def reference_cache_revalidates_def
      query_cache_g0_entry_def query_cache_g0_cut_def)

lemma query_cache_export_one_removal_uses_the_checked_witness:
  "query_cache_export_replies (Inl 12) (Inl 11) 100 (Application_Value 17)
      (Current_Cut_Value query_cache_g0_cut (Units_Value 0)) query_cache_g0_entry =
    [1,0,0,0,0,0,0,1,9,0,1,0]"
  unfolding query_cache_export_replies_def
  apply (subst query_cache_g0_removing_only_source_equality_changes_the_result(1))
  apply (subst query_cache_g0_removing_only_source_equality_changes_the_result(2))
  by (simp add: query_cache_g0_cut_def)

lemma query_cache_export_upstream_refusals_remain_refusals:
  "query_cache_export_replies live cached provider query Product_Read_Busy candidate =
    [1,0,0,0,0,0,1,0,0,0,0,0]"
  "query_cache_export_replies live cached provider query Product_Read_Unavailable candidate =
    [2,0,0,0,0,0,2,0,0,0,0,0]"
  "query_cache_export_replies live cached provider query Product_Read_Rejected candidate =
    [3,0,0,0,0,0,3,0,0,0,0,0]"
  by (simp_all add: query_cache_export_replies_def query_cache_source_consume_def query_cache_source_removed_def)

export_code query_cache_export_observe
  in SML module_name OIP_Query_Cache_Source file_prefix "oip_query_cache_source"

thm_oracles query_cache_export_normal_uses_the_checked_consumer
  query_cache_export_one_removal_uses_the_checked_witness
  query_cache_export_upstream_refusals_remain_refusals

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms query_cache_export_normal_uses_the_checked_consumer
    query_cache_export_one_removal_uses_the_checked_witness
    query_cache_export_upstream_refusals_remain_refusals})
  then () else error "Unexpected oracle in query cache standalone export"
\<close>

end
