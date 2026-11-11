theory Query6_Capture_Export
  imports "OIP_Query6_Capture_G0.Query6_Capture_G0" "HOL-Library.Code_Target_Nat"
begin

definition query6_export_core :: "unit \<Rightarrow> integer list" where
  "query6_export_core ignored_unit = map integer_of_nat (encode_wire_core query6_g0_core)"

fun query6_export_cache_error_tag :: "product_read_reply \<Rightarrow> nat" where
  "query6_export_cache_error_tag Product_Read_Busy = 1"
| "query6_export_cache_error_tag Product_Read_Unavailable = 2"
| "query6_export_cache_error_tag Product_Read_Rejected = 3"
| "query6_export_cache_error_tag _ = 4"

fun query6_export_reply :: "query6_capture_reply \<Rightarrow> nat list" where
  "query6_export_reply Q6_Endpoint_Rejected = [0,1,0,0,0,0,0,0]"
| "query6_export_reply Q6_Endpoint_Unavailable = [0,2,0,0,0,0,0,0]"
| "query6_export_reply (Q6_Cache_Error upstream) =
    [1,query6_export_cache_error_tag upstream,0,0,0,0,0,0]"
| "query6_export_reply (Q6_Cache_Value entry) =
    (case (cached_query entry, cached_value entry) of
       (Application_Value captured_asset, Units_Value captured_units) \<Rightarrow>
       [1,0,1,cached_provider entry,captured_asset,cut_authority_epoch (cached_cut entry),
        cut_revision (cached_cut entry),captured_units]
     | _ \<Rightarrow> [3,0,0,0,0,0,0,0])"
| "query6_export_reply Q6_Not_Capture = [2,0,0,0,0,0,0,0]"

definition query6_export_selector_fields where
  "query6_export_selector_fields =
    (case code_source_nonreceipt_read_service (7::nat) query6_g0_core of
       Some (Service_Capture selected_token selected_proof selected_target (Application_Value selected_asset)) \<Rightarrow>
         [wire_principal query6_g0_core,proof_session selected_proof,proof_epoch selected_proof,
          selected_target,selected_asset]
     | _ \<Rightarrow> [])"

definition query6_export_upstream :: "nat \<Rightarrow> product_cut \<Rightarrow> nat \<Rightarrow> product_read_reply" where
  "query6_export_upstream upstream_tag selected_cut selected_units =
    (if upstream_tag = 0 then Current_Cut_Value selected_cut (Units_Value selected_units)
     else if upstream_tag = 1 then Product_Read_Busy
     else if upstream_tag = 2 then Product_Read_Unavailable else Product_Read_Rejected)"

fun query6_export_observe_nat :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list option" where
  "query6_export_observe_nat
    [row_id,authenticated_present,active_present,verified_present,target_present,available_input,
     current_epoch_input,upstream_tag,provider_input,selected_epoch,selected_revision,selected_units]
    cache_assets current_assets =
    (if \<not> list_all (\<lambda>n. n \<le> 1)
       [authenticated_present,active_present,verified_present,target_present,available_input] \<or> upstream_tag > 3
     then None else
     let facts = (query6_g0_facts cache_assets current_assets)\<lparr>
       q6_authenticated_subject := (if authenticated_present = 1 then Some (7,7) else None),
       q6_active_proof := (if active_present = 1 then Some \<lparr>proof_session = 2, proof_epoch = 9\<rparr> else None),
       q6_verified_capture := (if verified_present = 1 then Some query6_g0_scope else None),
       q6_registered_targets := (if target_present = 1 then [2] else []),
       q6_current_epoch := current_epoch_input, q6_authority_available := (available_input = 1)\<rparr>;
       selected_cut = \<lparr>cut_authority_epoch = selected_epoch,cut_revision = selected_revision\<rparr>;
       upstream = query6_export_upstream upstream_tag selected_cut selected_units;
       original = query6_capture_from_core False 7 query6_g0_core facts provider_input upstream (0::nat);
       altered = query6_capture_from_core True 7 query6_g0_core facts provider_input upstream (0::nat)
     in Some ([row_id] @ query6_export_selector_fields @
       [provider_input,selected_epoch,selected_revision,selected_units,upstream_tag,
        (if query6_capture_permission False query6_g0_scope facts then 1 else 0),
        (if query6_current_permission query6_g0_scope facts then 1 else 0)] @
       query6_export_reply (snd original) @ query6_export_reply (snd altered) @
       [if fst original = 0 \<and> fst altered = 0 then 1 else 0]))"
| "query6_export_observe_nat _ cache_assets current_assets = None"

definition query6_export_observe :: "integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list option" where
  "query6_export_observe metadata cache_assets current_assets =
    (if list_all (\<lambda>n. 0 \<le> n) (metadata @ cache_assets @ current_assets)
     then map_option (map integer_of_nat) (query6_export_observe_nat
       (map nat_of_integer metadata) (map nat_of_integer cache_assets) (map nat_of_integer current_assets))
     else None)"

lemma query6_export_selector_keeps_the_actual_capture_scope:
  "query6_export_selector_fields = [7,2,9,2,17]"
  unfolding query6_export_selector_fields_def
  apply (subst query6_g0_selected_service)
  by (simp add: query6_g0_core_def)

lemma query6_export_preserves_endpoint_vs_cache_failure:
  "query6_export_reply Q6_Endpoint_Rejected \<noteq> query6_export_reply (Q6_Cache_Error Product_Read_Rejected)"
  "query6_export_reply Q6_Endpoint_Unavailable \<noteq> query6_export_reply (Q6_Cache_Error Product_Read_Unavailable)"
  by simp_all

export_code query6_export_core query6_export_observe
  in SML module_name OIP_Query6_Capture file_prefix "oip_query6_capture"

thm_oracles query6_export_selector_keeps_the_actual_capture_scope
  query6_export_preserves_endpoint_vs_cache_failure

end
