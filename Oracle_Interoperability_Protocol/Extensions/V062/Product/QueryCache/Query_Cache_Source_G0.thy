theory Query_Cache_Source_G0
  imports "OIP_Reference_Profile.Reference_Cache_Consumption"
begin

text \<open>
  G-0 candidate only. The product's uncached read is an explicit input.
  A process-local source is its Arc allocation identity, represented by a nat.
  A reopened source is its exact RecoveryProfile, not its process allocation.
  This additional input is absent from product_cache_entry. No existing
  definition, acceptance rule, identity policy, or history is replaced here.
\<close>

type_synonym query_cache_runtime_source = "nat + recovery_profile"

definition query_cache_runtime_source ::
  "recovery_profile option \<Rightarrow> nat \<Rightarrow> query_cache_runtime_source" where
  "query_cache_runtime_source profile instance =
    (case profile of None \<Rightarrow> Inl instance | Some selected \<Rightarrow> Inr selected)"

definition query_cache_source_consume ::
  "query_cache_runtime_source \<Rightarrow> query_cache_runtime_source \<Rightarrow>
   nat \<Rightarrow> application_query \<Rightarrow> product_read_reply \<Rightarrow>
   product_cache_entry \<Rightarrow> product_read_reply" where
  "query_cache_source_consume live_source candidate_source provider query exact candidate =
    (case exact of Current_Cut_Value selected_cut actual \<Rightarrow>
      if candidate_source = live_source \<and>
         reference_cache_revalidates provider query selected_cut actual candidate
      then Current_Cut_Value selected_cut (cached_value candidate)
      else Product_Read_Busy
    | _ \<Rightarrow> exact)"

text \<open>
  The sole removal drops source identity equality. The provider, query, both
  cut fields, actual-value comparison and upstream uncached reply remain.
\<close>

definition query_cache_source_removed ::
  "query_cache_runtime_source \<Rightarrow> query_cache_runtime_source \<Rightarrow>
   nat \<Rightarrow> application_query \<Rightarrow> product_read_reply \<Rightarrow>
   product_cache_entry \<Rightarrow> product_read_reply" where
  "query_cache_source_removed live_source candidate_source provider query exact candidate =
    (case exact of Current_Cut_Value selected_cut actual \<Rightarrow>
      if reference_cache_revalidates provider query selected_cut actual candidate
      then Current_Cut_Value selected_cut (cached_value candidate)
      else Product_Read_Busy
    | _ \<Rightarrow> exact)"

lemma query_cache_runtime_source_matches_the_three_product_branches:
  "query_cache_runtime_source (Some p) x = query_cache_runtime_source (Some q) y \<longleftrightarrow> p = q"
  "query_cache_runtime_source None x = query_cache_runtime_source None y \<longleftrightarrow> x = y"
  "query_cache_runtime_source (Some p) x \<noteq> query_cache_runtime_source None y"
  "query_cache_runtime_source None x \<noteq> query_cache_runtime_source (Some p) y"
  by (simp_all add: query_cache_runtime_source_def)

lemma query_cache_existing_revalidation_is_reused:
  "reference_cache_revalidates (read_provider reads) query
      (observed_product_cut (read_authority reads))
      (stored_query query (capture_snapshot (authoritative_read_core (read_authority reads)))) candidate =
    valid_recovered_cache query candidate reads"
  by (auto simp: reference_cache_revalidates_def valid_recovered_cache_def cache_is_current_for_def)

lemma query_cache_source_success_preserves_every_binding:
  assumes "query_cache_source_consume live_source candidate_source provider query exact candidate =
    Current_Cut_Value selected_cut value"
  shows "candidate_source = live_source"
    "cached_provider candidate = provider"
    "cached_query candidate = query"
    "cached_cut candidate = selected_cut"
    "cached_value candidate = value"
    "exact = Current_Cut_Value selected_cut value"
  using assms
  by (cases exact; auto simp: query_cache_source_consume_def reference_cache_revalidates_def split: if_splits)+

context source_attestation
begin

lemma query_cache_same_source_agrees_with_existing_busy_consumer:
  assumes trusted: "read_at_identity_endpoint directory policy authenticate verify_read token proof target
      (Current_Data query expected) (discard_process_cache s) =
      Authorized_Data (Current_Cut_Value actual observed)"
    and cut: "actual = observed_product_cut (read_authority (regulated_read_world s))"
    and observed_value: "observed = stored_query query
      (capture_snapshot (authoritative_read_core (read_authority (regulated_read_world s))))"
  shows "Authorized_Data (query_cache_source_consume source source
      (read_provider (regulated_read_world s)) query (Current_Cut_Value actual observed) candidate) =
    read_with_revalidated_cache directory policy authenticate verify_read token proof target
      (Current_Data query expected) (Some candidate) s"
  using trusted cut observed_value
  by (auto simp: query_cache_source_consume_def read_with_revalidated_cache_def
      reference_cache_revalidates_def valid_recovered_cache_def cache_is_current_for_def Let_def)

end

definition query_cache_g0_cut :: product_cut where
  "query_cache_g0_cut = \<lparr>cut_authority_epoch = 9, cut_revision = 0\<rparr>"

definition query_cache_g0_profile :: recovery_profile where
  "query_cache_g0_profile =
    \<lparr>recovery_deployment = 7, recovery_format = 1, recovery_authority_profile = 99\<rparr>"

definition query_cache_g0_entry :: product_cache_entry where
  "query_cache_g0_entry = \<lparr>cached_query = Application_Value 17, cached_provider = 100,
    cached_cut = query_cache_g0_cut, cached_value = Units_Value 0\<rparr>"

lemma query_cache_g0_normal:
  "query_cache_source_consume (Inl 11) (Inl 11) 100 (Application_Value 17)
    (Current_Cut_Value query_cache_g0_cut (Units_Value 0)) query_cache_g0_entry =
    Current_Cut_Value query_cache_g0_cut (Units_Value 0)"
  by (simp add: query_cache_source_consume_def reference_cache_revalidates_def query_cache_g0_entry_def)

lemma query_cache_g0_wrong_source_same_every_other_field:
  "query_cache_source_consume (Inl 12) (Inl 11) 100 (Application_Value 17)
    (Current_Cut_Value query_cache_g0_cut (Units_Value 0)) query_cache_g0_entry = Product_Read_Busy"
  by (simp add: query_cache_source_consume_def)

lemma query_cache_g0_wrong_provider:
  "query_cache_source_consume (Inl 11) (Inl 11) 101 (Application_Value 17)
    (Current_Cut_Value query_cache_g0_cut (Units_Value 0)) query_cache_g0_entry = Product_Read_Busy"
  by (simp add: query_cache_source_consume_def reference_cache_revalidates_def query_cache_g0_entry_def)

lemma query_cache_g0_wrong_query_same_value:
  "query_cache_source_consume (Inl 11) (Inl 11) 100 (Application_Value 18)
    (Current_Cut_Value query_cache_g0_cut (Units_Value 0)) query_cache_g0_entry = Product_Read_Busy"
  by (simp add: query_cache_source_consume_def reference_cache_revalidates_def query_cache_g0_entry_def)

lemma query_cache_g0_changed_selected_cut_same_value:
  "query_cache_source_consume (Inl 11) (Inl 11) 100 (Application_Value 17)
    (Current_Cut_Value (query_cache_g0_cut\<lparr>cut_revision := 3\<rparr>) (Units_Value 0))
    query_cache_g0_entry = Product_Read_Busy"
  "query_cache_source_consume (Inl 11) (Inl 11) 100 (Application_Value 17)
    (Current_Cut_Value (query_cache_g0_cut\<lparr>cut_authority_epoch := 10\<rparr>) (Units_Value 0))
    query_cache_g0_entry = Product_Read_Busy"
  by (simp_all add: query_cache_source_consume_def reference_cache_revalidates_def
      query_cache_g0_entry_def query_cache_g0_cut_def)

lemma query_cache_g0_reopened_profile:
  "query_cache_source_consume
    (query_cache_runtime_source (Some query_cache_g0_profile) 12)
    (query_cache_runtime_source (Some query_cache_g0_profile) 11)
    100 (Application_Value 17) (Current_Cut_Value query_cache_g0_cut (Units_Value 0))
    query_cache_g0_entry = Current_Cut_Value query_cache_g0_cut (Units_Value 0)"
  "query_cache_source_consume
    (query_cache_runtime_source (Some (query_cache_g0_profile\<lparr>recovery_deployment := 8\<rparr>)) 12)
    (query_cache_runtime_source (Some query_cache_g0_profile) 11)
    100 (Application_Value 17) (Current_Cut_Value query_cache_g0_cut (Units_Value 0))
    query_cache_g0_entry = Product_Read_Busy"
  by (simp_all add: query_cache_source_consume_def query_cache_runtime_source_def
      reference_cache_revalidates_def query_cache_g0_entry_def query_cache_g0_profile_def)

lemma query_cache_g0_upstream_refusals_are_preserved:
  "query_cache_source_consume live cached provider query Product_Read_Busy entry = Product_Read_Busy"
  "query_cache_source_consume live cached provider query Product_Read_Unavailable entry = Product_Read_Unavailable"
  "query_cache_source_consume live cached provider query Product_Read_Rejected entry = Product_Read_Rejected"
  by (simp_all add: query_cache_source_consume_def)

lemma query_cache_g0_removing_only_source_equality_changes_the_result:
  "query_cache_source_consume (Inl 12) (Inl 11) 100 (Application_Value 17)
    (Current_Cut_Value query_cache_g0_cut (Units_Value 0)) query_cache_g0_entry = Product_Read_Busy"
  "query_cache_source_removed (Inl 12) (Inl 11) 100 (Application_Value 17)
    (Current_Cut_Value query_cache_g0_cut (Units_Value 0)) query_cache_g0_entry =
    Current_Cut_Value query_cache_g0_cut (Units_Value 0)"
  by (simp_all add: query_cache_source_consume_def query_cache_source_removed_def
      reference_cache_revalidates_def query_cache_g0_entry_def)

thm_oracles query_cache_source_success_preserves_every_binding
  source_attestation.query_cache_same_source_agrees_with_existing_busy_consumer
  query_cache_g0_normal query_cache_g0_wrong_source_same_every_other_field
  query_cache_g0_wrong_provider query_cache_g0_wrong_query_same_value
  query_cache_g0_changed_selected_cut_same_value query_cache_g0_reopened_profile
  query_cache_g0_removing_only_source_equality_changes_the_result

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms query_cache_source_success_preserves_every_binding
    source_attestation.query_cache_same_source_agrees_with_existing_busy_consumer
    query_cache_g0_normal query_cache_g0_wrong_source_same_every_other_field
    query_cache_g0_wrong_provider query_cache_g0_wrong_query_same_value
    query_cache_g0_changed_selected_cut_same_value query_cache_g0_reopened_profile
    query_cache_g0_removing_only_source_equality_changes_the_result})
  then () else error "Unexpected oracle in query cache source G0"
\<close>

end
