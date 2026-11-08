theory Reference_Cache_Consumption
  imports Reference_Product_Image
begin

definition reference_cache_revalidates where
  "reference_cache_revalidates provider query live_cut value candidate \<longleftrightarrow>
    cached_provider candidate = provider \<and> cached_query candidate = query \<and>
    cached_cut candidate = live_cut \<and> cached_value candidate = value"

definition current_reference_read_with_cache where
  "current_reference_read_with_cache directory policy authenticate verify_read token proof target query expected connection frame supplied =
    (let exact = current_read_from_reference_image directory policy authenticate verify_read token proof target query expected connection frame;
         provider = retained_provider (reference_product (image_authority frame))
     in case (exact, supplied) of
          (Authorized_Data (Current_Cut_Value live_cut value), Some candidate) \<Rightarrow>
            if reference_cache_revalidates provider query live_cut value candidate
            then Authorized_Data (Current_Cut_Value (cached_cut candidate) (cached_value candidate))
            else exact
        | _ \<Rightarrow> exact)"

theorem a_reference_cache_can_only_return_the_actual_current_reply:
  "current_reference_read_with_cache directory policy authenticate verify_read token proof target query expected connection frame supplied =
   current_read_from_reference_image directory policy authenticate verify_read token proof target query expected connection frame"
  by (simp add: current_reference_read_with_cache_def reference_cache_revalidates_def Let_def
    split: identity_read_reply.splits product_read_reply.splits option.splits if_splits)

lemma a_cache_cannot_supply_data_when_the_current_identity_is_refused:
  assumes "\<not> identity_read_allowed directory policy authenticate verify_read token proof target
    (Current_Data query expected) (identity_source (reference_read_source connection (image_authority frame)))"
  shows "current_reference_read_with_cache directory policy authenticate verify_read token proof target query expected connection frame supplied =
    Identity_Read_Rejected"
  using assms by (simp add: a_reference_cache_can_only_return_the_actual_current_reply
    current_read_from_reference_image_def reference_current_read_def Let_def)

lemma the_wrong_provider_cut_or_value_is_never_accepted_as_a_cache:
  assumes "cached_provider candidate \<noteq> provider \<or> cached_cut candidate \<noteq> live_cut \<or> cached_value candidate \<noteq> value"
  shows "\<not> reference_cache_revalidates provider query live_cut value candidate"
  using assms by (auto simp: reference_cache_revalidates_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms a_reference_cache_can_only_return_the_actual_current_reply
      a_cache_cannot_supply_data_when_the_current_identity_is_refused
      the_wrong_provider_cut_or_value_is_never_accepted_as_a_cache})
  then () else error "Unexpected oracle in reference cache consumption"
\<close>

end
