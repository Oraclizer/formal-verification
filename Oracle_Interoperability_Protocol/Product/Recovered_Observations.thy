theory Recovered_Observations
  imports Durable_Execution
begin

definition discard_process_cache where
  "discard_process_cache s =
    replace_regulated_reads ((regulated_read_world s)\<lparr>query_cache := (\<lambda>_. None)\<rparr>) s"

definition valid_recovered_cache where
  "valid_recovered_cache query entry reads \<longleftrightarrow>
    cache_is_current_for entry query reads \<and> cached_value entry =
      stored_query query (capture_snapshot (authoritative_read_core (read_authority reads)))"

context source_attestation
begin

definition read_with_revalidated_cache where
  "read_with_revalidated_cache directory policy authenticate verify_read token proof target request supplied s =
    (let trusted = read_at_identity_endpoint directory policy authenticate verify_read token proof target request (discard_process_cache s)
     in case (request, trusted, supplied) of
       (Current_Data query expected, Authorized_Data (Current_Cut_Value actual observed), Some candidate) \<Rightarrow>
         if valid_recovered_cache query candidate (regulated_read_world s) then trusted
         else Authorized_Data Product_Read_Busy
     | _ \<Rightarrow> trusted)"

definition capture_revalidated_cache where
  "capture_revalidated_cache directory policy authenticate verify_read token proof target query s =
    query_cache (regulated_read_world
      (capture_at_identity_endpoint directory policy authenticate verify_read token proof target query (discard_process_cache s))) query"

lemma wrong_cache_value_cannot_be_returned_as_current:
  assumes original: "read_at_identity_endpoint directory policy authenticate verify_read token proof target
    (Current_Data query expected) (discard_process_cache s) = Authorized_Data (Current_Cut_Value actual observed)"
    and forged: "cached_value candidate \<noteq>
       stored_query query (capture_snapshot (authoritative_read_core (read_authority (regulated_read_world s))))"
  shows "read_with_revalidated_cache directory policy authenticate verify_read token proof target
    (Current_Data query expected) (Some candidate) s = Authorized_Data Product_Read_Busy"
  using assms by (simp add: read_with_revalidated_cache_def valid_recovered_cache_def Let_def)

lemma a_valid_same_authority_cache_preserves_the_actual_current_response:
  assumes "read_at_identity_endpoint directory policy authenticate verify_read token proof target
    (Current_Data query expected) (discard_process_cache s) = Authorized_Data (Current_Cut_Value actual observed)"
    "valid_recovered_cache query candidate (regulated_read_world s)"
  shows "read_with_revalidated_cache directory policy authenticate verify_read token proof target
    (Current_Data query expected) (Some candidate) s = Authorized_Data (Current_Cut_Value actual observed)"
  using assms by (simp add: read_with_revalidated_cache_def Let_def)

end

end
