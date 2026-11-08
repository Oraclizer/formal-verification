theory Reference_Read_Consumption
  imports Reference_Read_Cuts Reference_Authority_Trace
begin

definition reference_read_source where
  "reference_read_source connection snapshot =
    reopen_retained_product connection (reference_product snapshot)"

definition reference_current_read where
  "reference_current_read directory policy authenticate verify_read token proof target query expected
      connection snapshot read history =
    (let live = reference_read_source connection snapshot in
      if \<not> identity_read_allowed directory policy authenticate verify_read token proof target
          (Current_Data query expected) (identity_source live)
      then Identity_Read_Rejected
      else if \<not> read_authority_available (regulated_read_world live) \<or> reference_history_prefixes history = []
      then Identity_Read_Unavailable
      else case current_reference_observation True (\<lambda>row. read row query) expected history of
        None \<Rightarrow> Authorized_Data Product_Read_Busy
      | Some (actual,value) \<Rightarrow> Authorized_Data (Current_Cut_Value actual value))"

definition reference_historical_read where
  "reference_historical_read directory policy authenticate verify_read token proof target query revision
      connection snapshot read history =
    (let live = reference_read_source connection snapshot in
      if \<not> identity_read_allowed directory policy authenticate verify_read token proof target
          (Historical_Data query revision) (identity_source live)
      then Identity_Read_Rejected
      else if \<not> read_authority_available (regulated_read_world live)
      then Identity_Read_Unavailable
      else case historical_reference_observation True (\<lambda>row. read row query) revision history of
        None \<Rightarrow> Authorized_Data Product_Read_Unavailable
      | Some (actual,value) \<Rightarrow> Authorized_Data (Historical_Prefix_Value actual value))"

theorem the_reference_endpoint_current_value_consumes_current_identity_and_exact_cut:
  assumes "reference_current_read directory policy authenticate verify_read token proof target query expected
      connection snapshot read history = Authorized_Data (Current_Cut_Value actual value)"
  shows "identity_read_allowed directory policy authenticate verify_read token proof target
      (Current_Data query expected) (identity_source (reference_read_source connection snapshot))"
    "actual = expected" "actual = reference_observed_cut history"
    "value = read (last (reference_history_prefixes history)) query"
  using assms by (auto simp: reference_current_read_def current_reference_observation_def Let_def
    split: if_splits)

theorem the_reference_endpoint_historical_value_consumes_current_identity_and_its_exact_prefix:
  assumes "reference_historical_read directory policy authenticate verify_read token proof target query revision
      connection snapshot read history = Authorized_Data (Historical_Prefix_Value actual value)"
  shows "identity_read_allowed directory policy authenticate verify_read token proof target
      (Historical_Data query revision) (identity_source (reference_read_source connection snapshot))"
    "actual = revision" "revision < length (reference_history_prefixes history)"
    "value = read (reference_history_prefixes history ! revision) query"
  using assms by (auto simp: reference_historical_read_def historical_reference_observation_def Let_def
    split: if_splits)

lemma reference_current_and_historical_reads_refuse_an_identity_without_permission:
  assumes "\<not> identity_read_allowed directory policy authenticate verify_read token proof target
      (Current_Data query expected) (identity_source (reference_read_source connection snapshot))"
    "\<not> identity_read_allowed directory policy authenticate verify_read token proof target
      (Historical_Data query revision) (identity_source (reference_read_source connection snapshot))"
  shows "reference_current_read directory policy authenticate verify_read token proof target query expected
      connection snapshot read history = Identity_Read_Rejected"
    "reference_historical_read directory policy authenticate verify_read token proof target query revision
      connection snapshot read history = Identity_Read_Rejected"
  using assms by (simp_all add: reference_current_read_def reference_historical_read_def Let_def)

lemma a_prior_cut_remains_stale_even_when_the_current_value_is_the_same:
  assumes "expected \<noteq> reference_observed_cut history"
  shows "reference_current_read directory policy authenticate verify_read token proof target query expected
      connection snapshot read history \<noteq> Authorized_Data (Current_Cut_Value actual value)"
  using assms by (auto simp: reference_current_read_def current_reference_observation_def Let_def split: if_splits)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_reference_endpoint_current_value_consumes_current_identity_and_exact_cut
      the_reference_endpoint_historical_value_consumes_current_identity_and_its_exact_prefix
      reference_current_and_historical_reads_refuse_an_identity_without_permission
      a_prior_cut_remains_stale_even_when_the_current_value_is_the_same})
  then () else error "Unexpected oracle in reference read consumption"
\<close>

end
