theory Reference_Signed_Provider
  imports "Reference_Authority_Trace" "Reference_Ordered_Control"
begin

definition selected_signed_provider where
  "selected_signed_provider stored_fingerprint configured_fingerprint \<longleftrightarrow>
    stored_fingerprint = Some configured_fingerprint"

definition supplied_reference_endpoint_allowed where
  "supplied_reference_endpoint_allowed stored_fingerprint configured_fingerprint control
      directory policy authenticate verify token proof target operation actor call_id payload source \<longleftrightarrow>
    selected_signed_provider stored_fingerprint configured_fingerprint \<and> actor \<notin> control_revoked control \<and>
    endpoint_call_allowed directory policy authenticate verify token proof target operation actor call_id payload source"

theorem a_reference_call_uses_the_selected_provider_and_current_authenticated_namespace:
  assumes "supplied_reference_endpoint_allowed stored_fingerprint configured_fingerprint control
    directory policy authenticate verify token proof target operation actor call_id payload source"
  shows "stored_fingerprint = Some configured_fingerprint"
    "actor \<notin> control_revoked control"
    "\<exists>identity. authenticate token = Some identity \<and> directory (fst call_id) = Some identity \<and>
      identity_principal identity = fst call_id \<and> verify identity proof target operation call_id payload"
proof -
  show "stored_fingerprint = Some configured_fingerprint" "actor \<notin> control_revoked control"
    using assms by (simp_all add: supplied_reference_endpoint_allowed_def selected_signed_provider_def)
  have admitted: "endpoint_call_allowed directory policy authenticate verify token proof target operation actor call_id payload source"
    using assms by (simp add: supplied_reference_endpoint_allowed_def)
  show "\<exists>identity. authenticate token = Some identity \<and> directory (fst call_id) = Some identity \<and>
      identity_principal identity = fst call_id \<and> verify identity proof target operation call_id payload"
    using endpoint_call_refines_authenticated_namespace[OF admitted] by blast
qed

lemma substituting_provider_configuration_or_revoking_the_actor_closes_the_same_call:
  assumes "stored_fingerprint \<noteq> Some configured_fingerprint \<or> actor \<in> control_revoked control"
  shows "\<not> supplied_reference_endpoint_allowed stored_fingerprint configured_fingerprint control
    directory policy authenticate verify token proof target operation actor call_id payload source"
  using assms by (auto simp: supplied_reference_endpoint_allowed_def selected_signed_provider_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms a_reference_call_uses_the_selected_provider_and_current_authenticated_namespace
      substituting_provider_configuration_or_revoking_the_actor_closes_the_same_call})
  then () else error "Unexpected oracle in selected signed provider"
\<close>

end
