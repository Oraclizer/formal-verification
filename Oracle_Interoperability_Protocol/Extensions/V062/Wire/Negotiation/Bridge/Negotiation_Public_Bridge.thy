theory Negotiation_Public_Bridge
  imports "OIP_Product.Wire_Negotiation"
    "OIP_V062_Negotiation_Core.Negotiation_List_Model"
begin

text \<open>This draft reuses the public selected_wire_version. The new
policy wrapper adds the existing implementation's explicit legacy permission
and version-5 capability restrictions. It is not an unconditional equivalence
claim about authenticated_wire_negotiation, whose legacy branch is wider.\<close>

definition n_public_offer :: "n_offer \<Rightarrow> peer_offer" where
  "n_public_offer offer = \<lparr>offer_deployment = n_deployment offer,
    offer_sender = n_sender offer, offer_receiver = n_receiver offer,
    offer_challenge = n_challenge offer, offer_expires = n_expires offer,
    offered_versions = set (n_versions offer),
    offered_families = {f. family_number f \<in> set (n_families offer)},
    offered_atomicities = set (n_atomicities offer), offered_schemes = set (n_schemes offer)\<rparr>"

definition n_public_profile :: "n_profile \<Rightarrow> negotiated_wire_profile" where
  "n_public_profile profile = \<lparr>negotiated_version = n_version profile,
    negotiated_families = {f. family_number f \<in> set (n_profile_families profile)},
    negotiated_atomicities = set (n_profile_atomicities profile),
    negotiated_schemes = set (n_profile_schemes profile)\<rparr>"

definition n_public_policy_selected :: "nat \<Rightarrow> bool \<Rightarrow> peer_offer \<Rightarrow> peer_offer \<Rightarrow> negotiated_wire_profile option" where
  "n_public_policy_selected floor legacy local remote =
    (case selected_wire_version floor
      ((offered_versions local \<inter> offered_versions remote) - (if legacy then {} else {5})) of
       None \<Rightarrow> None
     | Some v \<Rightarrow> Some \<lparr>negotiated_version = v,
         negotiated_families = (if v = 5
           then offered_families local \<inter> offered_families remote \<inter> {Wire_Query, Wire_Heartbeat}
           else offered_families local \<inter> offered_families remote),
         negotiated_atomicities = offered_atomicities local \<inter> offered_atomicities remote,
         negotiated_schemes = (if v = 5
           then offered_schemes local \<inter> offered_schemes remote \<inter> {1}
           else offered_schemes local \<inter> offered_schemes remote)\<rparr>)"

lemma n_legacy_family_numbers_are_exact:
  "(family_number family = 4 \<or> family_number family = 6) =
    (family = Wire_Query \<or> family = Wire_Heartbeat)"
  by (cases family) simp_all

lemma n_list_version_reuses_public_selector:
  "n_list_version floor legacy xs ys =
    selected_wire_version floor ((set xs \<inter> set ys) - (if legacy then {} else {5}))"
  by (auto simp: n_list_version_def selected_wire_version_def)

lemma n_list_selection_projects_to_extended_public_sets:
  "map_option n_public_profile (n_list_selected floor legacy local remote) =
    n_public_policy_selected floor legacy (n_public_offer local) (n_public_offer remote)"
  by (auto simp: n_list_selected_def n_list_version_def n_intersect_def
      n_public_offer_def n_public_profile_def n_public_policy_selected_def selected_wire_version_def
      n_legacy_family_numbers_are_exact set_eq_iff split: if_splits)

lemma n_existing_authenticated_v6_result_is_preserved:
  assumes "authenticated_wire_negotiation verify confirm deployment sender receiver challenge floor now local remote = Some profile"
    "6 \<in> offered_versions local" "6 \<in> offered_versions remote" "floor \<le> 6"
  shows "n_public_policy_selected floor legacy local remote = Some profile"
  using assms
  by (auto simp: authenticated_wire_negotiation_def n_public_policy_selected_def
      selected_wire_version_def Let_def split: if_splits)

lemma n_existing_selector_needs_the_explicit_legacy_policy:
  "selected_wire_version 5 {5} = Some 5"
  "n_list_version 5 False [5] [5] = None"
  by (simp_all add: selected_wire_version_def n_list_version_def)

lemma n_registered_family_number_has_a_constructor:
  assumes "number \<in> {1, 2, 3, 4, 5, 6, 7}"
  shows "\<exists>family. family_number family = number"
proof -
  have "number = 1 \<or> number = 2 \<or> number = 3 \<or> number = 4 \<or>
    number = 5 \<or> number = 6 \<or> number = 7"
    using assms by auto
  then show ?thesis by (elim disjE) (metis family_number.simps)+
qed

lemma n_family_projection_is_lossless_on_registered_numbers:
  assumes "set (n_families offer) \<subseteq> {1, 2, 3, 4, 5, 6, 7}"
  shows "family_number ` offered_families (n_public_offer offer) = set (n_families offer)"
proof -
  have witness: "\<exists>family. family_number family = number"
    if "number \<in> set (n_families offer)" for number
    using assms that n_registered_family_number_has_a_constructor by blast
  show ?thesis using witness by (auto simp: n_public_offer_def)
qed

lemma n_unknown_family_has_no_public_constructor:
  "{family. family_number family \<in> {99}} = {}"
proof -
  have "family_number family \<noteq> 99" for family by (cases family) simp_all
  then show ?thesis by auto
qed

thm_oracles n_list_version_reuses_public_selector
  n_list_selection_projects_to_extended_public_sets n_existing_authenticated_v6_result_is_preserved
  n_family_projection_is_lossless_on_registered_numbers n_unknown_family_has_no_public_constructor

ML \<open>
  if null (Thm_Deps.all_oracles @{thms n_list_and_extended_set_selection_agree
      n_list_version_reuses_public_selector n_list_selection_projects_to_extended_public_sets
      n_existing_authenticated_v6_result_is_preserved n_existing_selector_needs_the_explicit_legacy_policy
      n_family_projection_is_lossless_on_registered_numbers n_unknown_family_has_no_public_constructor})
  then writeln "NEGOTIATION_PUBLIC_BRIDGE_ORACLES_EMPTY"
  else error "Negotiation public bridge unexpectedly depends on an oracle"
\<close>

end
