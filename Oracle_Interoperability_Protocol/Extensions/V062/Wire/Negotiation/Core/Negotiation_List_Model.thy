theory Negotiation_List_Model
  imports Main
begin

text \<open>Isolated feasibility draft. Native checking is owned by Main.
The numeric carriers preserve unknown offered values; the production u64
representation is a separate input-bound obligation.\<close>

record n_offer =
  n_deployment :: nat
  n_sender :: nat
  n_receiver :: nat
  n_challenge :: nat
  n_expires :: nat
  n_versions :: "nat list"
  n_families :: "nat list"
  n_atomicities :: "nat list"
  n_schemes :: "nat list"

record n_profile =
  n_version :: nat
  n_profile_families :: "nat list"
  n_profile_atomicities :: "nat list"
  n_profile_schemes :: "nat list"

record n_set_profile =
  n_set_version :: nat
  n_set_families :: "nat set"
  n_set_atomicities :: "nat set"
  n_set_schemes :: "nat set"

fun n_strictly_sorted :: "nat list \<Rightarrow> bool" where
  "n_strictly_sorted [] = True"
| "n_strictly_sorted [x] = True"
| "n_strictly_sorted (x # y # xs) = (x < y \<and> n_strictly_sorted (y # xs))"

definition n_offer_canonical :: "n_offer \<Rightarrow> bool" where
  "n_offer_canonical offer \<longleftrightarrow>
    n_strictly_sorted (n_versions offer) \<and>
    n_strictly_sorted (n_families offer) \<and>
    n_strictly_sorted (n_atomicities offer) \<and>
    n_strictly_sorted (n_schemes offer)"

definition n_profile_canonical :: "n_profile \<Rightarrow> bool" where
  "n_profile_canonical profile \<longleftrightarrow>
    n_strictly_sorted (n_profile_families profile) \<and>
    n_strictly_sorted (n_profile_atomicities profile) \<and>
    n_strictly_sorted (n_profile_schemes profile)"

definition n_intersect :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "n_intersect xs ys = filter (\<lambda>x. x \<in> set ys) xs"

definition n_list_version :: "nat \<Rightarrow> bool \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat option" where
  "n_list_version floor legacy local remote =
    List.find (\<lambda>v. floor \<le> v \<and> (v \<noteq> 5 \<or> legacy) \<and>
      v \<in> set local \<and> v \<in> set remote) [6, 5]"

definition n_set_selected_version :: "nat \<Rightarrow> bool \<Rightarrow> nat set \<Rightarrow> nat option" where
  "n_set_selected_version floor legacy common =
    (if floor \<le> 6 \<and> 6 \<in> common then Some 6
     else if floor \<le> 5 \<and> legacy \<and> 5 \<in> common then Some 5 else None)"

definition n_list_selected :: "nat \<Rightarrow> bool \<Rightarrow> n_offer \<Rightarrow> n_offer \<Rightarrow> n_profile option" where
  "n_list_selected floor legacy local remote =
    (case n_list_version floor legacy (n_versions local) (n_versions remote) of
       None \<Rightarrow> None
     | Some v \<Rightarrow> Some \<lparr>n_version = v,
         n_profile_families = filter (\<lambda>f. v \<noteq> 5 \<or> f \<in> {4, 6})
           (n_intersect (n_families local) (n_families remote)),
         n_profile_atomicities = n_intersect (n_atomicities local) (n_atomicities remote),
         n_profile_schemes = filter (\<lambda>s. v \<noteq> 5 \<or> s = 1)
           (n_intersect (n_schemes local) (n_schemes remote))\<rparr>)"

definition n_abstract_profile :: "n_profile \<Rightarrow> n_set_profile" where
  "n_abstract_profile profile = \<lparr>n_set_version = n_version profile,
    n_set_families = set (n_profile_families profile),
    n_set_atomicities = set (n_profile_atomicities profile),
    n_set_schemes = set (n_profile_schemes profile)\<rparr>"

definition n_set_selected :: "nat \<Rightarrow> bool \<Rightarrow> n_offer \<Rightarrow> n_offer \<Rightarrow> n_set_profile option" where
  "n_set_selected floor legacy local remote =
    (case n_set_selected_version floor legacy (set (n_versions local) \<inter> set (n_versions remote)) of
       None \<Rightarrow> None
     | Some v \<Rightarrow> Some \<lparr>n_set_version = v,
         n_set_families = {f \<in> set (n_families local) \<inter> set (n_families remote). v \<noteq> 5 \<or> f \<in> {4, 6}},
         n_set_atomicities = set (n_atomicities local) \<inter> set (n_atomicities remote),
         n_set_schemes = {s \<in> set (n_schemes local) \<inter> set (n_schemes remote). v \<noteq> 5 \<or> s = 1}\<rparr>)"

datatype n_selection = N_Invalid_Format | N_Unsupported_Version | N_Selected n_profile

definition n_select :: "nat \<Rightarrow> bool \<Rightarrow> n_offer \<Rightarrow> n_offer \<Rightarrow> n_selection" where
  "n_select floor legacy local remote =
    (if n_offer_canonical local \<and> n_offer_canonical remote
     then case n_list_selected floor legacy local remote of
       None \<Rightarrow> N_Unsupported_Version | Some profile \<Rightarrow> N_Selected profile
     else N_Invalid_Format)"

text \<open>The unchecked helper exists only to name the deletion of the
canonical-list guard. It is not another production admission path.\<close>

definition n_select_without_canonical_guard where
  "n_select_without_canonical_guard floor legacy local remote =
    (case n_list_selected floor legacy local remote of
       None \<Rightarrow> N_Unsupported_Version | Some profile \<Rightarrow> N_Selected profile)"

lemma n_adjacent_guard_is_strict_order:
  "n_strictly_sorted xs = sorted_wrt (<) xs"
  by (induction xs rule: n_strictly_sorted.induct) (auto intro: less_trans)

lemma n_intersect_denotes_set_intersection:
  "set (n_intersect xs ys) = set xs \<inter> set ys"
  by (auto simp: n_intersect_def)

lemma n_list_and_set_version_agree:
  "n_list_version floor legacy xs ys = n_set_selected_version floor legacy (set xs \<inter> set ys)"
  by (auto simp: n_list_version_def n_set_selected_version_def)

lemma n_list_and_extended_set_selection_agree:
  "map_option n_abstract_profile (n_list_selected floor legacy local remote) =
    n_set_selected floor legacy local remote"
  by (auto simp: n_list_selected_def n_set_selected_def n_abstract_profile_def
      n_list_and_set_version_agree n_intersect_def split: option.splits)

lemma n_filter_preserves_canonical_order:
  assumes "n_strictly_sorted xs"
  shows "n_strictly_sorted (filter P xs)"
  using assms sorted_wrt_filter by (simp add: n_adjacent_guard_is_strict_order)

lemma n_selected_lists_are_canonical:
  assumes "n_offer_canonical local"
    "n_list_selected floor legacy local remote = Some profile"
  shows "n_profile_canonical profile"
  using assms
  by (auto simp: n_offer_canonical_def n_profile_canonical_def n_list_selected_def
      n_intersect_def intro: n_filter_preserves_canonical_order split: option.splits)

lemma n_canonical_lists_with_equal_sets_are_equal:
  assumes "n_strictly_sorted xs" "n_strictly_sorted ys" "set xs = set ys"
  shows "xs = ys"
  using assms strict_sorted_equal by (metis n_adjacent_guard_is_strict_order)

lemma n_selected_version_respects_floor:
  assumes "n_list_version floor legacy xs ys = Some v"
  shows "floor \<le> v"
  using assms by (auto simp: n_list_version_def split: if_splits)

lemma n_version_five_requires_explicit_legacy:
  assumes "n_list_version floor legacy xs ys = Some 5"
  shows "legacy"
  using assms by (auto simp: n_list_version_def split: if_splits)

lemma n_current_common_version_wins:
  assumes "floor \<le> 6" "6 \<in> set xs" "6 \<in> set ys"
  shows "n_list_version floor legacy xs ys = Some 6"
  using assms by (simp add: n_list_version_def)

lemma n_malformed_offer_is_rejected:
  assumes "\<not> n_offer_canonical local \<or> \<not> n_offer_canonical remote"
  shows "n_select floor legacy local remote = N_Invalid_Format"
  using assms by (auto simp: n_select_def)

end
