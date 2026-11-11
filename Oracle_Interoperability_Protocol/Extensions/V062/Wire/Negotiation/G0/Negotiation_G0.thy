theory Negotiation_G0
  imports "OIP_V062_Negotiation_Core.Negotiation_List_Model"
begin

text \<open>All statements below use kernel proof methods and the explicit premises
of each statement. The recorded native build verifies the proofs.\<close>

definition ng_local :: n_offer where
  "ng_local = \<lparr>n_deployment = 7, n_sender = 2, n_receiver = 0,
    n_challenge = 3, n_expires = 200, n_versions = [5, 6],
    n_families = [1, 4, 6], n_atomicities = [1, 2], n_schemes = [1, 2]\<rparr>"

definition ng_remote :: n_offer where
  "ng_remote = \<lparr>n_deployment = 7, n_sender = 0, n_receiver = 2,
    n_challenge = 3, n_expires = 201, n_versions = [5, 6],
    n_families = [1, 4, 6, 7], n_atomicities = [2, 3], n_schemes = [1, 2]\<rparr>"

definition ng_current :: n_profile where
  "ng_current = \<lparr>n_version = 6, n_profile_families = [1, 4, 6],
    n_profile_atomicities = [2], n_profile_schemes = [1, 2]\<rparr>"

definition ng_legacy :: n_profile where
  "ng_legacy = \<lparr>n_version = 5, n_profile_families = [4, 6],
    n_profile_atomicities = [2], n_profile_schemes = [1]\<rparr>"

lemmas ng_defs = ng_local_def ng_remote_def ng_current_def ng_legacy_def
  n_select_def n_select_without_canonical_guard_def n_offer_canonical_def
  n_list_selected_def n_list_version_def n_intersect_def

lemma ng_normal_current:
  "n_select 5 False ng_local ng_remote = N_Selected ng_current"
  by (simp add: ng_defs)

lemma ng_explicit_legacy:
  "n_select 5 True ng_local (ng_remote\<lparr>n_versions := [5]\<rparr>) = N_Selected ng_legacy"
  by (simp add: ng_defs)

lemma ng_unsorted_guard_removal_reaches_selection:
  "n_select 5 True (ng_local\<lparr>n_families := [6, 1, 4]\<rparr>) ng_remote = N_Invalid_Format"
  "n_select_without_canonical_guard 5 True
     (ng_local\<lparr>n_families := [6, 1, 4]\<rparr>) ng_remote =
     N_Selected (ng_current\<lparr>n_profile_families := [6, 1, 4]\<rparr>)"
  by (simp_all add: ng_defs)

lemma ng_duplicate_guard_removal_reaches_selection:
  "n_select 5 True ng_local (ng_remote\<lparr>n_versions := [5, 6, 6]\<rparr>) = N_Invalid_Format"
  "n_select_without_canonical_guard 5 True ng_local
     (ng_remote\<lparr>n_versions := [5, 6, 6]\<rparr>) = N_Selected ng_current"
  by (simp_all add: ng_defs)

lemma ng_floor_guard_removal_reaches_legacy:
  "n_select 6 True (ng_local\<lparr>n_versions := [5]\<rparr>)
     (ng_remote\<lparr>n_versions := [5]\<rparr>) = N_Unsupported_Version"
  "n_select 0 True (ng_local\<lparr>n_versions := [5]\<rparr>)
     (ng_remote\<lparr>n_versions := [5]\<rparr>) = N_Selected ng_legacy"
  by (simp_all add: ng_defs)

lemma ng_legacy_permission_removal_reaches_legacy:
  "n_select 5 False ng_local (ng_remote\<lparr>n_versions := [5]\<rparr>) = N_Unsupported_Version"
  "n_select 5 True ng_local (ng_remote\<lparr>n_versions := [5]\<rparr>) = N_Selected ng_legacy"
  by (simp_all add: ng_defs)

lemma ng_empty_intersections_are_accepted:
  "n_select 5 False
     (ng_local\<lparr>n_families := [], n_atomicities := [], n_schemes := []\<rparr>) ng_remote =
     N_Selected \<lparr>n_version = 6, n_profile_families = [], n_profile_atomicities = [], n_profile_schemes = []\<rparr>"
  by (simp add: ng_defs)

lemma ng_current_profile_preserves_unknown_family_numbers:
  "n_select 5 False (ng_local\<lparr>n_families := [99]\<rparr>)
     (ng_remote\<lparr>n_families := [99]\<rparr>) =
     N_Selected (ng_current\<lparr>n_profile_families := [99]\<rparr>)"
  by (simp add: ng_defs)

lemma ng_set_abstraction_hides_the_unsorted_input:
  "n_set_selected 5 True (ng_local\<lparr>n_families := [6, 1, 4]\<rparr>) ng_remote =
     n_set_selected 5 True ng_local ng_remote"
  by (simp add: n_set_selected_def n_set_selected_version_def ng_local_def ng_remote_def insert_commute)

thm_oracles ng_normal_current ng_explicit_legacy
  ng_unsorted_guard_removal_reaches_selection ng_duplicate_guard_removal_reaches_selection
  ng_floor_guard_removal_reaches_legacy ng_legacy_permission_removal_reaches_legacy
  ng_empty_intersections_are_accepted ng_current_profile_preserves_unknown_family_numbers
  ng_set_abstraction_hides_the_unsorted_input

ML \<open>
  if null (Thm_Deps.all_oracles @{thms ng_normal_current ng_explicit_legacy
      ng_unsorted_guard_removal_reaches_selection ng_duplicate_guard_removal_reaches_selection
      ng_floor_guard_removal_reaches_legacy ng_legacy_permission_removal_reaches_legacy
      ng_empty_intersections_are_accepted ng_current_profile_preserves_unknown_family_numbers
      ng_set_abstraction_hides_the_unsorted_input})
  then writeln "NEGOTIATION_G0_ORACLES_EMPTY"
  else error "Negotiation G0 unexpectedly depends on an oracle"
\<close>

end
