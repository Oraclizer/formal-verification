theory Witness_Mirror_Check
  imports "OIP_Reference_Profile.Reference_Witness_Selection" "HOL-Library.Code_Target_Nat"
begin

section \<open>Exact prepared witness bytes and their parent mark\<close>

type_synonym wm_mark = "nat \<times> nat list"

definition wm_agrees :: "bool \<Rightarrow> wm_mark \<Rightarrow> wm_mark option \<Rightarrow> nat list \<Rightarrow> wm_mark \<Rightarrow> nat list list \<Rightarrow> bool" where
  "wm_agrees wm_check_parent wm_selected wm_parent wm_raw wm_base wm_preparations \<longleftrightarrow>
    wm_base = wm_selected \<or> ((\<not> wm_check_parent \<or> wm_parent = Some wm_base) \<and> wm_raw \<in> set wm_preparations)"

definition wm_authority_for where
  "wm_authority_for wm_check_parent wm_profile_matches wm_limit wm_selected wm_parent wm_raw wm_base wm_preparations \<longleftrightarrow>
    wm_profile_matches \<and> length wm_preparations \<le> wm_limit \<and>
    wm_agrees wm_check_parent wm_selected wm_parent wm_raw wm_base wm_preparations"

lemma wm_native_mirror_refines_the_prepared_reference_mirror:
  fixes wm_observed :: "'control reference_witness_cut"
  assumes "wm_authority_for True wm_profile_matches wm_limit wm_selected wm_parent wm_raw wm_base wm_preparations"
    "wm_base = wm_selected \<Longrightarrow> wm_mirrored = Some wm_observed"
    "wm_parent = Some wm_base \<Longrightarrow> wm_raw \<in> set wm_preparations \<Longrightarrow>
      \<exists>wm_proposal \<in> wm_prepared. proposal_after wm_proposal = wm_observed"
  shows "prepared_mirror_agrees wm_mirrored wm_prepared wm_observed"
  using assms by (auto simp: wm_authority_for_def wm_agrees_def prepared_mirror_agrees_def)

lemma wm_accepting_an_older_mirror_requires_both_exact_parent_and_bytes:
  assumes "wm_base \<noteq> wm_selected"
    "wm_authority_for True wm_profile_matches wm_limit wm_selected wm_parent wm_raw wm_base wm_preparations"
  shows "wm_parent = Some wm_base" "wm_raw \<in> set wm_preparations"
    "wm_profile_matches" "length wm_preparations \<le> wm_limit"
  using assms by (auto simp: wm_authority_for_def wm_agrees_def)

lemma wm_removing_the_parent_check_releases_the_same_bytes_from_an_unrelated_base:
  assumes "wm_base \<noteq> wm_selected" "wm_parent \<noteq> Some wm_base" "wm_raw \<in> set wm_preparations"
    "wm_profile_matches" "length wm_preparations \<le> wm_limit"
  shows "\<not> wm_authority_for True wm_profile_matches wm_limit wm_selected wm_parent wm_raw wm_base wm_preparations"
    "wm_authority_for False wm_profile_matches wm_limit wm_selected wm_parent wm_raw wm_base wm_preparations"
  using assms by (simp_all add: wm_authority_for_def wm_agrees_def)

definition wm_bit :: "bool \<Rightarrow> integer" where
  "wm_bit wm_value = (if wm_value then 1 else 0)"

definition wm_observe :: "bool \<Rightarrow> integer list \<Rightarrow> integer list list \<Rightarrow> integer list" where
  "wm_observe wm_check wm_header wm_blobs =
    (case (wm_header,wm_blobs) of
      ([wm_profile,wm_limit,wm_curr_rev,wm_base_rev,wm_has_parent,wm_prev_rev],
       wm_curr_digest # wm_base_digest # wm_prev_digest # wm_raw # wm_preparations) \<Rightarrow>
      if wm_profile < 0 \<or> wm_profile > 1 \<or> wm_limit < 0 \<or> wm_curr_rev < 0 \<or> wm_base_rev < 0 \<or>
         wm_has_parent < 0 \<or> wm_has_parent > 1 \<or> wm_prev_rev < 0 \<or>
         length wm_curr_digest \<noteq> 32 \<or> length wm_base_digest \<noteq> 32 \<or> length wm_prev_digest \<noteq> 32 \<or>
         \<not> list_all (\<lambda>wm_word. 0 \<le> wm_word \<and> wm_word < 256) (concat wm_blobs)
      then [] else
      (let wm_selected = (nat_of_integer wm_curr_rev,map nat_of_integer wm_curr_digest);
           wm_base = (nat_of_integer wm_base_rev,map nat_of_integer wm_base_digest);
           wm_parent = (if wm_has_parent = 0 then None else Some (nat_of_integer wm_prev_rev,map nat_of_integer wm_prev_digest));
           wm_bytes = map nat_of_integer wm_raw;
           wm_proposals = map (map nat_of_integer) wm_preparations
       in [wm_bit (wm_agrees wm_check wm_selected wm_parent wm_bytes wm_base wm_proposals),
           wm_bit (wm_authority_for wm_check (wm_profile = 1) (nat_of_integer wm_limit) wm_selected wm_parent wm_bytes wm_base wm_proposals)])
     | _ \<Rightarrow> [])"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms wm_native_mirror_refines_the_prepared_reference_mirror
    wm_accepting_an_older_mirror_requires_both_exact_parent_and_bytes
    wm_removing_the_parent_check_releases_the_same_bytes_from_an_unrelated_base}) then ()
  else error "Unexpected oracle in witness mirror check"
\<close>

export_code wm_observe in SML module_name OIP_Witness_Mirror file_prefix "oip_witness_mirror"

end
