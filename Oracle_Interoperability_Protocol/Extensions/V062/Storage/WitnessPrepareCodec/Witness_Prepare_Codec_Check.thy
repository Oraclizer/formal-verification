theory Witness_Prepare_Codec_Check
  imports "OIP_Witness_Mirror_Check.Witness_Mirror_Check"
begin

section \<open>Authority-prepare decode boundary and exact re-encoding\<close>

text \<open>
  The outer option represents the result of reading the authority value. The
  inner option supplies the typed decoding and re-encoding projection at the
  host codec boundary. The original bytes are kept separately. These definitions
  do not define the host JSON parser, serializer, or storage protocol.
\<close>

datatype wmcc_result =
  WMCC_Read_Failed | WMCC_Codec_Failed | WMCC_Noncanonical |
  WMCC_Mirror_Refused | WMCC_Accepted

type_synonym wmcc_prepare = "nat list \<times> bool \<times> wm_mark \<times> nat list list"

definition wmcc_authority_for ::
  "bool \<Rightarrow> (nat list \<times> wmcc_prepare option) option \<Rightarrow> nat \<Rightarrow>
    wm_mark \<Rightarrow> wm_mark option \<Rightarrow> nat list \<Rightarrow> wmcc_result"
where
  "wmcc_authority_for check read limit selected parent selected_raw =
    (case read of
      None \<Rightarrow> WMCC_Read_Failed
    | Some (raw, None) \<Rightarrow> WMCC_Codec_Failed
    | Some (raw, Some (reencoded, profile_matches, base, preparations)) \<Rightarrow>
        if check \<and> reencoded \<noteq> raw then WMCC_Noncanonical
        else if wm_authority_for True profile_matches limit selected parent
                  selected_raw base preparations then WMCC_Accepted
        else WMCC_Mirror_Refused)"

lemma wmcc_missing_read_and_codec_fail_first:
  "wmcc_authority_for check None limit selected parent selected_raw = WMCC_Read_Failed"
  "wmcc_authority_for check (Some (raw, None)) limit selected parent selected_raw = WMCC_Codec_Failed"
  by (simp_all add: wmcc_authority_for_def)

lemma wmcc_accepted_iff_exact_codec_and_mirror:
  "(wmcc_authority_for True (Some (raw, Some (reencoded, profile_matches, base, preparations)))
      limit selected parent selected_raw = WMCC_Accepted) \<longleftrightarrow>
    reencoded = raw \<and>
    wm_authority_for True profile_matches limit selected parent selected_raw base preparations"
  by (auto simp: wmcc_authority_for_def)

lemma wmcc_roundtrip_removal_changes_acceptance_iff:
  "((wmcc_authority_for False (Some (raw, Some (reencoded, profile_matches, base, preparations)))
      limit selected parent selected_raw = WMCC_Accepted) \<and>
    (wmcc_authority_for True (Some (raw, Some (reencoded, profile_matches, base, preparations)))
      limit selected parent selected_raw \<noteq> WMCC_Accepted)) \<longleftrightarrow>
    reencoded \<noteq> raw \<and>
    wm_authority_for True profile_matches limit selected parent selected_raw base preparations"
  by (auto simp: wmcc_authority_for_def)

lemma wmcc_acceptance_preserves_prepared_reference_mirror:
  fixes observed :: "'control reference_witness_cut"
  assumes accept: "wmcc_authority_for True (Some (raw, Some (reencoded, profile_matches, base, preparations)))
      limit selected parent selected_raw = WMCC_Accepted"
    and current: "base = selected \<Longrightarrow> mirrored = Some observed"
    and prepared: "parent = Some base \<Longrightarrow> selected_raw \<in> set preparations \<Longrightarrow>
      \<exists>proposal \<in> proposed. proposal_after proposal = observed"
  shows "prepared_mirror_agrees mirrored proposed observed"
proof -
  from accept have mirror:
    "wm_authority_for True profile_matches limit selected parent selected_raw base preparations"
    by (simp add: wmcc_accepted_iff_exact_codec_and_mirror)
  show ?thesis
    by (rule wm_native_mirror_refines_the_prepared_reference_mirror[OF mirror current prepared])
qed

fun wmcc_result_word :: "wmcc_result \<Rightarrow> integer" where
  "wmcc_result_word WMCC_Read_Failed = 0"
| "wmcc_result_word WMCC_Codec_Failed = 1"
| "wmcc_result_word WMCC_Noncanonical = 2"
| "wmcc_result_word WMCC_Mirror_Refused = 3"
| "wmcc_result_word WMCC_Accepted = 4"

definition wmcc_byte_rows :: "integer list list \<Rightarrow> bool" where
  "wmcc_byte_rows blobs \<longleftrightarrow>
    list_all (\<lambda>word. 0 \<le> word \<and> word < 256) (concat blobs)"

definition wmcc_observe :: "bool \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> integer list list \<Rightarrow> integer list" where
  "wmcc_observe check phase header blobs =
    (if phase = 0 then (if header = [] \<and> blobs = [] then [0] else [])
     else if phase = 1 then
       (case blobs of [raw] \<Rightarrow> if header = [] \<and> wmcc_byte_rows [raw] then [1] else [] | _ \<Rightarrow> [])
     else if phase = 2 then
       (case (header, blobs) of
         ([profile,limit,curr_rev,base_rev,has_parent,prev_rev],
          raw # reencoded # curr_digest # base_digest # prev_digest # selected_raw # preparations) \<Rightarrow>
          if profile < 0 \<or> profile > 1 \<or> limit < 0 \<or> curr_rev < 0 \<or> base_rev < 0 \<or>
             has_parent < 0 \<or> has_parent > 1 \<or> prev_rev < 0 \<or>
             length curr_digest \<noteq> 32 \<or> length base_digest \<noteq> 32 \<or> length prev_digest \<noteq> 32 \<or>
             \<not> wmcc_byte_rows blobs then []
          else
            (let selected = (nat_of_integer curr_rev, map nat_of_integer curr_digest);
                 base = (nat_of_integer base_rev, map nat_of_integer base_digest);
                 parent = (if has_parent = 0 then None else Some (nat_of_integer prev_rev, map nat_of_integer prev_digest));
                 prep = (map nat_of_integer reencoded, profile = 1, base, map (map nat_of_integer) preparations);
                 read = Some (map nat_of_integer raw, Some prep)
             in [wmcc_result_word (wmcc_authority_for check read (nat_of_integer limit) selected parent
                    (map nat_of_integer selected_raw))])
        | _ \<Rightarrow> [])
     else [])"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms wmcc_missing_read_and_codec_fail_first
    wmcc_accepted_iff_exact_codec_and_mirror wmcc_roundtrip_removal_changes_acceptance_iff
    wmcc_acceptance_preserves_prepared_reference_mirror}) then ()
  else error "Unexpected oracle in witness prepare codec check"
\<close>

export_code wmcc_observe in SML module_name OIP_Witness_Prepare_Codec file_prefix "oip_witness_prepare_codec"

end
