theory Independent_Publication_Check
  imports "OIP_Direct_Publication_Check.Direct_Publication_Check"
begin

section \<open>Independent writer, protected head, and current lineage floor\<close>

text \<open>
  The typed readback supplies an authenticated current head and checkpoint.
  The protected head is the exact selected address. The checkpoint's floor
  supplies the ancestry check and can refer to an earlier record. The file
  decoder, lineage consumer, and independent journal verifier each supply
  their own result to this view.
\<close>

record ('digest,'writer) ip_checkpoint =
  ip_floor :: "'digest dp_address option"
  ip_protected :: "'digest dp_address option"
  ip_generation :: nat
  ip_writer :: 'writer

definition ip_select where
  "ip_select check_generation ip_observed ip_readback ip_expected ip_record ip_image ip_lineage ip_verified =
    (case ip_readback of None \<Rightarrow> DP_Stopped DP_Hold
     | Some (ip_read_head,ip_current) \<Rightarrow>
       if (check_generation \<and> ip_generation ip_current \<noteq> ip_generation ip_observed) \<or>
          ip_writer ip_current \<noteq> ip_writer ip_observed \<or> ip_protected ip_current \<noteq> Some ip_expected
       then DP_Stopped DP_Hold
       else case ip_floor ip_current of None \<Rightarrow> DP_Stopped DP_Hold | Some ip_current_floor \<Rightarrow>
         (case dp_confirm True ip_expected ip_read_head ip_record ip_image of
            DP_Stopped ip_error \<Rightarrow> DP_Stopped ip_error
          | DP_Selected \<Rightarrow> (case ip_lineage ip_current_floor of Some ip_error \<Rightarrow> DP_Stopped ip_error
              | None \<Rightarrow> if ip_verified then DP_Selected else DP_Stopped DP_Hold)))"

lemma ip_selection_requires_current_writer_protected_head_and_verified_lineage:
  assumes "ip_select True ip_observed ip_readback ip_expected ip_record ip_image ip_lineage ip_verified = DP_Selected"
  obtains ip_current ip_current_floor where
    "ip_readback = Some (Some ip_expected,ip_current)"
    "ip_generation ip_current = ip_generation ip_observed"
    "ip_writer ip_current = ip_writer ip_observed"
    "ip_protected ip_current = Some ip_expected"
    "ip_floor ip_current = Some ip_current_floor"
    "ip_image = DP_Exact_Image ip_record"
    "ip_lineage ip_current_floor = None"
    "ip_verified"
  using assms by (auto simp: ip_select_def dp_confirm_def split: option.splits prod.splits dp_image.splits dp_reply.splits if_splits)

lemma ip_missing_current_floor_blocks_before_the_record_check:
  assumes "ip_floor ip_current = None"
  shows "ip_select check_generation ip_observed (Some (ip_read_head,ip_current)) ip_expected ip_record
       ip_image ip_lineage ip_verified = DP_Stopped DP_Hold"
  using assms by (simp add: ip_select_def)

lemma ip_generation_only_removal_exposes_the_same_readback:
  assumes generation: "ip_generation ip_current \<noteq> ip_generation ip_observed"
    and writer: "ip_writer ip_current = ip_writer ip_observed"
    and protected: "ip_protected ip_current = Some ip_expected"
    and floor: "ip_floor ip_current = Some ip_current_floor"
    and lineage: "ip_lineage ip_current_floor = None"
  shows "ip_select True ip_observed (Some (Some ip_expected,ip_current)) ip_expected ip_record
       (DP_Exact_Image ip_record) ip_lineage True = DP_Stopped DP_Hold"
    "ip_select False ip_observed (Some (Some ip_expected,ip_current)) ip_expected ip_record
       (DP_Exact_Image ip_record) ip_lineage True = DP_Selected"
  using generation writer protected floor lineage by (simp_all add: ip_select_def dp_confirm_def)

lemma ip_reads_the_current_floor_after_writer_binding:
  "ip_select check_generation (ip_observed\<lparr>ip_floor := ip_other_floor\<rparr>) ip_readback ip_expected
      ip_record ip_image ip_lineage ip_verified =
   ip_select check_generation ip_observed ip_readback ip_expected ip_record ip_image ip_lineage ip_verified"
  by (simp add: ip_select_def split: option.splits prod.splits)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ip_selection_requires_current_writer_protected_head_and_verified_lineage
      ip_missing_current_floor_blocks_before_the_record_check ip_generation_only_removal_exposes_the_same_readback
      ip_reads_the_current_floor_after_writer_binding}) then ()
  else error "Unexpected oracle in independent publication readback"
\<close>

end
