theory Witness_Prepare_Compare_Link
  imports "OIP_Witness_Prepare_Codec_Check.Witness_Prepare_Codec_Check"
    "OIP_Etcd_Control_Confirmation.Etcd_Control_Confirmation"
begin

text \<open>Same-base prepare planning and conditional readback after an
  authority compare failure. Each projection supplies the exact host JSON
  re-encoding and typed prepare fields. The intended contender value is
  independent of the later physical readback.\<close>

record wpc_prepare_view =
  wpc_raw_prepare :: "nat list"
  wpc_reencoded_prepare :: "nat list"
  wpc_prepare_profile :: "nat list"
  wpc_prepare_base :: wm_mark
  wpc_preparations :: "nat list list"

record wpc_current_witness =
  wpc_current_raw :: "nat list"
  wpc_current_profile :: "nat list"
  wpc_current_mark :: wm_mark
  wpc_current_parent :: "wm_mark option"

definition wpc_codec_view where
  "wpc_codec_view wpc_expected wpc_view =
     Some (wpc_raw_prepare wpc_view,
       Some (wpc_reencoded_prepare wpc_view,wpc_prepare_profile wpc_view = wpc_expected,
         wpc_prepare_base wpc_view,wpc_preparations wpc_view))"

definition wpc_authority_for where
  "wpc_authority_for wpc_limit wpc_current wpc_view =
    wmcc_authority_for True (wpc_codec_view (wpc_current_profile wpc_current) wpc_view)
      wpc_limit (wpc_current_mark wpc_current) (wpc_current_parent wpc_current) (wpc_current_raw wpc_current)"

definition wpc_after_compare_false where
  "wpc_after_compare_false wpc_limit wpc_current wpc_target wpc_readback =
    (if wpc_authority_for wpc_limit wpc_current wpc_readback = WMCC_Accepted \<and>
        wpc_prepare_base wpc_readback = wpc_current_mark wpc_current \<and>
        List.member (wpc_preparations wpc_readback) wpc_target
     then Some wpc_target else None)"

lemma wpc_compare_false_accepts_only_exact_target_at_same_base:
  "wpc_after_compare_false wpc_limit wpc_current wpc_target wpc_readback = Some wpc_result \<longleftrightarrow>
    wpc_authority_for wpc_limit wpc_current wpc_readback = WMCC_Accepted \<and>
    wpc_prepare_base wpc_readback = wpc_current_mark wpc_current \<and>
    List.member (wpc_preparations wpc_readback) wpc_target \<and> wpc_result = wpc_target"
  by (auto simp: wpc_after_compare_false_def split: if_splits)

lemma wpc_compare_false_is_a_transport_result_before_the_witness_readback:
  assumes "ec_txn_revision wpc_cluster wpc_expected wpc_response = Some None"
  shows "ec_confirm_write True wpc_cluster wpc_expected wpc_key wpc_cap wpc_candidate wpc_response wpc_transport_readback = Some None"
  using assms by (simp add: ec_confirm_write_def)

definition wpc_intended_append where
  "wpc_intended_append wpc_limit wpc_cap wpc_current wpc_initial wpc_candidate wpc_intended \<longleftrightarrow>
    wpc_authority_for wpc_limit wpc_current wpc_intended = WMCC_Accepted \<and>
    length (wpc_raw_prepare wpc_intended) \<le> wpc_cap \<and>
    wpc_prepare_base wpc_intended = wpc_current_mark wpc_current \<and>
    \<not> List.member (wpc_preparations wpc_initial) wpc_candidate \<and>
    wpc_preparations wpc_intended = wpc_preparations wpc_initial @ [wpc_candidate]"

datatype wpc_prediction =
    WPC_Invalid_Plan
  | WPC_No_Target_On_Compare_False
  | WPC_Exact_Target_On_Compare_False "nat list"

definition wpc_predict where
  "wpc_predict wpc_limit wpc_cap wpc_current wpc_initial wpc_target wpc_contender wpc_original_intent wpc_contender_intent =
    (if wpc_authority_for wpc_limit wpc_current wpc_initial = WMCC_Accepted \<and>
        length (wpc_raw_prepare wpc_initial) \<le> wpc_cap \<and>
        wpc_prepare_base wpc_initial = wpc_current_mark wpc_current \<and>
        length (wpc_preparations wpc_initial) < wpc_limit \<and>
        wpc_intended_append wpc_limit wpc_cap wpc_current wpc_initial wpc_target wpc_original_intent \<and>
        wpc_intended_append wpc_limit wpc_cap wpc_current wpc_initial wpc_contender wpc_contender_intent
     then case wpc_after_compare_false wpc_limit wpc_current wpc_target wpc_contender_intent of
        None \<Rightarrow> WPC_No_Target_On_Compare_False
      | Some wpc_raw \<Rightarrow> WPC_Exact_Target_On_Compare_False wpc_raw
     else WPC_Invalid_Plan)"

lemma wpc_valid_intents_reduce_membership_to_exact_contender_bytes:
  assumes "wpc_predict wpc_limit wpc_cap wpc_current wpc_initial wpc_target wpc_contender
    wpc_original_intent wpc_contender_intent \<noteq> WPC_Invalid_Plan"
  shows "wpc_after_compare_false wpc_limit wpc_current wpc_target wpc_contender_intent =
    (if wpc_target = wpc_contender then Some wpc_target else None)"
proof -
  have initial:
    "\<not> List.member (wpc_preparations wpc_initial) wpc_target"
    using assms by (auto simp: wpc_predict_def wpc_intended_append_def split: if_splits)
  have intended: "wpc_intended_append wpc_limit wpc_cap wpc_current wpc_initial wpc_contender wpc_contender_intent"
    using assms by (auto simp: wpc_predict_def split: if_splits)
  show ?thesis
    using initial intended by (simp add: wpc_intended_append_def wpc_after_compare_false_def List.member_iff)
qed

lemma wpc_same_intended_readback_preserves_the_compare_false_prediction:
  assumes "wpc_actual_readback = wpc_contender_intent"
    "wpc_predict wpc_limit wpc_cap wpc_current wpc_initial wpc_target wpc_contender
      wpc_original_intent wpc_contender_intent \<noteq> WPC_Invalid_Plan"
  shows "wpc_after_compare_false wpc_limit wpc_current wpc_target wpc_actual_readback =
    (if wpc_target = wpc_contender then Some wpc_target else None)"
  using wpc_valid_intents_reduce_membership_to_exact_contender_bytes[OF assms(2)] assms(1) by simp

lemma wpc_physical_compare_false_and_exact_install_agree_with_the_plan:
  assumes "ec_txn_revision wpc_cluster wpc_expected wpc_response = Some None"
    "wpc_actual_readback = wpc_contender_intent"
    "wpc_predict wpc_limit wpc_cap wpc_current wpc_initial wpc_target wpc_contender
      wpc_original_intent wpc_contender_intent \<noteq> WPC_Invalid_Plan"
  shows "ec_confirm_write True wpc_cluster wpc_expected wpc_key wpc_cap wpc_candidate wpc_response wpc_transport_readback = Some None"
    "wpc_after_compare_false wpc_limit wpc_current wpc_target wpc_actual_readback =
      (if wpc_target = wpc_contender then Some wpc_target else None)"
  by (rule wpc_compare_false_is_a_transport_result_before_the_witness_readback[OF assms(1)],
      rule wpc_same_intended_readback_preserves_the_compare_false_prediction[OF assms(2,3)])

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms wpc_compare_false_accepts_only_exact_target_at_same_base
    wpc_compare_false_is_a_transport_result_before_the_witness_readback
    wpc_valid_intents_reduce_membership_to_exact_contender_bytes
    wpc_same_intended_readback_preserves_the_compare_false_prediction
    wpc_physical_compare_false_and_exact_install_agree_with_the_plan})
  then () else error "Unexpected oracle in same-base Witness prepare comparison"
\<close>

end
