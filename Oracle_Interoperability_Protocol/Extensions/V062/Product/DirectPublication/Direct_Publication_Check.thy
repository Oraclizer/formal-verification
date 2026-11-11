theory Direct_Publication_Check
  imports "OIP_Product.Recovery_Anchor"
begin

section \<open>Direct publication readback after a prepared record\<close>

text \<open>
  The native address adds file offset and length to the public authenticated
  head. The exact image lookup supplies its decoded record or its failure.
  The direct carrier separates the pre-publication result, an ambiguous
  compare-and-set reply, and the independent authoritative readback.
  The optional head is the result of a successful head read. A head read
  error returns Hold before the comparison represented here.
\<close>

type_synonym 'digest dp_address = "'digest commit_head \<times> nat \<times> nat"

datatype dp_refusal = DP_Hold | DP_Invalid_Image | DP_IO | DP_Publication nat
datatype dp_reply = DP_Selected | DP_Stopped dp_refusal
datatype dp_cas = DP_Cas_OK | DP_Cas_Uncertain | DP_Known_Refusal dp_refusal
datatype 'record dp_image = DP_Exact_Image 'record | DP_Image_Error dp_refusal

definition dp_confirm where
  "dp_confirm check_head dp_expected dp_read_head dp_record dp_read_image =
    (if check_head \<and> dp_read_head \<noteq> Some dp_expected then DP_Stopped DP_Hold
     else case dp_read_image of DP_Image_Error dp_error \<Rightarrow> DP_Stopped dp_error
       | DP_Exact_Image dp_read_record \<Rightarrow>
         if dp_read_record = dp_record then DP_Selected else DP_Stopped DP_Invalid_Image)"

fun dp_after_cas where
  "dp_after_cas check_head DP_Cas_OK dp_expected dp_head dp_record dp_read_image =
    dp_confirm check_head dp_expected dp_head dp_record dp_read_image"
| "dp_after_cas check_head DP_Cas_Uncertain dp_expected dp_head dp_record dp_read_image =
    dp_confirm check_head dp_expected dp_head dp_record dp_read_image"
| "dp_after_cas check_head (DP_Known_Refusal dp_error) dp_expected dp_head dp_record dp_read_image =
    DP_Stopped dp_error"

lemma dp_uncertain_cas_requires_the_same_exact_selection_as_success:
  "dp_after_cas True DP_Cas_Uncertain dp_expected dp_head dp_record dp_read_image =
   dp_after_cas True DP_Cas_OK dp_expected dp_head dp_record dp_read_image"
  by simp

lemma dp_a_known_refusal_does_not_read_the_candidate:
  "dp_after_cas True (DP_Known_Refusal dp_error) dp_expected dp_head dp_record dp_read_image = DP_Stopped dp_error"
  by simp

lemma dp_selection_requires_the_exact_head_and_record:
  assumes "dp_after_cas True dp_status dp_expected dp_head dp_record dp_read_image = DP_Selected"
  shows "dp_head = Some dp_expected" "dp_read_image = DP_Exact_Image dp_record"
  using assms by (cases dp_status; cases dp_read_image; auto simp: dp_confirm_def split: if_splits)+

lemma dp_the_same_flushed_record_can_be_selected_only_after_head_change:
  assumes "dp_head \<noteq> Some dp_expected"
  shows "dp_after_cas True DP_Cas_Uncertain dp_expected dp_head dp_record (DP_Exact_Image dp_record) = DP_Stopped DP_Hold"
    "dp_after_cas False DP_Cas_Uncertain dp_expected dp_head dp_record (DP_Exact_Image dp_record) = DP_Selected"
  using assms by (simp_all add: dp_confirm_def)

lemma dp_selected_direct_record_agrees_with_public_reopen:
  fixes dp_expected :: "'digest dp_address"
  assumes chosen: "dp_after_cas True dp_status dp_expected dp_head dp_record dp_read_image = DP_Selected"
    and address: "fst dp_expected = head_for_record dp_digest dp_record"
    and head: "map_option fst dp_head = committed_head dp_store"
    and decoded_record: "dp_read_image = DP_Exact_Image dp_record \<Longrightarrow>
      flushed_records dp_store (head_for_record dp_digest dp_record) = Some dp_record"
    and profile: "attachment_profile dp_attachment = image_profile dp_record"
  shows "reopen_from_authenticated_head dp_digest (image_profile dp_record) (Some dp_attachment) dp_store =
    Some (reopen_retained_product (attachment_connection dp_attachment) (image_records dp_record))"
proof -
  have selected_head: "committed_head dp_store = Some (head_for_record dp_digest dp_record)"
    using head address dp_selection_requires_the_exact_head_and_record(1)[OF chosen] by simp
  show ?thesis
    by (rule independently_anchored_records_construct_a_fresh_endpoint[OF selected_head
      decoded_record[OF dp_selection_requires_the_exact_head_and_record(2)[OF chosen]] profile])
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms dp_uncertain_cas_requires_the_same_exact_selection_as_success
      dp_a_known_refusal_does_not_read_the_candidate dp_selection_requires_the_exact_head_and_record
      dp_the_same_flushed_record_can_be_selected_only_after_head_change dp_selected_direct_record_agrees_with_public_reopen})
  then () else error "Unexpected oracle in direct publication readback"
\<close>

end
