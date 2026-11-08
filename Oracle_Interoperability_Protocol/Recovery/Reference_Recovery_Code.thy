theory Reference_Recovery_Code
  imports "Pilot_Storage"
begin

datatype native_reopen_witness =
    Native_Direct
  | Native_Independent_Current
  | Native_Witness_Unavailable

definition native_reopen_view where
  "native_reopen_view attached requires_independent witness profile native =
    (if \<not> attached \<or> witness = Native_Witness_Unavailable \<or>
        requires_independent \<noteq> (witness = Native_Independent_Current)
     then None
     else case native_current native of None \<Rightarrow> None
       | Some address \<Rightarrow> if address_profile address \<noteq> profile then None
           else native_records native address)"

lemma required_recovery_witness_cannot_fall_back_to_a_direct_open:
  "native_reopen_view attached True Native_Direct profile native = None"
  "native_reopen_view attached True Native_Witness_Unavailable profile native = None"
  by (simp_all add: native_reopen_view_def)

lemma a_different_profile_cannot_reuse_the_current_native_record:
  assumes "native_current native = Some address" "address_profile address \<noteq> profile"
  shows "native_reopen_view attached required witness profile native = None"
  using assms by (simp add: native_reopen_view_def)

theorem every_exact_native_reopen_selects_related_model_records:
  fixes native :: "('hash, 'native) native_journal_view"
    and model :: "'hash placed_digest recovery_store"
  assumes opened: "native_reopen_view attached required witness profile native = Some exact_image"
    and related: "journal_views_related (\<lambda>native_image record. relates native_image (image_records record)) native model"
    and addressed: "\<And>address records. native_current native = Some address \<Longrightarrow>
       flushed_records model (model_head_of address) = Some records \<Longrightarrow>
       head_for_record digest records = model_head_of address"
    and authenticated: "attachment_profile attachment = profile"
  obtains records :: "'hash placed_digest persisted_commit" where "relates exact_image (image_records records)"
    "reopen_from_authenticated_head digest profile (Some attachment) model =
      Some (reopen_retained_product (attachment_connection attachment) (image_records records))"
    "capture_retained_product
      (reopen_retained_product (attachment_connection attachment) (image_records records)) = image_records records"
proof -
  obtain address where current: "native_current native = Some address"
    and profile: "address_profile address = profile"
    and image_at: "native_records native address = Some exact_image"
    using opened by (cases "native_current native") (auto simp: native_reopen_view_def split: if_splits)
  have live: "committed_head model = Some (model_head_of address)"
    using related current by (simp add: journal_views_related_def)
  have row: "rel_option (\<lambda>native_image record. relates native_image (image_records record))
      (native_records native address) (flushed_records model (model_head_of address))"
    using related unfolding journal_views_related_def by blast
  obtain records where stored: "flushed_records model (model_head_of address) = Some records"
    and actual: "relates exact_image (image_records records)"
    using row image_at by (cases "flushed_records model (model_head_of address)") auto
  have response: "reopen_from_authenticated_head digest profile (Some attachment) model =
      Some (reopen_retained_product (attachment_connection attachment) (image_records records))"
    using live stored addressed[OF current stored] authenticated profile
    by (simp add: reopen_from_authenticated_head_def model_head_of_def)
  have exact: "capture_retained_product
      (reopen_retained_product (attachment_connection attachment) (image_records records)) = image_records records"
    by (rule product_round_trip_preserves_the_durable_projection)
  show thesis
  proof (rule that[of records])
    show "relates exact_image (image_records records)" by (rule actual)
    show "reopen_from_authenticated_head digest profile (Some attachment) model =
      Some (reopen_retained_product (attachment_connection attachment) (image_records records))" by (rule response)
    show "capture_retained_product
      (reopen_retained_product (attachment_connection attachment) (image_records records)) = image_records records"
      by (rule exact)
  qed
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms required_recovery_witness_cannot_fall_back_to_a_direct_open
      a_different_profile_cannot_reuse_the_current_native_record every_exact_native_reopen_selects_related_model_records})
  then () else error "Unexpected oracle in native recovery code correspondence"
\<close>

end
