theory Pilot_Storage
  imports "OIP_Product.Recovery_Commit" "Reference_Authority_Grants"
begin

record 'hash native_address =
  address_profile :: recovery_profile
  address_sequence :: nat
  address_offset :: nat
  address_length :: nat
  address_hash :: 'hash

type_synonym 'hash placed_digest = "nat \<times> nat \<times> 'hash"

definition model_head_of :: "'hash native_address \<Rightarrow> 'hash placed_digest commit_head" where
  "model_head_of address =
    \<lparr>head_profile = address_profile address, head_sequence = address_sequence address,
     head_digest = (address_offset address, address_length address, address_hash address)\<rparr>"

lemma model_head_of_reflects_exact_address:
  "model_head_of a = model_head_of b \<longleftrightarrow> a = b"
  by (cases a; cases b) (simp add: model_head_of_def)

record ('hash, 'image) native_journal_view =
  native_current :: "'hash native_address option"
  native_records :: "'hash native_address \<Rightarrow> 'image option"

definition journal_views_related where
  "journal_views_related relates native model \<longleftrightarrow>
    map_option model_head_of (native_current native) = committed_head model \<and>
    (\<forall>address. rel_option relates
       (native_records native address) (flushed_records model (model_head_of address)))"

definition native_confirm_reply where
  "native_confirm_reply native expected expected_image reply =
    (if native_current native = Some expected \<and> native_records native expected = Some expected_image
     then Some reply else None)"

definition model_confirm_reply where
  "model_confirm_reply model expected records reply =
    (if committed_head model = Some expected \<and> flushed_records model expected = Some records
     then Some reply else None)"

lemma exact_retained_readback_matches:
  assumes views: "journal_views_related relates native model"
    and compared: "\<And>n m. native_records native expected = Some n \<Longrightarrow>
      flushed_records model (model_head_of expected) = Some m \<Longrightarrow>
      relates n m \<Longrightarrow> (n = expected_image \<longleftrightarrow> m = records)"
  shows "map_option convert (native_confirm_reply native expected expected_image reply) =
    model_confirm_reply model (model_head_of expected) records (convert reply)"
proof -
  have heads: "(native_current native = Some expected) =
      (committed_head model = Some (model_head_of expected))"
    using views by (cases "native_current native") (auto simp: journal_views_related_def model_head_of_reflects_exact_address)
  have pair: "rel_option relates (native_records native expected)
      (flushed_records model (model_head_of expected))"
    using views unfolding journal_views_related_def by blast
  have bodies: "(native_records native expected = Some expected_image) =
      (flushed_records model (model_head_of expected) = Some records)"
    using pair compared
    by (cases "native_records native expected"; cases "flushed_records model (model_head_of expected)")
       auto
  show ?thesis by (simp add: native_confirm_reply_def model_confirm_reply_def heads bodies)
qed

definition native_guarded_reply where
  "native_guarded_reply checked definite_refusal changed previous next old_image new_image reply current =
    (if \<not> checked \<or> (changed \<and> definite_refusal) then None
     else if changed then native_confirm_reply current next new_image reply
     else native_confirm_reply current previous old_image reply)"

definition model_guarded_reply where
  "model_guarded_reply checked definite_refusal changed previous old_records prepared digest reply current =
    (if \<not> checked \<or> (changed \<and> definite_refusal) then None
     else if changed then issue_committed_response digest prepared current
     else model_confirm_reply current previous old_records reply)"

theorem guarded_storage_matches_replies_at_the_confirmed_cut:
  assumes views: "journal_views_related relates native model"
    and old: "\<And>n m. native_records native previous = Some n \<Longrightarrow>
      flushed_records model (model_head_of previous) = Some m \<Longrightarrow>
      relates n m \<Longrightarrow> (n = old_image \<longleftrightarrow> m = old_records)"
    and new: "\<And>n m. native_records native candidate = Some n \<Longrightarrow>
      flushed_records model (model_head_of candidate) = Some m \<Longrightarrow>
      relates n m \<Longrightarrow> (n = new_image \<longleftrightarrow> m = prepared_record prepared)"
    and head: "head_for_record digest (prepared_record prepared) = model_head_of candidate"
    and reply: "prepared_reply prepared = convert reply"
  shows "map_option convert
    (native_guarded_reply checked refusal changed previous candidate old_image new_image reply native) =
    model_guarded_reply checked refusal changed (model_head_of previous) old_records
      prepared digest (convert reply) model"
proof -
  have old_readback: "map_option convert (native_confirm_reply native previous old_image reply) =
      model_confirm_reply model (model_head_of previous) old_records (convert reply)"
    by (rule exact_retained_readback_matches[OF views old])
  have new_readback: "map_option convert (native_confirm_reply native candidate new_image reply) =
      model_confirm_reply model (model_head_of candidate) (prepared_record prepared) (convert reply)"
    by (rule exact_retained_readback_matches[OF views new])
  show ?thesis
    using old_readback new_readback
    by (cases checked; cases refusal; cases changed)
       (simp_all add: native_guarded_reply_def model_guarded_reply_def issue_committed_response_def
          model_confirm_reply_def Let_def head reply)
qed

lemma a_definite_refusal_cannot_use_an_apparently_matching_write_readback:
  "native_guarded_reply True True True previous candidate old_image new_image reply current = None"
  by (simp add: native_guarded_reply_def)

lemma a_changed_storage_location_cannot_release_the_prepared_reply:
  assumes "native_current current = Some observed" "observed \<noteq> candidate"
  shows "native_guarded_reply True False True previous candidate old_image new_image reply current = None"
  using assms by (simp add: native_guarded_reply_def native_confirm_reply_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms model_head_of_reflects_exact_address
      exact_retained_readback_matches guarded_storage_matches_replies_at_the_confirmed_cut
      a_definite_refusal_cannot_use_an_apparently_matching_write_readback
      a_changed_storage_location_cannot_release_the_prepared_reply})
  then () else error "Unexpected oracle in pilot storage correspondence"
\<close>

end
