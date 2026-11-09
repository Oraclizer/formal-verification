theory Sync_V061_Strict_Proof_Link
  imports "OIP_Sync_V061_Extraction_V1.Sync_V061_Observation_Export"
begin

definition sync_proof_structure_allowed :: "sync_statement \<Rightarrow> sync_votes \<Rightarrow> bool" where
  "sync_proof_structure_allowed statement votes \<longleftrightarrow>
    sync_format statement = 1 \<and> sync_claim statement = 1 \<and> sorted_wrt (<) (map fst votes)"

definition sync_decode_proof_strict :: "wire_bytes \<Rightarrow> (sync_statement \<times> sync_votes) option" where
  "sync_decode_proof_strict raw = Option.bind (sync_decode_proof raw) (\<lambda>(statement, votes).
    if sync_proof_structure_allowed statement votes then Some (statement, votes) else None)"

lemma sync_strict_proof_success:
  "sync_decode_proof_strict raw = Some (statement, votes) \<longleftrightarrow>
    sync_decode_proof raw = Some (statement, votes) \<and> sync_proof_structure_allowed statement votes"
  by (auto simp: sync_decode_proof_strict_def bind_eq_Some_conv split: prod.splits if_splits)

lemma sync_strict_proof_rejects_unsupported_or_unordered:
  assumes "sync_decode_proof raw = Some (statement, votes)"
    "sync_format statement \<noteq> 1 \<or> sync_claim statement \<noteq> 1 \<or> \<not> sorted_wrt (<) (map fst votes)"
  shows "sync_decode_proof_strict raw = None"
  using assms by (simp add: sync_decode_proof_strict_def sync_proof_structure_allowed_def)

lemma sync_strict_proof_preserves_verification:
  "(sync_decode_proof_strict raw = Some (statement, votes) \<and>
      sync_proof_ok verify registry core request statement votes) \<longleftrightarrow>
    (sync_decode_proof raw = Some (statement, votes) \<and>
      sync_proof_ok verify registry core request statement votes)"
  by (auto simp: sync_strict_proof_success sync_proof_structure_allowed_def sync_proof_ok_def
    split: option.splits prod.splits)

lemma sync_strict_proof_rejection_already_fails_fresh_verification:
  assumes "sync_decode_proof_strict (sync_attestation request) = None"
    "sync_signed_cut request = sync_current_cut state"
  shows "sync_fresh_assess verify state core request = Sync_Reject Sync_Proof_Rejected"
proof (cases "sync_decode_proof (sync_attestation request)")
  case None
  with assms(2) show ?thesis by (simp add: sync_fresh_assess_def)
next
  case (Some decoded)
  obtain statement votes where decoded: "decoded = (statement, votes)" by (cases decoded)
  note preserves = sync_strict_proof_preserves_verification[where raw="sync_attestation request"
    and statement=statement and votes=votes and verify=verify
    and registry="sync_origin_registry (sync_selected_policy state)" and core=core and request=request]
  have "\<not> sync_proof_ok verify (sync_origin_registry (sync_selected_policy state)) core request statement votes"
    using preserves by (simp add: assms(1) Some decoded)
  with assms(2) Some decoded show ?thesis by (simp add: sync_fresh_assess_def)
qed

definition sync_proof_integer_observation_strict :: "integer list \<Rightarrow> (integer list \<times> integer list list) option" where
  "sync_proof_integer_observation_strict raw =
    (if list_all (\<lambda>octet. 0 \<le> octet \<and> octet < 256) raw then
       case sync_decode_proof_strict (map nat_of_integer raw) of
         None \<Rightarrow> None
       | Some _ \<Rightarrow> sync_proof_integer_observation raw
     else None)"

lemma sync_strict_observation_reuses_exact_structure:
  assumes "sync_decode_proof_strict (map nat_of_integer raw) = Some decoded"
  shows "sync_proof_integer_observation_strict raw = sync_proof_integer_observation raw"
  using assms by (simp add: sync_proof_integer_observation_strict_def sync_proof_integer_observation_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_strict_proof_success
    sync_strict_proof_rejects_unsupported_or_unordered sync_strict_proof_preserves_verification
    sync_strict_proof_rejection_already_fails_fresh_verification sync_strict_observation_reuses_exact_structure})
  then () else error "Unexpected oracle in the strict Sync proof observation"
\<close>

export_code sync_proof_integer_observation_strict
  in SML module_name OIP_Sync_Strict_Proof_Link file_prefix "oip_sync_strict_proof_link"

end
