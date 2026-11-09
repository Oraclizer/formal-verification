theory Sync_V061_Attestation
  imports "OIP_Sync_V061_Position_Definitions.Sync_V061_Attestation_Model"
begin

lemma sync_decoded_proof_is_the_original_canonical_blob:
  assumes "sync_decode_proof raw = Some (a,votes)"
  shows "wire_octets raw" "sync_proof_bytes a votes = raw"
proof -
  have accepted: "code_reencoding_decode wire_octets sync_parse_proof
      (\<lambda>(statement,proofs). Some (sync_proof_bytes statement proofs)) raw = Some (a,votes)"
    using assms by (simp add: sync_decode_proof_def)
  show "wire_octets raw"
    by (rule an_accepted_generated_value_passes_the_exact_encoder(1)[OF accepted])
  show "sync_proof_bytes a votes = raw"
    using an_accepted_generated_value_passes_the_exact_encoder(3)[OF accepted] by simp
qed

lemma sync_accepted_proof_binds_every_request_field_and_current_roster:
  assumes "sync_proof_ok verify registry core r a votes"
  shows "sync_format a = 1" "sync_claim a = 1" "sync_deployment a = wire_deployment core"
    "(sync_asset a, sync_origin a) = sync_key r" "sync_item a = sync_requested r"
    "sync_predecessor a = sync_claimed_prior r"
    "sync_current_roster registry (sync_origin a) = Some (sync_origin_epoch (sync_item a), sync_roster a)"
  using assms by (simp_all add: sync_proof_ok_def)

theorem sync_accepted_quorum_verifies_every_supplied_signature:
  assumes accepted: "sync_proof_ok verify registry core r a votes"
  obtains quorum keys where
    "sync_registered_rosters registry (sync_deployment a,sync_origin a,sync_origin_epoch (sync_item a),sync_roster a) =
      Some (quorum,keys)"
    "0 < quorum" "quorum \<le> card (fst ` set votes)"
    "quorum \<le> card ((keys \<circ> fst) ` set votes)"
    "sorted_wrt (<) (map fst votes)" "distinct (map (keys \<circ> fst) votes)"
    "\<forall>(signer,signature) \<in> set votes. \<exists>key. keys signer = Some key \<and>
        verify key (sync_statement_bytes a) signature"
proof -
  obtain quorum keys where chosen:
    "sync_registered_rosters registry (sync_deployment a,sync_origin a,sync_origin_epoch (sync_item a),sync_roster a) =
      Some (quorum,keys)"
    and size: "0 < quorum" "quorum \<le> length votes"
    and ids: "sorted_wrt (<) (map fst votes)" and distinct_keys: "distinct (map (keys \<circ> fst) votes)"
    and valid: "\<forall>(signer,signature) \<in> set votes. \<exists>key. keys signer = Some key \<and>
        verify key (sync_statement_bytes a) signature"
    using accepted by (auto simp: sync_proof_ok_def split: option.splits prod.splits)
  have distinct_ids: "distinct (map fst votes)" using ids by (simp add: strict_sorted_iff)
  have count_ids: "quorum \<le> card (fst ` set votes)"
    using distinct_card[OF distinct_ids] size(2) by simp
  have count_keys: "quorum \<le> card ((keys \<circ> fst) ` set votes)"
    using distinct_card[OF distinct_keys] size(2) by simp
  show thesis using that[OF chosen size(1) count_ids count_keys ids distinct_keys valid] .
qed

lemma sync_historical_roster_does_not_authorize_a_fresh_proof:
  assumes "sync_current_roster registry (sync_origin a) \<noteq> Some (sync_origin_epoch (sync_item a), sync_roster a)"
  shows "\<not> sync_proof_ok verify registry core r a votes"
  using assms by (simp add: sync_proof_ok_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_decoded_proof_is_the_original_canonical_blob
    sync_accepted_proof_binds_every_request_field_and_current_roster
    sync_accepted_quorum_verifies_every_supplied_signature sync_historical_roster_does_not_authorize_a_fresh_proof})
  then () else error "Unexpected oracle in SyncCommitment attestation"
\<close>

end
