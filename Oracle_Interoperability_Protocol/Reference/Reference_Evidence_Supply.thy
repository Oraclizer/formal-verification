theory Reference_Evidence_Supply
  imports "Reference_Authority_Trace"
begin

datatype evidence_purpose = Source_Terminal | Legal_Order | Enforcement_Order | Trusted_Time
  | Secondary_Ack | Ownership_Consent | Recovery_Attachment | Recovery_Repair

record ('payload, 'epoch) reference_evidence_claim =
  evidence_purpose :: evidence_purpose
  evidence_profile :: nat
  evidence_epoch :: 'epoch
  evidence_payload :: 'payload

definition registered_reference_proof where
  "registered_reference_proof keys verify claim signer proof \<longleftrightarrow>
    (\<exists>key. keys (evidence_purpose claim) (evidence_epoch claim) signer = Some key \<and> verify key claim proof)"

definition source_certificate_quorum where
  "source_certificate_quorum keys verify required claim proofs \<longleftrightarrow>
    evidence_purpose claim = Source_Terminal \<and> 0 < required \<and> required \<le> length proofs \<and>
    distinct (map fst proofs) \<and>
    distinct (map (\<lambda>(signer, _). keys Source_Terminal (evidence_epoch claim) signer) proofs) \<and>
    (\<forall>(signer, proof) \<in> set proofs. registered_reference_proof keys verify claim signer proof)"

definition authoritative_source_certificate where
  "authoritative_source_certificate terminal_at keys verify required claim proofs \<longleftrightarrow>
    (let (origin, terminal) = evidence_payload claim in
     terminal_at (evidence_profile claim, origin) = Some (evidence_epoch claim, terminal) \<and>
     source_certificate_quorum keys verify required claim proofs)"

theorem a_source_certificate_counts_distinct_registered_keys_for_the_exact_claim:
  assumes "source_certificate_quorum keys verify required claim proofs"
  shows "required \<le> card (fst ` set proofs)"
    "required \<le> card ((\<lambda>(signer, _). keys Source_Terminal (evidence_epoch claim) signer) ` set proofs)"
    "evidence_purpose claim = Source_Terminal"
    "(signer, proof) \<in> set proofs \<Longrightarrow> \<exists>key.
      keys Source_Terminal (evidence_epoch claim) signer = Some key \<and> verify key claim proof"
proof -
  let ?registered_keys = "map (\<lambda>(signer, _). keys Source_Terminal (evidence_epoch claim) signer) proofs"
  have signers: "distinct (map fst proofs)" and keys: "distinct ?registered_keys"
    and size: "required \<le> length proofs" and kind: "evidence_purpose claim = Source_Terminal"
    using assms by (simp_all add: source_certificate_quorum_def)
  show "required \<le> card (fst ` set proofs)"
    using distinct_card[OF signers] size by simp
  show "required \<le> card ((\<lambda>(signer, _). keys Source_Terminal (evidence_epoch claim) signer) ` set proofs)"
    using distinct_card[OF keys] size by simp
  show "evidence_purpose claim = Source_Terminal" by (rule kind)
  show "(signer, proof) \<in> set proofs \<Longrightarrow> \<exists>key.
      keys Source_Terminal (evidence_epoch claim) signer = Some key \<and> verify key claim proof"
    using assms kind by (auto simp: source_certificate_quorum_def registered_reference_proof_def)
qed

lemma a_missing_current_purpose_key_cannot_supply_proof:
  assumes "keys (evidence_purpose claim) (evidence_epoch claim) signer = None"
  shows "\<not> registered_reference_proof keys verify claim signer proof"
  using assms by (simp add: registered_reference_proof_def)

theorem two_certificates_for_one_authoritative_origin_bind_the_same_epoch_and_decision:
  assumes first: "authoritative_source_certificate terminal_at keys verify required first first_proofs"
    and second: "authoritative_source_certificate terminal_at keys verify required second second_proofs"
    and origin: "fst (evidence_payload first) = fst (evidence_payload second)"
    and profile: "evidence_profile first = evidence_profile second"
  shows "evidence_epoch first = evidence_epoch second" "evidence_payload first = evidence_payload second"
proof -
  have read_first: "terminal_at (evidence_profile first, fst (evidence_payload first)) =
      Some (evidence_epoch first, snd (evidence_payload first))"
    using first by (cases "evidence_payload first") (simp add: authoritative_source_certificate_def)
  have read_second: "terminal_at (evidence_profile second, fst (evidence_payload second)) =
      Some (evidence_epoch second, snd (evidence_payload second))"
    using second by (cases "evidence_payload second") (simp add: authoritative_source_certificate_def)
  show "evidence_epoch first = evidence_epoch second" using read_first read_second origin profile by simp
  have terminal: "snd (evidence_payload first) = snd (evidence_payload second)"
    using read_first read_second origin profile by simp
  show "evidence_payload first = evidence_payload second" by (rule prod_eqI[OF origin terminal])
qed

lemma an_unrecorded_source_decision_cannot_be_supplied_by_a_quorum:
  assumes "terminal_at (evidence_profile claim, fst (evidence_payload claim)) \<noteq>
      Some (evidence_epoch claim, snd (evidence_payload claim))"
  shows "\<not> authoritative_source_certificate terminal_at keys verify required claim proofs"
  using assms by (cases "evidence_payload claim") (simp add: authoritative_source_certificate_def)

theorem a_quorum_of_actual_source_signers_consumes_their_durable_origin_record:
  assumes accepted: "source_certificate_quorum keys verify required claim proofs"
    and issued: "\<And>signer proof. (signer, proof) \<in> set proofs \<Longrightarrow>
      registered_reference_proof keys verify claim signer proof \<Longrightarrow>
      terminal_at (evidence_profile claim, fst (evidence_payload claim)) =
        Some (evidence_epoch claim, snd (evidence_payload claim))"
  shows "authoritative_source_certificate terminal_at keys verify required claim proofs"
proof -
  have nonempty: "proofs \<noteq> []"
    using accepted by (auto simp: source_certificate_quorum_def)
  then obtain vote rest where votes: "proofs = vote # rest" by (cases proofs) auto
  obtain signer vote_proof where "vote = (signer, vote_proof)" by (cases vote) auto
  then have member: "(signer, vote_proof) \<in> set proofs" using votes by simp
  have verified: "registered_reference_proof keys verify claim signer vote_proof"
    using accepted member by (auto simp: source_certificate_quorum_def)
  have exact: "terminal_at (evidence_profile claim, fst (evidence_payload claim)) =
      Some (evidence_epoch claim, snd (evidence_payload claim))"
    by (rule issued[OF member verified])
  show ?thesis using exact accepted
    by (cases "evidence_payload claim") (simp add: authoritative_source_certificate_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms a_source_certificate_counts_distinct_registered_keys_for_the_exact_claim
      a_missing_current_purpose_key_cannot_supply_proof
      two_certificates_for_one_authoritative_origin_bind_the_same_epoch_and_decision
      an_unrecorded_source_decision_cannot_be_supplied_by_a_quorum
      a_quorum_of_actual_source_signers_consumes_their_durable_origin_record})
  then () else error "Unexpected oracle in reference evidence supply"
\<close>

end
