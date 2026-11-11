theory Publication_Endorser_Link
  imports "OIP_Resolver_Waiting_Model_Link.Resolver_Waiting_ABI"
    "OIP_Message_Code.Wire_Code_Session_Authentication"
    "OIP_Message_Code.Wire_Code_Source_Call_Signature"
begin

text \<open>The ordered ordinary Refund has an admitted recovery endorser.
  The publication callback checks the current worker, exact credential
  packet and current endorser, then admits the envelope at the saved
  admission clock. The recovery signature and source certificate are
  fixed admission evidence. Candidate construction and durable selection
  are outside this callback.\<close>

record pea_wire_input =
  pea_packet :: wire_bytes
  pea_credential_packet :: wire_bytes
  pea_expected_core :: wire_bytes
  pea_envelope_preimage :: wire_bytes
  pea_envelope_signature :: wire_bytes
  pea_certificate :: wire_bytes
  pea_worker_preimage :: wire_bytes
  pea_worker_signature :: wire_bytes
  pea_owner_preimage :: wire_bytes
  pea_owner_signature :: wire_bytes
  pea_endorsement_preimage :: wire_bytes
  pea_endorsement_signature :: wire_bytes

record pea_context =
  pea_session_config :: code_source_session_config
  pea_snapshot :: code_source_identity_snapshot
  pea_worker_peer :: code_source_signing_peer
  pea_owner_public_key :: wire_bytes
  pea_owner_recovery_assets :: "nat list"
  pea_owner_registry :: "(nat \<times> nat) list"
  pea_recorded_binding :: code_source_binding
  pea_revoked :: "nat list"
  pea_owner_proof :: session_proof
  pea_channel :: code_channel_guard
  pea_boundary :: wire_boundary

definition pea_exact_before where
  "pea_exact_before pea_hash pea_control pea_control_sha pea_record pea_head pea_file_len pea_config_raw pea_policy_sha \<longleftrightarrow>
    0 < fst pea_control \<and> pea_hash (snd pea_control) = Some pea_control_sha \<and>
    0 < rdw_address_length pea_head \<and> length pea_record = rdw_address_length pea_head \<and>
    rdw_span_ends_by (rdw_address_offset pea_head) (rdw_address_length pea_head) pea_file_len \<and>
    pea_hash pea_record = Some (rdw_address_hash pea_head) \<and>
    pea_hash (code_json_ascii ''oip/reference-authority-policy/v1'' @ [0] @ pea_config_raw) = Some pea_policy_sha"

definition pea_digest where
  "pea_digest pea_hash pea_raw = (case pea_hash pea_raw of None \<Rightarrow> [] | Some pea_sha \<Rightarrow> pea_sha)"

definition pea_auth_at where
  "pea_auth_at pea_context pea_hash pea_verify pea_preimage pea_signature pea_proof pea_now =
    code_source_authenticate_session_bytes (pea_session_config pea_context) (pea_digest pea_hash) pea_verify
      pea_preimage pea_signature pea_proof (Some pea_now)"

definition pea_active_at where
  "pea_active_at pea_context pea_hash pea_verify pea_preimage pea_signature pea_proof pea_now =
    code_source_active_identity
      (\<lambda>_ pea_current_proof. pea_auth_at pea_context pea_hash pea_verify pea_preimage pea_signature pea_current_proof pea_now)
      () pea_proof (pea_snapshot pea_context)"

datatype pea_recheck = PEA_Current_Identities | PEA_Worker_Refused | PEA_Owner_Refused

definition pea_recheck where
  "pea_recheck pea_expected_worker pea_current_worker pea_expected_owner pea_current_owner pea_packet_raw pea_credential_raw =
    (if pea_current_worker \<noteq> Some pea_expected_worker \<or> \<not> code_matches_signed_packet pea_packet_raw pea_credential_raw
     then PEA_Worker_Refused
     else if pea_current_owner \<noteq> Some pea_expected_owner then PEA_Owner_Refused
     else PEA_Current_Identities)"

lemma pea_a_current_worker_does_not_replace_the_current_owner_check:
  assumes "pea_current_worker = Some pea_expected_worker" "code_matches_signed_packet pea_packet_raw pea_credential_raw"
    "pea_current_owner \<noteq> Some pea_expected_owner"
  shows "pea_recheck pea_expected_worker pea_current_worker pea_expected_owner pea_current_owner
    pea_packet_raw pea_credential_raw = PEA_Owner_Refused"
  using assms by (simp add: pea_recheck_def)

lemma pea_a_token_past_its_expiry_is_refused_at_publication:
  assumes "code_decode_session_claim_preimage pea_preimage = Some pea_claim"
    "token_claim_expires pea_claim < pea_now"
  shows "pea_auth_at pea_context pea_hash pea_verify pea_preimage pea_signature pea_proof pea_now = None"
  using assms by (auto simp: pea_auth_at_def code_source_authenticate_session_bytes_def
    code_source_session_time_current_def split: option.splits if_splits)

definition pea_admission_at where
  "pea_admission_at pea_context pea_verify pea_packet_value pea_admitted pea_boundary_clock =
    (let pea_scope = (pea_boundary pea_context)\<lparr>boundary_now := pea_boundary_clock\<rparr>;
         pea_peer_key = source_signing_public_key (pea_worker_peer pea_context);
         pea_cut = source_identity_cut (pea_snapshot pea_context)
     in case code_boundary_at (Some (pea_scope,pea_peer_key)) (pea_channel pea_context)
          (boundary_deployment pea_scope) pea_cut (Some pea_admitted) False of Inl _ \<Rightarrow> False
        | Inr (pea_live_scope,pea_live_key) \<Rightarrow>
            code_admit_packet (\<lambda>_ pea_msg pea_sig. pea_verify pea_live_key pea_msg pea_sig)
              pea_packet_value (pea_live_scope\<lparr>boundary_now := pea_admitted\<rparr>) = None)"

definition pea_scope_at_admission where
  "pea_scope_at_admission pea_context pea_verify pea_packet_value pea_payload pea_worker_proof pea_worker pea_owner pea_wire pea_admitted =
    (let pea_core = packet_core pea_packet_value; pea_binding = source_payload_binding pea_payload;
         pea_asset = source_binding_asset pea_binding; pea_target = source_payload_endpoint pea_payload;
         pea_peer = pea_worker_peer pea_context
     in pea_worker = source_signing_identity pea_peer \<and>
        identity_principal pea_worker = source_payload_caller pea_payload \<and>
        proof_session pea_worker_proof = source_payload_session pea_payload \<and>
        pea_target \<in> source_identity_endpoints (pea_snapshot pea_context) \<and>
        code_source_session_call_grant pea_peer (proof_session pea_worker_proof) pea_target Execute_Ordinary pea_asset \<and>
        map_of (pea_owner_registry pea_context) pea_asset = Some (identity_principal pea_owner) \<and>
        pea_binding = pea_recorded_binding pea_context \<and>
        List.member (pea_owner_recovery_assets pea_context) pea_asset \<and>
        \<not> List.member (pea_revoked pea_context) (identity_principal pea_worker) \<and>
        \<not> List.member (pea_revoked pea_context) (identity_principal pea_owner) \<and>
        pea_verify (pea_owner_public_key pea_context) (pea_endorsement_preimage pea_wire) (pea_endorsement_signature pea_wire) \<and>
        source_payload_cut pea_payload = source_identity_cut (pea_snapshot pea_context) \<and>
        wire_target_domain pea_core = pea_target \<and>
        length (pea_packet pea_wire) \<le> boundary_max_frame (pea_boundary pea_context) \<and>
        pea_admission_at pea_context pea_verify pea_packet_value pea_admitted pea_admitted)"

fun pea_identity_words :: "registered_identity option \<Rightarrow> nat list" where
  "pea_identity_words None = []"
| "pea_identity_words (Some pea_id) =
     [identity_principal pea_id,identity_domain pea_id,identity_ocid pea_id,identity_rai pea_id]"

definition pea_publication_row where
  "pea_publication_row pea_context pea_hash pea_verify pea_wire pea_packet_value pea_worker_proof
     pea_worker pea_owner pea_admitted pea_now =
    (let pea_worker_now = pea_auth_at pea_context pea_hash pea_verify (pea_worker_preimage pea_wire)
          (pea_worker_signature pea_wire) pea_worker_proof pea_now;
         pea_owner_now = pea_auth_at pea_context pea_hash pea_verify (pea_owner_preimage pea_wire)
          (pea_owner_signature pea_wire) (pea_owner_proof pea_context) pea_now;
         pea_check = pea_recheck pea_worker pea_worker_now pea_owner pea_owner_now (pea_packet pea_wire) (pea_credential_packet pea_wire);
         pea_result = (case pea_check of PEA_Worker_Refused \<Rightarrow> 2 | PEA_Owner_Refused \<Rightarrow> 3
           | PEA_Current_Identities \<Rightarrow>
                if pea_admission_at pea_context pea_verify pea_packet_value pea_admitted pea_now then 1 else 4)
     in [[pea_result,pea_admitted,pea_now],pea_identity_words pea_worker_now,pea_identity_words pea_owner_now])"

definition pea_trace where
  "pea_trace pea_context pea_hash pea_verify pea_wire pea_admitted pea_tick =
    (if pea_tick > 1 then [[0]]
     else case decode_wire_packet (pea_packet pea_wire) of None \<Rightarrow> [[0]]
       | Some pea_packet_value \<Rightarrow>
        let pea_core = packet_core pea_packet_value in
        if encode_wire_core pea_core \<noteq> pea_expected_core pea_wire \<or>
           envelope_signing_bytes pea_core \<noteq> pea_envelope_preimage pea_wire \<or>
           packet_signature pea_packet_value \<noteq> pea_envelope_signature pea_wire
        then [[0]]
        else (case code_decode_ordinary pea_core of
          Code_Ordinary_Ready pea_native pea_credential pea_versions (Wire_Refund pea_generation pea_ref) \<Rightarrow>
            let pea_payload = code_source_payload_from_native pea_core pea_native pea_credential pea_versions
                  (Wire_Refund pea_generation pea_ref);
                pea_worker_proof = \<lparr>proof_session = native_session pea_native,
                  proof_epoch = cut_authority_epoch (source_identity_cut (pea_snapshot pea_context))\<rparr>;
                pea_admitted_worker = pea_active_at pea_context pea_hash pea_verify (pea_worker_preimage pea_wire)
                  (pea_worker_signature pea_wire) pea_worker_proof pea_admitted;
                pea_admitted_owner = pea_active_at pea_context pea_hash pea_verify (pea_owner_preimage pea_wire)
                  (pea_owner_signature pea_wire) (pea_owner_proof pea_context) pea_admitted
            in case (pea_admitted_worker,pea_admitted_owner) of (Some pea_worker,Some pea_owner) \<Rightarrow>
                 if native_proof_bytes pea_native = [pea_certificate pea_wire] \<and>
                    pea_scope_at_admission pea_context pea_verify pea_packet_value pea_payload pea_worker_proof pea_worker pea_owner pea_wire pea_admitted
                 then [[fst (native_id pea_native),snd (native_id pea_native),pea_generation,pea_ref],
                       pea_identity_words pea_admitted_worker,pea_identity_words pea_admitted_owner]
                    @ rdw_payload_rows pea_payload @
                    pea_publication_row pea_context pea_hash pea_verify pea_wire pea_packet_value pea_worker_proof
                      pea_worker pea_owner pea_admitted (pea_admitted + pea_tick)
                 else [[0]]
               | _ \<Rightarrow> [[0]]
         | _ \<Rightarrow> [[0]]))"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms pea_a_current_worker_does_not_replace_the_current_owner_check
      pea_a_token_past_its_expiry_is_refused_at_publication
      source_session_authentication_keeps_the_current_record_grants_time_and_curve_inputs
      ordered_publication_can_reuse_its_admission_time_without_retesting_a_later_clock})
  then () else error "Unexpected oracle in publication endorser reauthorization"
\<close>

end
