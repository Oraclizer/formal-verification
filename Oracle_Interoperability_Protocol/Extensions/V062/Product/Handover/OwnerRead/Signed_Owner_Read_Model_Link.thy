theory Signed_Owner_Read_Model_Link
  imports "OIP_Secondary_Read_Export.Secondary_Read_Export"
    "OIP_Message_Code.Wire_Code_Session_Authentication"
begin

definition sor_identity :: "nat list \<Rightarrow> registered_identity" where
  "sor_identity sor_row = \<lparr>identity_principal = sor_row ! 0,identity_domain = sor_row ! 1,
    identity_ocid = sor_row ! 2,identity_rai = sor_row ! 3\<rparr>"

definition sor_identity_view where
  "sor_identity_view sor_id = [identity_principal sor_id,identity_domain sor_id,
    identity_ocid sor_id,identity_rai sor_id]"

definition sor_owner_state where
  "sor_owner_state sor_epoch sor_revision sor_directory sor_sessions sor_endpoints =
    \<lparr>source_identity_cut = \<lparr>cut_authority_epoch = sor_epoch,cut_revision = sor_revision\<rparr>,
      source_identity_directory = map_of (map (\<lambda>sor_row. (sor_row ! 0,sor_identity sor_row)) sor_directory),
      source_identity_sessions = map_of (map (\<lambda>sor_row. (sor_row ! 0,
        \<lparr>session_principal = sor_row ! 1,session_epoch = sor_row ! 2\<rparr>)) sor_sessions),
      source_identity_endpoints = set sor_endpoints\<rparr>"

fun sor_arrival where
  "sor_arrival Code_First = (0::nat)"
| "sor_arrival Code_Identical = 1"
| "sor_arrival Code_Replay_Conflict = 2"

fun sor_owner_option :: "nat option \<Rightarrow> nat list" where
  "sor_owner_option None = [0,0]"
| "sor_owner_option (Some sor_owner) = [1,sor_owner]"

fun sor_read_reply :: "nat option secondary_read_reply \<Rightarrow> nat list" where
  "sor_read_reply Secondary_Rejected = [0]"
| "sor_read_reply Secondary_Unavailable = [1]"
| "sor_read_reply (Secondary_Answer sor_owner) = [2] @ sor_owner_option sor_owner"

definition sor_bit :: "bool \<Rightarrow> nat" where
  "sor_bit sor_fact = (if sor_fact then 1 else 0)"

definition sor_wire_key_words where
  "sor_wire_key_words sor_core =
    (case code_transport_key sor_core of (sor_deployment,sor_source,sor_principal,sor_uuid) \<Rightarrow>
       [sor_deployment,sor_source,sor_principal] @ sor_uuid)"

definition sor_project_owner where
  "sor_project_owner sor_core sor_proof sor_target sor_asset sor_claim sor_state sor_profile sor_peer sor_issuer
      sor_now sor_prior sor_owners sor_grants =
    (let sor_epoch_match = token_claim_epoch sor_claim = proof_epoch sor_proof;
         sor_session_match = token_claim_session sor_claim = proof_session sor_proof;
         sor_profile_match = token_claim_profile sor_claim = sor_profile;
         sor_issuer_match = token_claim_issuer sor_claim = sor_issuer;
         sor_peer_match = token_claim_identity sor_claim = sor_peer;
         sor_clock_match = token_claim_issued sor_claim \<le> sor_now \<and> sor_now \<le> token_claim_expires sor_claim;
         sor_token_fields = sor_epoch_match \<and> sor_session_match \<and> sor_profile_match \<and>
           sor_issuer_match \<and> sor_peer_match \<and> sor_clock_match;
         sor_active = code_source_active_identity
           (\<lambda>_ _. if sor_token_fields then Some (token_claim_identity sor_claim) else None) () sor_proof sor_state;
         sor_header_match = (case sor_active of None \<Rightarrow> False | Some sor_id \<Rightarrow>
           identity_principal sor_id = wire_principal sor_core \<and> identity_domain sor_id = wire_source_domain sor_core);
         sor_endpoint = sor_target \<in> source_identity_endpoints sor_state;
         sor_grant = sor_asset \<in> set sor_grants;
         sor_exact = encode_wire_core sor_core;
         sor_binding = code_compare_binding sor_prior sor_exact;
         sor_selected_owner = secondary_owner_registry sor_owners sor_asset;
         sor_read_access = sor_header_match \<and> sor_grant \<and> sor_binding \<noteq> Code_Replay_Conflict
     in [[wire_principal sor_core,wire_key_number sor_core,wire_source_domain sor_core,wire_deployment sor_core,
            proof_session sor_proof,proof_epoch sor_proof,sor_target,sor_asset],
         sor_exact,
         [cut_authority_epoch (source_identity_cut sor_state),cut_revision (source_identity_cut sor_state)],
         sor_identity_view (token_claim_identity sor_claim) @
           [token_claim_session sor_claim,token_claim_epoch sor_claim,token_claim_issued sor_claim,token_claim_expires sor_claim],
         map sor_bit [sor_epoch_match,sor_session_match,sor_profile_match,sor_issuer_match,sor_peer_match,sor_clock_match],
         map sor_bit [sor_active \<noteq> None,sor_header_match,sor_endpoint,sor_grant],
         [sor_arrival sor_binding],
         sor_owner_option sor_selected_owner,
         sor_read_reply (secondary_gate sor_endpoint sor_read_access True sor_selected_owner),
         sor_read_reply (secondary_gate sor_endpoint sor_read_access False sor_selected_owner)])"

definition sor_trace where
  "sor_trace sor_inputs =
    (case sor_inputs of
      [[sor_packet,sor_expected_core,sor_preimage,sor_signature],[sor_claim_bytes],
       [[sor_epoch,sor_revision,sor_now,sor_deployment,sor_format,sor_authority,sor_version,sor_channel_deployment,
         sor_source,sor_target,sor_key_id]],[sor_peer],[sor_issuer],[sor_transport_key],[sor_prior],
       sor_directory,sor_sessions,sor_owners,[sor_endpoints],[sor_grants]] \<Rightarrow>
        if length sor_peer = 4 \<and> length sor_issuer = 32 \<and>
           list_all (\<lambda>sor_row. length sor_row = 4) sor_directory \<and>
           list_all (\<lambda>sor_row. length sor_row = 3) sor_sessions \<and>
           list_all (\<lambda>sor_row. length sor_row = 2) sor_owners \<and>
           list_all (\<lambda>sor_byte. sor_byte < 256)
             (sor_packet @ sor_expected_core @ sor_preimage @ sor_signature @ sor_claim_bytes @ sor_prior @ sor_issuer)
        then (case (decode_wire_packet sor_packet,code_decode_session_claim_preimage sor_claim_bytes) of
          (Some sor_decoded,Some sor_claim) \<Rightarrow>
            (let sor_core = packet_core sor_decoded in
             if encode_wire_packet sor_decoded = sor_packet \<and> encode_wire_core sor_core = sor_expected_core \<and>
                envelope_signing_bytes sor_core = sor_preimage \<and> packet_signature sor_decoded = sor_signature \<and>
                sor_wire_key_words sor_core = sor_transport_key \<and> wire_version sor_core = sor_version \<and>
                wire_deployment sor_core = sor_channel_deployment \<and> wire_source_domain sor_core = sor_source \<and>
                wire_target_domain sor_core = sor_target \<and> wire_key_number sor_core = sor_key_id
             then (case code_source_nonreceipt_read_service (0::nat) sor_core of
               Some (Service_Read _ sor_proof sor_decoded_target (Owner_Data sor_asset) None) \<Rightarrow>
                 Some (sor_project_owner sor_core sor_proof sor_decoded_target sor_asset sor_claim
                   (sor_owner_state sor_epoch sor_revision sor_directory sor_sessions sor_endpoints)
                   (sor_deployment,sor_format,sor_authority) (sor_identity sor_peer) sor_issuer sor_now
                   (if sor_prior = [] then None else Some sor_prior)
                   (map (\<lambda>sor_row. (sor_row ! 0,sor_row ! 1)) sor_owners) sor_grants)
              | _ \<Rightarrow> None)
             else None)
        | _ \<Rightarrow> None)
        else None
    | _ \<Rightarrow> None)"

lemma sor_mismatched_claim_refuses_before_external_crypto:
  assumes decoded: "code_decode_session_claim_preimage sor_preimage = Some sor_claim"
    and mismatch: "token_claim_epoch sor_claim \<noteq> proof_epoch sor_proof \<or>
      token_claim_session sor_claim \<noteq> proof_session sor_proof"
  shows "code_source_authenticate_session_bytes sor_configuration sor_sha sor_verify sor_preimage sor_signature
      sor_proof sor_now = None"
  using decoded mismatch by (simp add: code_source_authenticate_session_bytes_def)

context source_attestation
begin

lemma sor_authorized_registry_is_the_committed_owner:
  assumes token: "sor_authenticate sor_token = Some sor_identity_value"
    and allowed: "identity_read_allowed sor_directory sor_policy sor_authenticate sor_verify
      sor_token sor_proof sor_target (Owner_Data sor_asset) (identity_source sor_live)"
    and available: "read_authority_available (regulated_read_world sor_live)"
    and registry: "map_of sor_owners = product_owners (product_durable (identity_source sor_live))"
  shows "read_at_identity_endpoint sor_directory sor_policy sor_authenticate sor_verify
    sor_token sor_proof sor_target (Owner_Data sor_asset) sor_live =
    Authorized_Owner (secondary_owner_registry sor_owners sor_asset)"
  using authorized_owner_read_uses_the_same_committed_token_owner[OF token allowed available] registry
  by (simp add: secondary_owner_registry_def)

end

definition sor_u64 :: "integer \<Rightarrow> bool" where
  "sor_u64 sor_word \<longleftrightarrow> 0 \<le> sor_word \<and> sor_word < 18446744073709551616"

definition sor_owner_integer_abi :: "integer list list list \<Rightarrow> integer list list option" where
  "sor_owner_integer_abi sor_input =
    (if list_all (list_all (list_all sor_u64)) sor_input
     then map_option (map (map integer_of_nat)) (sor_trace (map (map (map nat_of_integer)) sor_input))
     else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      sor_mismatched_claim_refuses_before_external_crypto source_attestation.sor_authorized_registry_is_the_committed_owner
      secondary_wire_owner_keeps_the_named_registry_asset
      the_source_active_identity_is_the_existing_current_model_identity_check})
  then () else error "Unexpected oracle in signed owner read link"
\<close>

export_code sor_owner_integer_abi in SML
  module_name OIP_Signed_Owner_Read_Link file_prefix "oip_signed_owner_read_link"

end
