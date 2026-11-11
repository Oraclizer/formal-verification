theory Publication_Endorser_ABI
  imports Publication_Endorser_Link
begin

fun pea_pair :: "nat list \<Rightarrow> (nat \<times> nat) option" where
  "pea_pair [pea_a,pea_b] = Some (pea_a,pea_b)"
| "pea_pair _ = None"

definition pea_directory_row where
  "pea_directory_row pea_row =
    map_option (\<lambda>pea_identity. (identity_principal pea_identity,pea_identity)) (rdw_parse_identity pea_row)"

fun pea_session_row :: "nat list \<Rightarrow> (nat \<times> product_session_binding) option" where
  "pea_session_row [pea_session,pea_principal,pea_epoch] =
     Some (pea_session,\<lparr>session_principal = pea_principal,session_epoch = pea_epoch\<rparr>)"
| "pea_session_row _ = None"

fun pea_parse_snapshot ::
  "nat list list list \<Rightarrow> (code_source_identity_snapshot \<times> (nat \<times> nat) list \<times>
    code_source_binding \<times> nat list) option" where
  "pea_parse_snapshot [[pea_cut_input],pea_directory,pea_sessions,[pea_endpoints],pea_owners,[pea_binding_words],[pea_revoked_input]] =
    (case (rdw_parse_cut pea_cut_input,rdw_collect pea_directory_row pea_directory,
        rdw_collect pea_session_row pea_sessions,rdw_collect pea_pair pea_owners,rdw_parse_binding pea_binding_words) of
        (Some pea_live,Some pea_ids,Some pea_ss,Some pea_owner_rows,Some pea_binding) \<Rightarrow>
          Some (\<lparr>source_identity_cut = pea_live,source_identity_directory = map_of pea_ids,
            source_identity_sessions = map_of pea_ss,source_identity_endpoints = set pea_endpoints\<rparr>,
            pea_owner_rows,pea_binding,pea_revoked_input)
      | _ \<Rightarrow> None)"
| "pea_parse_snapshot _ = None"

fun pea_parse_wire where
  "pea_parse_wire [pea_packet_raw,pea_credential_raw,pea_core_bytes,pea_preimage,pea_signature,pea_cert,
    pea_worker_pre,pea_worker_sig,pea_owner_pre,pea_owner_sig,pea_endorse_pre,pea_endorse_sig] =
    Some \<lparr>pea_packet = pea_packet_raw,pea_credential_packet = pea_credential_raw,pea_expected_core = pea_core_bytes,
      pea_envelope_preimage = pea_preimage,pea_envelope_signature = pea_signature,pea_certificate = pea_cert,
      pea_worker_preimage = pea_worker_pre,pea_worker_signature = pea_worker_sig,
      pea_owner_preimage = pea_owner_pre,pea_owner_signature = pea_owner_sig,
      pea_endorsement_preimage = pea_endorse_pre,pea_endorsement_signature = pea_endorse_sig\<rparr>"
| "pea_parse_wire _ = None"

fun pea_parse_context where
  "pea_parse_context pea_live pea_owner_rows pea_binding pea_revoked_rows
    [[pea_dep,pea_fmt,pea_authority,pea_epoch,pea_max_token,pea_route,pea_frame,pea_floor,pea_skew,pea_key_id,pea_endpoint],
     [pea_version,pea_channel_dep,pea_local,pea_remote,pea_expires],
     pea_worker_id,pea_owner_id,pea_worker_key,pea_owner_key,pea_issuer,pea_response_key,pea_local_key,pea_remote_key,
     [pea_worker_sid,pea_owner_sid,pea_owner_epoch],pea_worker_grants,pea_owner_grants,
     pea_execute_assets,pea_receipt_assets,pea_recovery_assets,pea_family_numbers,pea_atomicities,pea_schemes] =
    (case (rdw_parse_identity pea_worker_id,rdw_parse_identity pea_owner_id,rdw_collect family_at_number pea_family_numbers) of
       (Some pea_worker,Some pea_owner,Some pea_families) \<Rightarrow>
         let pea_grant = \<lparr>source_call_execute_assets = set pea_execute_assets,source_call_receipt_assets = set pea_receipt_assets\<rparr>;
             pea_peer = \<lparr>source_signing_identity = pea_worker,source_signing_key_number = pea_key_id,
                source_signing_public_key = pea_worker_key,source_signing_sessions = [(pea_worker_sid,[(pea_endpoint,pea_grant)])]\<rparr>;
             pea_token_config = \<lparr>source_session_profile = (pea_dep,pea_fmt,pea_authority),source_session_epoch = pea_epoch,
                source_session_issuer = pea_issuer,source_session_max_seconds = pea_max_token,
                source_session_peers = [
                  (identity_principal pea_worker,\<lparr>source_session_identity = pea_worker,
                     source_session_serialized_grants = [(pea_worker_sid,pea_worker_grants)]\<rparr>),
                  (identity_principal pea_owner,\<lparr>source_session_identity = pea_owner,
                     source_session_serialized_grants = [(pea_owner_sid,pea_owner_grants)]\<rparr>)]\<rparr>;
             pea_profile = \<lparr>negotiated_version = pea_version,negotiated_families = set pea_families,
                negotiated_atomicities = set pea_atomicities,negotiated_schemes = set pea_schemes\<rparr>;
             pea_current = (pea_version = 6 \<and> pea_channel_dep = pea_dep \<and> pea_local = pea_endpoint \<and>
                pea_local_key = pea_response_key \<and> pea_remote = identity_domain pea_worker \<and> pea_remote_key = pea_worker_key);
             pea_guard = \<lparr>guard_channel_version = pea_version,guard_channel_deployment = pea_channel_dep,
                guard_channel_local = pea_local,guard_channel_remote = pea_remote,guard_channel_expires = pea_expires,
                guard_channel_peer_key = pea_remote_key,guard_channel_current = pea_current\<rparr>;
             pea_scope = \<lparr>boundary_profile = pea_profile,boundary_deployment = pea_dep,boundary_source = pea_remote,
                boundary_target = pea_local,boundary_principal = identity_principal pea_worker,boundary_key = pea_key_id,
                boundary_epoch = pea_epoch,boundary_route_scope = pea_route,boundary_now = 0,boundary_asset_ttl_floor = pea_floor,
                boundary_future_skew = pea_skew,boundary_max_frame = pea_frame,boundary_version_floor = 6,
                boundary_critical_allowed = False,boundary_threshold_supported = False\<rparr>
         in if pea_epoch = cut_authority_epoch (source_identity_cut pea_live)
            then Some \<lparr>pea_session_config = pea_token_config,pea_snapshot = pea_live,pea_worker_peer = pea_peer,
                pea_owner_public_key = pea_owner_key,pea_owner_recovery_assets = pea_recovery_assets,
                pea_owner_registry = pea_owner_rows,pea_recorded_binding = pea_binding,pea_revoked = pea_revoked_rows,
                pea_owner_proof = \<lparr>proof_session = pea_owner_sid,proof_epoch = pea_owner_epoch\<rparr>,
                pea_channel = pea_guard,pea_boundary = pea_scope\<rparr>
            else None
     | _ \<Rightarrow> None)"
| "pea_parse_context _ _ _ _ _ = None"

fun pea_clock_case where
  "pea_clock_case pea_context pea_hash pea_verify pea_wire [pea_admitted,pea_tick] =
     pea_trace pea_context pea_hash pea_verify pea_wire pea_admitted pea_tick"
| "pea_clock_case _ _ _ _ _ = [[0]]"

definition pea_nat_abi ::
  "nat list list \<Rightarrow> nat list list \<Rightarrow> nat list list \<Rightarrow> nat list list list \<Rightarrow>
    nat list list list \<Rightarrow> nat list list list \<Rightarrow> nat list list \<Rightarrow> nat list list list" where
  "pea_nat_abi pea_raw pea_policy pea_wire_rows pea_snapshot_rows pea_hash_rows pea_crypto_facts pea_clocks =
    (case pea_raw of [[pea_mod,pea_file_len],pea_control_raw,pea_control_sha,pea_record,pea_head_words,pea_head_sha,
         pea_config_raw,pea_policy_sha] \<Rightarrow>
       (case (rdw_make_address pea_head_words pea_head_sha,rdw_collect rdw_parse_hash pea_hash_rows,
             pea_parse_wire pea_wire_rows,pea_parse_snapshot pea_snapshot_rows) of
          (Some pea_head,Some pea_digests,Some pea_wire,Some (pea_live,pea_owners,pea_binding,pea_revoked_rows)) \<Rightarrow>
            let pea_hash = map_of pea_digests in
            if pea_exact_before pea_hash (pea_mod,pea_control_raw) pea_control_sha pea_record pea_head pea_file_len
                  pea_config_raw pea_policy_sha
            then (case pea_parse_context pea_live pea_owners pea_binding pea_revoked_rows pea_policy of None \<Rightarrow> [[[0]]]
              | Some pea_context \<Rightarrow> map (pea_clock_case pea_context pea_hash
                    (\<lambda>pea_key pea_msg pea_sig. List.member pea_crypto_facts [pea_key,pea_msg,pea_sig]) pea_wire) pea_clocks)
            else [[[0]]]
        | _ \<Rightarrow> [[[0]]])
      | _ \<Rightarrow> [[[0]]])"

definition pea_integer_word :: "integer \<Rightarrow> bool" where
  "pea_integer_word pea_word \<longleftrightarrow> 0 \<le> pea_word \<and> pea_word < 18446744073709551616"

definition pea_integer_rows where
  "pea_integer_rows pea_rows \<longleftrightarrow> list_all (list_all pea_integer_word) pea_rows"

definition pea_integer_abi ::
  "integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list list \<Rightarrow>
    integer list list list \<Rightarrow> integer list list list \<Rightarrow> integer list list \<Rightarrow> integer list list list" where
  "pea_integer_abi pea_raw pea_policy pea_wire_rows pea_snapshot_rows pea_hash_rows pea_crypto_facts pea_clocks =
    (if list_all pea_integer_rows [pea_raw,pea_policy,pea_wire_rows,pea_clocks] \<and>
        list_all (list_all pea_integer_rows) [pea_snapshot_rows,pea_hash_rows,pea_crypto_facts]
     then map (map (map integer_of_nat))
       (pea_nat_abi (map (map nat_of_integer) pea_raw) (map (map nat_of_integer) pea_policy)
          (map (map nat_of_integer) pea_wire_rows) (map (map (map nat_of_integer)) pea_snapshot_rows)
          (map (map (map nat_of_integer)) pea_hash_rows) (map (map (map nat_of_integer)) pea_crypto_facts)
          (map (map nat_of_integer) pea_clocks))
     else [[[0]]])"

export_code pea_integer_abi in SML
  module_name OIP_Publication_Endorser_ABI file_prefix "oip_publication_endorser_abi"

end
