theory Resolver_Current_Control_ABI
  imports Resolver_Current_Control_Link
begin

fun rcc_parse_saved :: "nat list list \<Rightarrow> (client_call_id \<times> (code_source_call_payload \<times> code_source_outcome)) option" where
  "rcc_parse_saved [rcc_id,[rcc_msg,rcc_oe,rcc_endpoint,rcc_caller,rcc_s,rcc_ce,rcc_cr,rcc_cmd,rcc_arg],
       rcc_binding_words,rcc_credential_words,rcc_version_words,rcc_outcome_words] =
    (if rcc_cmd = 3 then
       (case (rdw_id rcc_id,rdw_parse_cut [rcc_ce,rcc_cr],rdw_parse_binding rcc_binding_words,
          rdw_parse_credential rcc_credential_words,rdw_parse_versions rcc_version_words,rcc_outcome_words) of
          (Some rcc_call,Some rcc_cut_value,Some rcc_binding,Some rcc_credential,Some rcc_versions,[rcc_code,rcc_position]) \<Rightarrow>
            if rcc_code = 3 then Some (rcc_call,(
              \<lparr>source_payload_message = rcc_msg,source_payload_origin_epoch = rcc_oe,source_payload_endpoint = rcc_endpoint,
                 source_payload_caller = rcc_caller,source_payload_session = rcc_s,source_payload_cut = rcc_cut_value,
                 source_payload_binding = rcc_binding,source_payload_credential = rcc_credential,
                 source_payload_versions = rcc_versions,source_payload_command = Wire_Debit rcc_arg\<rparr>,
              \<lparr>source_outcome_reply = Code_Source_Accepted Code_Source_Debited_Reply,source_outcome_commit = Some rcc_position\<rparr>))
            else None
        | _ \<Rightarrow> None)
     else rdw_parse_saved [rcc_id,[rcc_msg,rcc_oe,rcc_endpoint,rcc_caller,rcc_s,rcc_ce,rcc_cr,rcc_cmd,rcc_arg],
       rcc_binding_words,rcc_credential_words,rcc_version_words,rcc_outcome_words])"
| "rcc_parse_saved _ = None"

fun rcc_member_row :: "nat list \<Rightarrow> (nat \<times> wire_bytes) option" where
  "rcc_member_row (rcc_id # rcc_key) = (if length rcc_key = 32 then Some (rcc_id,rcc_key) else None)"
| "rcc_member_row _ = None"

fun rcc_curve_row :: "nat list list \<Rightarrow> (wire_bytes \<times> wire_bytes \<times> wire_bytes \<times> bool) option" where
  "rcc_curve_row [rcc_key,rcc_message,rcc_signature] = Some (rcc_key,rcc_message,rcc_signature,True)"
| "rcc_curve_row _ = None"

definition rcc_directory_row where
  "rcc_directory_row rcc_row =
     map_option (\<lambda>rcc_identity. (identity_principal rcc_identity,rcc_identity)) (rdw_parse_identity rcc_row)"

fun rcc_session_row where
  "rcc_session_row [rcc_sid,rcc_principal,rcc_epoch] =
    Some (rcc_sid,\<lparr>session_principal = rcc_principal,session_epoch = rcc_epoch\<rparr>)"
| "rcc_session_row _ = None"

fun rcc_make_context where
  "rcc_make_context rcc_cut_value
    [[rcc_dep,rcc_fmt,rcc_authority,rcc_epoch,rcc_max_token,rcc_route,rcc_frame,rcc_floor,rcc_skew,rcc_peer_key_id,
       rcc_endpoint,rcc_host,rcc_resolution,rcc_token_sid,rcc_group,rcc_quorum],
     [rcc_version,rcc_channel_dep,rcc_local,rcc_remote,rcc_expires],rcc_identity_words,rcc_peer_key,rcc_issuer,
      rcc_token_pre,rcc_token_sig,rcc_grants,rcc_execute,rcc_receipts,rcc_family_codes,rcc_atomicities,rcc_schemes,
      rcc_response_key,rcc_channel_local_key,rcc_channel_remote_key,rcc_policy_preimage,rcc_policy_digest]
    [rcc_directory,rcc_sessions,[rcc_endpoints]] rcc_members rcc_good_keys rcc_curves =
    (case (rdw_parse_identity rcc_identity_words,rdw_collect rcc_directory_row rcc_directory,
       rdw_collect rcc_session_row rcc_sessions,rdw_collect family_at_number rcc_family_codes,
       rdw_collect rcc_member_row rcc_members,rdw_collect rcc_curve_row rcc_curves) of
      (Some rcc_id_value,Some rcc_ids,Some rcc_ss,Some rcc_families,Some rcc_members_value,Some rcc_facts) \<Rightarrow>
       let rcc_snapshot_value = \<lparr>source_identity_cut = rcc_cut_value,source_identity_directory = map_of rcc_ids,
             source_identity_sessions = map_of rcc_ss,source_identity_endpoints = set rcc_endpoints\<rparr>;
           rcc_grant = \<lparr>source_call_execute_assets = set rcc_execute,source_call_receipt_assets = set rcc_receipts\<rparr>;
           rcc_peer = \<lparr>source_signing_identity = rcc_id_value,source_signing_key_number = rcc_peer_key_id,
             source_signing_public_key = rcc_peer_key,source_signing_sessions = [(rcc_token_sid,[(rcc_endpoint,rcc_grant)])]\<rparr>;
           rcc_auth = \<lparr>source_session_profile = (rcc_dep,rcc_fmt,rcc_authority),source_session_epoch = rcc_epoch,
             source_session_issuer = rcc_issuer,source_session_max_seconds = rcc_max_token,
             source_session_peers = [(identity_principal rcc_id_value,\<lparr>source_session_identity = rcc_id_value,
                source_session_serialized_grants = [(rcc_token_sid,rcc_grants)]\<rparr>)]\<rparr>;
           rcc_profile = \<lparr>negotiated_version = rcc_version,negotiated_families = set rcc_families,
             negotiated_atomicities = set rcc_atomicities,negotiated_schemes = set rcc_schemes\<rparr>;
           rcc_boundary = \<lparr>boundary_profile = rcc_profile,boundary_deployment = rcc_dep,boundary_source = rcc_remote,
             boundary_target = rcc_local,boundary_principal = identity_principal rcc_id_value,boundary_key = rcc_group,
             boundary_epoch = rcc_epoch,boundary_route_scope = rcc_route,boundary_now = rcc_host,
             boundary_asset_ttl_floor = rcc_floor,boundary_future_skew = rcc_skew,boundary_max_frame = rcc_frame,
             boundary_version_floor = 6,boundary_critical_allowed = False,boundary_threshold_supported = True\<rparr>;
           rcc_channel_value = \<lparr>guard_channel_version = rcc_version,guard_channel_deployment = rcc_channel_dep,
             guard_channel_local = rcc_local,guard_channel_remote = rcc_remote,guard_channel_expires = rcc_expires,
             guard_channel_peer_key = rcc_channel_remote_key,
             guard_channel_current = (rcc_version = 6 \<and> rcc_channel_dep = rcc_dep \<and> rcc_local = rcc_endpoint \<and>
                 rcc_response_key = rcc_channel_local_key \<and> rcc_peer_key = rcc_channel_remote_key \<and> identity_domain rcc_id_value = rcc_remote)\<rparr>;
           rcc_current_roster = [rcc_dep,rcc_remote,identity_principal rcc_id_value,rcc_group,rcc_epoch]
       in if cut_authority_epoch rcc_cut_value = rcc_epoch
          then Some \<lparr>rcc_session_config = rcc_auth,rcc_identity_snapshot = rcc_snapshot_value,rcc_signing_peer = rcc_peer,
             rcc_scope = rcc_boundary,rcc_channel = rcc_channel_value,
             rcc_registry = p19_export_registry rcc_current_roster (rcc_current_roster @ [rcc_quorum]) rcc_members_value,
             rcc_key_checks = map (\<lambda>rcc_k. (rcc_k,True)) rcc_good_keys,rcc_strict_checks = rcc_facts,
             rcc_token_preimage = rcc_token_pre,rcc_token_signature = rcc_token_sig,rcc_host_clock = rcc_host,
             rcc_resolution_clock = rcc_resolution,rcc_security_preimage = rcc_policy_preimage,rcc_security_digest = rcc_policy_digest\<rparr>
          else None
     | _ \<Rightarrow> None)"
| "rcc_make_context _ _ _ _ _ _ = None"

definition rcc_nat_abi ::
  "nat list list \<Rightarrow> nat list list list list \<Rightarrow> nat list list \<Rightarrow> nat list list list \<Rightarrow>
   nat list list \<Rightarrow> nat list list \<Rightarrow> nat list list list \<Rightarrow> nat list list list \<Rightarrow>
   nat list list \<Rightarrow> nat list list" where
  "rcc_nat_abi rcc_header rcc_tables rcc_config rcc_identity_tables rcc_members rcc_keys rcc_curves rcc_hashes rcc_late =
    (case (rcc_header,rcc_tables) of
      ([[rcc_mod,rcc_writer,rcc_expected,rcc_size],rcc_profile,rcc_address,rcc_head_digest,rcc_record_header,
         rcc_parent,rcc_parent_digest,rcc_selected_cut,rcc_control_raw,rcc_control_canon,rcc_control_digest,
         rcc_raw_record,rcc_record_canon,rcc_packet_raw,rcc_core_raw],
       [[[rcc_revoked_rows]],rcc_cancelled,rcc_decisions,rcc_latest,rcc_calls,rcc_bindings,[rcc_claimed]]) \<Rightarrow>
       (case (rdw_make_profile rcc_profile,rdw_make_address rcc_address rcc_head_digest,
          rdw_parse_fields [rcc_record_header,rcc_parent,rcc_parent_digest],rdw_parse_cut rcc_selected_cut,
          rdw_collect rdw_parse_transport rcc_cancelled,rdw_collect rdw_parse_decision rcc_decisions,
          rdw_collect rdw_parse_latest rcc_latest,rdw_collect rcc_parse_saved rcc_calls,
          rdw_collect rdw_parse_transport_binding rcc_bindings,rdw_collect rdw_id rcc_claimed,
          rdw_collect rdw_parse_hash rcc_hashes) of
         (Some rcc_cfg,Some rcc_head,Some rcc_hdr,Some rcc_cut_value,Some rcc_cancel_rows,
          Some rcc_decision_rows,Some rcc_latest_rows,Some rcc_call_rows,Some rcc_binding_rows,Some rcc_claim_rows,Some rcc_digest_rows) \<Rightarrow>
          (case rcc_make_context rcc_cut_value rcc_config rcc_identity_tables rcc_members rcc_keys rcc_curves of None \<Rightarrow> [[0]]
           | Some rcc_context_value \<Rightarrow>
             let rcc_control_view = \<lparr>source_control_stored = (rcc_mod,rcc_control_raw),source_control_revoked = rcc_revoked_rows,
                  source_control_cancelled = rcc_cancel_rows,source_control_decisions = rcc_decision_rows,source_control_latest = rcc_latest_rows\<rparr>;
                 rcc_view = \<lparr>rdw_observation = rcc_control_view,rdw_head = rcc_head,rdw_control_profile = rcc_cfg,
                   rdw_control_writer = rcc_writer,rdw_expected_writer = rcc_expected,rdw_control_canonical = rcc_control_canon,
                   rdw_control_sha = rcc_control_digest,rdw_file_size = rcc_size,rdw_record_bytes = rcc_raw_record,
                   rdw_record_canonical = rcc_record_canon,rdw_record_header = rcc_hdr,rdw_cut = rcc_cut_value,
                   rdw_ordinary_calls = rcc_call_rows,rdw_transport_bindings = rcc_binding_rows,rdw_other_claims = rcc_claim_rows\<rparr>
             in rcc_run rcc_context_value (map_of rcc_digest_rows) rcc_view rcc_packet_raw rcc_core_raw rcc_late)
       | _ \<Rightarrow> [[0]])
      | _ \<Rightarrow> [[0]])"

definition rcc_integer_word :: "integer \<Rightarrow> bool" where
  "rcc_integer_word rcc_n \<longleftrightarrow> 0 \<le> rcc_n \<and> rcc_n < 18446744073709551616"

definition rcc_integer_rows where
  "rcc_integer_rows rcc_rows \<longleftrightarrow> list_all (list_all rcc_integer_word) rcc_rows"

definition rcc_integer_abi ::
  "integer list list \<Rightarrow> integer list list list list \<Rightarrow> integer list list \<Rightarrow> integer list list list \<Rightarrow>
   integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list list \<Rightarrow> integer list list list \<Rightarrow>
   integer list list \<Rightarrow> integer list list" where
  "rcc_integer_abi rcc_header rcc_tables rcc_config rcc_identity_tables rcc_members rcc_keys rcc_curves rcc_hashes rcc_late =
    (if list_all rcc_integer_rows [rcc_header,rcc_config,rcc_members,rcc_keys,rcc_late] \<and>
        list_all (list_all rcc_integer_rows) [rcc_identity_tables,rcc_curves,rcc_hashes] \<and>
        list_all (list_all rcc_integer_rows) rcc_tables
     then map (map integer_of_nat) (rcc_nat_abi (map (map nat_of_integer) rcc_header)
       (map (map (map (map nat_of_integer))) rcc_tables) (map (map nat_of_integer) rcc_config)
       (map (map (map nat_of_integer)) rcc_identity_tables) (map (map nat_of_integer) rcc_members)
       (map (map nat_of_integer) rcc_keys) (map (map (map nat_of_integer)) rcc_curves)
       (map (map (map nat_of_integer)) rcc_hashes) (map (map nat_of_integer) rcc_late))
     else [[0]])"

export_code rcc_integer_abi in SML
  module_name OIP_Resolver_Current_Control_ABI file_prefix "oip_resolver_current_control_abi"

end
