theory Signed_Cache_Capture_Model_Link
  imports "OIP_Query6_Capture_Export.Query6_Capture_Export"
    "OIP_Message_Code.Wire_Code_Session_Claim_Bytes"
begin

definition scc_cut where
  "scc_cut scc_epoch scc_revision =
    \<lparr>cut_authority_epoch = scc_epoch,cut_revision = scc_revision\<rparr>"

definition scc_proof where
  "scc_proof scc_session scc_epoch =
    \<lparr>proof_session = scc_session,proof_epoch = scc_epoch\<rparr>"

definition scc_scope where
  "scc_scope scc_principal scc_session scc_epoch scc_target scc_asset =
    \<lparr>q6_scope_principal = scc_principal,q6_scope_proof = scc_proof scc_session scc_epoch,
      q6_scope_target = scc_target,q6_scope_query = Application_Value scc_asset\<rparr>"

definition scc_bit :: "bool \<Rightarrow> nat" where
  "scc_bit scc_value = (if scc_value then 1 else 0)"

definition scc_exact_packet where
  "scc_exact_packet scc_bytes scc_expected_core scc_preimage scc_signature =
    (if \<not> list_all (\<lambda>scc_word. scc_word < 256)
      (scc_bytes @ scc_expected_core @ scc_preimage @ scc_signature) then None
     else Option.bind (decode_wire_packet scc_bytes) (\<lambda>scc_packet.
       let scc_core = packet_core scc_packet in
       if encode_wire_packet scc_packet = scc_bytes \<and> encode_wire_core scc_core = scc_expected_core \<and>
          envelope_signing_bytes scc_core = scc_preimage \<and> packet_signature scc_packet = scc_signature
       then Some scc_core else None))"

definition scc_run where
  "scc_run scc_core scc_current_core scc_claim scc_meta scc_expected scc_verified scc_selection
      scc_current_selection scc_current_result scc_targets scc_cache_assets scc_current_assets scc_selected_bytes =
    (case (scc_meta,scc_expected,scc_verified,scc_selection,scc_current_selection,scc_current_result) of
      ([scc_token,scc_subject_token,scc_subject,scc_active_session,scc_active_epoch,scc_active,
        scc_live_epoch,scc_available,scc_token_curve,scc_envelope_curve,scc_now,
        scc_deployment,scc_format,scc_authority],
       [scc_principal,scc_session,scc_epoch,scc_target,scc_asset],
       [scc_verified_principal,scc_verified_session,scc_verified_epoch,scc_verified_target,scc_verified_asset],
       [scc_selected_epoch,scc_selected_revision,scc_provider],
       [scc_current_epoch,scc_current_revision],
       [scc_result_epoch,scc_result_revision,scc_units]) \<Rightarrow>
       if \<not> list_all (\<lambda>scc_flag. scc_flag \<le> 1)
           [scc_active,scc_available,scc_token_curve,scc_envelope_curve] then None
       else (case (code_source_nonreceipt_read_service scc_token scc_core,
                    code_source_nonreceipt_read_service scc_token scc_current_core) of
          (Some (Service_Capture scc_token_from_core scc_capture_proof scc_capture_target (Application_Value scc_capture_asset)),
           Some (Service_Read scc_current_token scc_current_proof scc_current_target
                 (Current_Data (Application_Value scc_current_asset) scc_expected_current) None)) \<Rightarrow>
           (let scc_selector = [wire_principal scc_core,proof_session scc_capture_proof,
                 proof_epoch scc_capture_proof,scc_capture_target,scc_capture_asset];
                scc_current_selector = [wire_principal scc_current_core,proof_session scc_current_proof,
                  proof_epoch scc_current_proof,scc_current_target,scc_current_asset,
                  cut_authority_epoch scc_expected_current,cut_revision scc_expected_current];
                scc_cut_from_selection = scc_cut scc_selected_epoch scc_selected_revision;
                scc_cut_from_control = scc_cut scc_current_epoch scc_current_revision;
                scc_cut_from_result = scc_cut scc_result_epoch scc_result_revision;
                scc_request = scc_scope scc_principal scc_session scc_epoch scc_target scc_asset;
                scc_claim_matches = identity_principal (token_claim_identity scc_claim) = scc_subject \<and>
                  identity_domain (token_claim_identity scc_claim) = wire_source_domain scc_core \<and>
                  token_claim_session scc_claim = scc_active_session \<and> token_claim_epoch scc_claim = scc_active_epoch \<and>
                  token_claim_profile scc_claim = (scc_deployment,scc_format,scc_authority) \<and>
                  token_claim_issued scc_claim \<le> scc_now \<and> scc_now \<le> token_claim_expires scc_claim;
                scc_facts = \<lparr>
                  q6_authenticated_subject = (if scc_token_curve = 1 \<and> scc_claim_matches
                    then Some (scc_subject_token,scc_subject) else None),
                  q6_active_proof = (if scc_active = 1 then Some (scc_proof scc_active_session scc_active_epoch) else None),
                  q6_verified_capture = (if scc_envelope_curve = 1 then Some
                    (scc_scope scc_verified_principal scc_verified_session scc_verified_epoch scc_verified_target scc_verified_asset)
                    else None),
                  q6_registered_targets = scc_targets,q6_current_epoch = scc_live_epoch,
                  q6_authority_available = (scc_available = 1),
                  q6_cache_grants = map (scc_scope scc_principal scc_session scc_epoch scc_target) scc_cache_assets,
                  q6_current_grants = map (scc_scope scc_principal scc_session scc_epoch scc_target) scc_current_assets\<rparr>;
                scc_upstream = query6_export_upstream 0 scc_cut_from_result scc_units;
                scc_normal = query6_capture_from_core False scc_token scc_core scc_facts scc_provider scc_upstream scc_selected_bytes;
                scc_diagnostic = query6_capture_from_core True scc_token scc_core scc_facts scc_provider scc_upstream scc_selected_bytes
            in if scc_selector = scc_expected \<and> scc_token_from_core = scc_token \<and> scc_current_token = scc_token \<and>
                  scc_current_selector = scc_expected @ [scc_current_epoch,scc_current_revision] \<and>
                  scc_cut_from_selection = scc_cut_from_control \<and> scc_cut_from_control = scc_cut_from_result \<and>
                  scc_selected_epoch = scc_live_epoch
               then Some [scc_selector,encode_wire_core scc_core,scc_current_selector,encode_wire_core scc_current_core,
                    scc_selection,scc_current_result,
                    [scc_bit scc_claim_matches,scc_bit (query6_auth_matches scc_token scc_request scc_facts),
                     scc_available,scc_token_curve,scc_envelope_curve,
                     scc_bit (query6_capture_permission False scc_request scc_facts),
                     scc_bit (query6_current_permission scc_request scc_facts),
                     scc_bit (fst scc_normal = scc_selected_bytes \<and> fst scc_diagnostic = scc_selected_bytes)],
                    query6_export_reply (snd scc_normal),query6_export_reply (snd scc_diagnostic)]
               else None)
        | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"

definition scc_trace where
  "scc_trace scc_input =
    (case scc_input of
      [[scc_packet,scc_core,scc_preimage,scc_signature],
       [scc_current_packet,scc_current_core,scc_current_preimage,scc_current_signature],
       [scc_claim_bytes],[scc_meta],[scc_scope_fields],[scc_verified],[scc_selection],
       [scc_current_selection],[scc_current_result],[scc_targets],[scc_cache_assets],[scc_current_assets],
       [scc_selected_bytes]] \<Rightarrow>
        (case (scc_exact_packet scc_packet scc_core scc_preimage scc_signature,
               scc_exact_packet scc_current_packet scc_current_core scc_current_preimage scc_current_signature,
               code_decode_session_claim_preimage scc_claim_bytes) of
          (Some scc_decoded,Some scc_current_decoded,Some scc_claim) \<Rightarrow>
            scc_run scc_decoded scc_current_decoded scc_claim scc_meta scc_scope_fields scc_verified scc_selection
              scc_current_selection scc_current_result scc_targets scc_cache_assets scc_current_assets scc_selected_bytes
        | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"

definition scc_u64 :: "integer \<Rightarrow> bool" where
  "scc_u64 scc_word \<longleftrightarrow> 0 \<le> scc_word \<and> scc_word < 18446744073709551616"

definition scc_integer_abi :: "integer list list list \<Rightarrow> integer list list option" where
  "scc_integer_abi scc_input =
    (if list_all (list_all (list_all scc_u64)) scc_input then
      map_option (map (map integer_of_nat)) (scc_trace (map (map (map nat_of_integer)) scc_input))
     else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      query6_exact_capture_selector_is_reused query6_capture_is_product_pure
      query6_current_grant_alone_cannot_capture query6_g0_only_current_fallback_changes_the_current_only_case
      a_decoded_session_signature_preimage_has_the_exact_domain_and_whole_claim})
  then () else error "Unexpected oracle in signed cache capture link"
\<close>

export_code scc_integer_abi in SML
  module_name OIP_Signed_Cache_Capture_Link file_prefix "oip_signed_cache_capture_link"

end
