theory Active_Session_Grant_Link
  imports "OIP_Message_Code.Wire_Code_Session_Authentication"
    "OIP_Reference_Profile.Reference_Authority_Grants"
    "HOL-Library.Code_Target_Nat"
begin

definition asg_any_execute :: "code_source_signing_peer \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "asg_any_execute asg_peer asg_target asg_asset =
    list_ex (\<lambda>asg_entry. code_source_session_call_grant asg_peer (fst asg_entry)
      asg_target Execute_Ordinary asg_asset) (source_signing_sessions asg_peer)"

lemma asg_active_grant_has_an_any_session_witness:
  assumes asg_grant: "code_source_session_call_grant asg_peer asg_session asg_target Execute_Ordinary asg_asset"
  shows "asg_any_execute asg_peer asg_target asg_asset"
proof -
  obtain asg_endpoints where asg_map:
    "map_of (source_signing_sessions asg_peer) asg_session = Some asg_endpoints"
    using asg_grant by (auto elim: a_source_call_grant_is_for_the_exact_session_target_and_asset)
  have asg_member: "(asg_session, asg_endpoints) \<in> set (source_signing_sessions asg_peer)"
    by (rule map_of_SomeD[OF asg_map])
  have asg_exists: "\<exists>asg_entry\<in>set (source_signing_sessions asg_peer).
      code_source_session_call_grant asg_peer (fst asg_entry) asg_target Execute_Ordinary asg_asset"
  proof (rule bexI[where x = "(asg_session, asg_endpoints)"])
    show "code_source_session_call_grant asg_peer (fst (asg_session, asg_endpoints))
      asg_target Execute_Ordinary asg_asset"
      using asg_grant by simp
    show "(asg_session, asg_endpoints) \<in> set (source_signing_sessions asg_peer)"
      by (rule asg_member)
  qed
  from asg_exists show ?thesis by (simp add: asg_any_execute_def list_ex_iff)
qed

definition asg_reserve_reference_inputs where
  "asg_reserve_reference_inputs asg_peer asg_session asg_asset asg_epoch asg_actor =
    \<lparr>reference_epoch = asg_epoch, reference_grants = (\<lambda>asg_endpoint.
      if code_source_session_call_grant asg_peer asg_session asg_endpoint Execute_Ordinary asg_asset
      then {(asg_actor, Adapter_Lock_Entry, Ref_Reserve)} else {})\<rparr>"

lemma asg_one_session_projects_to_the_reference_reserve_grant:
  "reference_permitted_at (asg_reserve_reference_inputs asg_peer asg_session asg_asset asg_epoch asg_actor)
      Adapter_Lock_Entry asg_actor
      (Client_Protocol asg_target asg_index (Reserve_Intent asg_request asg_versions asg_duration)) =
    code_source_session_call_grant asg_peer asg_session asg_target Execute_Ordinary asg_asset"
  by (simp add: reference_permitted_at_def asg_reserve_reference_inputs_def)

definition asg_materialized_words :: "code_source_action_request \<Rightarrow> nat list option" where
  "asg_materialized_words asg_request =
    (case source_request_action asg_request of Code_Source_Ordinary_Action asg_payload \<Rightarrow>
      (case source_payload_command asg_payload of Wire_Reserve asg_duration \<Rightarrow>
        (let asg_binding = source_payload_binding asg_payload;
             asg_cut = source_payload_cut asg_payload;
             asg_versions = source_payload_versions asg_payload
         in if source_payload_credential asg_payload = None then
           Some ([fst (source_request_id asg_request), snd (source_request_id asg_request),
             source_payload_message asg_payload, source_payload_origin_epoch asg_payload,
             source_payload_endpoint asg_payload, source_payload_caller asg_payload,
             source_payload_session asg_payload, cut_authority_epoch asg_cut, cut_revision asg_cut,
             fst (source_binding_origin asg_binding), snd (source_binding_origin asg_binding),
             source_binding_asset asg_binding, source_binding_owner asg_binding,
             source_binding_destination asg_binding, source_binding_recipient asg_binding,
             source_binding_amount asg_binding, length asg_versions] @
             concat (map (\<lambda>(asg_id, asg_version). [asg_id, asg_version]) asg_versions) @ [asg_duration])
         else None)
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"

definition asg_bit :: "bool \<Rightarrow> nat" where
  "asg_bit asg_value = (if asg_value then 1 else 0)"

definition asg_observe where
  "asg_observe asg_observed asg_signing asg_peer asg_authenticate asg_curve asg_packet asg_proof asg_request =
    (let asg_identity = source_signing_identity asg_peer;
         asg_target = source_request_target asg_request;
         asg_asset = source_binding_asset (source_payload_binding (code_source_action_payload (source_request_action asg_request)));
         asg_policy = (\<lambda>asg_who asg_endpoint asg_requested_asset asg_operation asg_epoch.
            asg_who = asg_identity \<and> asg_epoch = source_signing_epoch asg_signing \<and>
            asg_operation = Execute_Ordinary \<and> asg_any_execute asg_peer asg_endpoint asg_requested_asset);
         asg_verify = (\<lambda>asg_who asg_current_proof asg_endpoint asg_operation asg_call_id asg_action.
           code_verify_source_no_proof_call asg_signing asg_curve asg_packet asg_who asg_current_proof
             asg_endpoint asg_operation asg_call_id asg_action = Code_Source_Call_Verified)
     in map asg_bit [
       asg_authenticate () asg_proof = Some asg_identity,
       code_source_active_identity asg_authenticate () asg_proof asg_observed = Some asg_identity,
       asg_policy asg_identity asg_target asg_asset Execute_Ordinary (proof_epoch asg_proof),
       code_source_authorize_call asg_authenticate asg_policy (\<lambda>_ _ _ _ _ _. True)
         () asg_proof asg_request Execute_Ordinary asg_observed = Some asg_identity,
       code_source_session_call_grant asg_peer (proof_session asg_proof) asg_target Execute_Ordinary asg_asset,
       code_source_authorize_call asg_authenticate asg_policy asg_verify
         () asg_proof asg_request Execute_Ordinary asg_observed = Some asg_identity])"

definition asg_run :: "nat list list \<Rightarrow> nat list option" where
  "asg_run asg_rows =
    (case asg_rows of [[asg_deployment, asg_format, asg_profile, asg_epoch, asg_max_seconds,
       asg_max_frame, asg_max_nesting, asg_route_scope],
      [asg_now, asg_target, asg_proof_session, asg_selected_epoch, asg_selected_revision],
      [asg_principal, asg_domain, asg_ocid, asg_rai, asg_key_id],
      [asg_dir_principal, asg_dir_domain, asg_dir_ocid, asg_dir_rai],
      [asg_ledger_session, asg_ledger_principal, asg_ledger_epoch],
      asg_typed, asg_endpoints, asg_targets, asg_caller_key, asg_issuer,
      asg_packet, asg_original_core, asg_caller_preimage, asg_caller_signature,
      asg_token_preimage, asg_token_signature, [asg_caller_valid, asg_token_valid],
      [asg_session1, asg_endpoint1], asg_execute1, asg_receipts1, asg_json1, asg_digest1,
      [asg_session2, asg_endpoint2], asg_execute2, asg_receipts2, asg_json2, asg_digest2] \<Rightarrow>
    (case decode_wire_packet asg_packet of None \<Rightarrow> None | Some asg_wire_packet \<Rightarrow>
      (let asg_core = packet_core asg_wire_packet in
       if encode_wire_core asg_core \<noteq> asg_original_core \<or>
          envelope_signing_bytes asg_core \<noteq> asg_caller_preimage \<or>
          packet_signature asg_wire_packet \<noteq> asg_caller_signature then None
       else
         (case code_materialize_source_call asg_target asg_core of Inr (Some asg_request) \<Rightarrow>
           (if asg_materialized_words asg_request \<noteq> Some asg_typed then None
            else
              (let asg_identity = \<lparr>identity_principal = asg_principal, identity_domain = asg_domain,
                     identity_ocid = asg_ocid, identity_rai = asg_rai\<rparr>;
                   asg_directory = \<lparr>identity_principal = asg_dir_principal, identity_domain = asg_dir_domain,
                     identity_ocid = asg_dir_ocid, identity_rai = asg_dir_rai\<rparr>;
                   asg_proof = \<lparr>proof_session = asg_proof_session, proof_epoch = asg_selected_epoch\<rparr>;
                   asg_observed = \<lparr>
                     source_identity_cut = \<lparr>cut_authority_epoch = asg_selected_epoch, cut_revision = asg_selected_revision\<rparr>,
                     source_identity_directory = (\<lambda>asg_id. if asg_id = asg_dir_principal then Some asg_directory else None),
                     source_identity_sessions = (\<lambda>asg_id. if asg_id = asg_ledger_session then Some
                       \<lparr>session_principal = asg_ledger_principal, session_epoch = asg_ledger_epoch\<rparr> else None),
                     source_identity_endpoints = set asg_endpoints\<rparr>;
                   asg_grant1 = \<lparr>source_call_execute_assets = set asg_execute1, source_call_receipt_assets = set asg_receipts1\<rparr>;
                   asg_grant2 = \<lparr>source_call_execute_assets = set asg_execute2, source_call_receipt_assets = set asg_receipts2\<rparr>;
                   asg_peer = \<lparr>source_signing_identity = asg_identity, source_signing_key_number = asg_key_id,
                     source_signing_public_key = asg_caller_key, source_signing_sessions =
                     [(asg_session1, [(asg_endpoint1, asg_grant1)]), (asg_session2, [(asg_endpoint2, asg_grant2)])]\<rparr>;
                   asg_signing = \<lparr>source_signing_deployment = asg_deployment, source_signing_epoch = asg_epoch,
                     source_signing_targets = set asg_targets, source_signing_route_scope = asg_route_scope,
                     source_signing_max_frame = asg_max_frame, source_signing_max_nesting = asg_max_nesting,
                     source_signing_peers = [(asg_principal, asg_peer)]\<rparr>;
                   asg_session_config = \<lparr>source_session_profile = (asg_deployment, asg_format, asg_profile),
                     source_session_epoch = asg_epoch, source_session_issuer = asg_issuer,
                     source_session_max_seconds = asg_max_seconds, source_session_peers =
                     [(asg_principal, \<lparr>source_session_identity = asg_identity,
                        source_session_serialized_grants = [(asg_session1, asg_json1), (asg_session2, asg_json2)]\<rparr>)]\<rparr>;
                   asg_hash = (\<lambda>asg_preimage. if asg_preimage = code_session_grants_domain @ asg_json1 then asg_digest1
                     else if asg_preimage = code_session_grants_domain @ asg_json2 then asg_digest2 else []);
                   asg_curve = (\<lambda>asg_key asg_preimage asg_sig.
                     (asg_caller_valid = 1 \<and> asg_key = asg_caller_key \<and>
                       asg_preimage = asg_caller_preimage \<and> asg_sig = asg_caller_signature) \<or>
                     (asg_token_valid = 1 \<and> asg_key = asg_issuer \<and>
                       asg_preimage = asg_token_preimage \<and> asg_sig = asg_token_signature));
                   asg_authenticate = (\<lambda>_ asg_current_proof. code_source_authenticate_session_bytes
                     asg_session_config asg_hash asg_curve asg_token_preimage asg_token_signature
                     asg_current_proof (Some asg_now))
               in Some (asg_observe asg_observed asg_signing asg_peer asg_authenticate
                 asg_curve asg_packet asg_proof asg_request)))
         | _ \<Rightarrow> None)))
    | _ \<Rightarrow> None)"

definition asg_submit_integer :: "integer list list \<Rightarrow> integer list option" where
  "asg_submit_integer asg_rows =
    (if list_all (list_all (\<lambda>asg_word. 0 \<le> asg_word)) asg_rows
     then map_option (map integer_of_nat) (asg_run (map (map nat_of_integer) asg_rows))
     else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms asg_active_grant_has_an_any_session_witness
      asg_one_session_projects_to_the_reference_reserve_grant
      source_session_authentication_keeps_the_current_record_grants_time_and_curve_inputs
      a_verified_source_no_proof_call_consumes_the_original_packet_and_whole_payload})
  then () else error "Unexpected oracle in active session grant link"
\<close>

export_code asg_submit_integer in SML module_name OIP_Active_Session_Grant_ABI
  file_prefix oip_active_session_grant

end
