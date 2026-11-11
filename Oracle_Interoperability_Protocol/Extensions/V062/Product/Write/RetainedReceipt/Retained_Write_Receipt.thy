theory Retained_Write_Receipt
  imports "OIP_Signed_Write_Reopen_Link.Signed_Write_Reopen_Link"
    "OIP_Active_Session_Grant_Link.Active_Session_Grant_Link"
begin

definition rwr_active_policy where
  "rwr_active_policy rwr_peer rwr_proof rwr_config_epoch rwr_who rwr_target rwr_asset rwr_operation rwr_epoch \<longleftrightarrow>
    rwr_who = source_signing_identity rwr_peer \<and> rwr_epoch = proof_epoch rwr_proof \<and> rwr_epoch = rwr_config_epoch \<and>
    code_source_session_call_grant rwr_peer (proof_session rwr_proof) rwr_target rwr_operation rwr_asset"

definition rwr_write_words :: "code_source_call_payload \<Rightarrow> nat list option" where
  "rwr_write_words rwr_payload =
    (case (source_payload_command rwr_payload,source_payload_credential rwr_payload) of
      (Wire_Write rwr_generation rwr_value,Some credential) \<Rightarrow>
        (let rwr_binding = source_payload_binding rwr_payload; rwr_cut = source_payload_cut rwr_payload;
             rwr_tok = credential_token credential; rwr_versions = source_payload_versions rwr_payload in
          Some ([source_payload_message rwr_payload,source_payload_origin_epoch rwr_payload,
             source_payload_endpoint rwr_payload,source_payload_caller rwr_payload,source_payload_session rwr_payload,
             cut_authority_epoch rwr_cut,cut_revision rwr_cut,
             fst (source_binding_origin rwr_binding),snd (source_binding_origin rwr_binding),
             source_binding_asset rwr_binding,source_binding_owner rwr_binding,source_binding_destination rwr_binding,
             source_binding_recipient rwr_binding,source_binding_amount rwr_binding,
             token_asset rwr_tok,token_owner rwr_tok,token_generation rwr_tok,credential_epoch credential,
             fst (credential_origin credential),snd (credential_origin credential),length rwr_versions] @
             concat (map (\<lambda>(rwr_asset,rwr_version). [rwr_asset,rwr_version]) rwr_versions) @ [rwr_generation,rwr_value]))
      | _ \<Rightarrow> None)"

datatype rwr_result = RWR_Product_Rejected | RWR_Unavailable | RWR_Outside_Completed_Write | RWR_Retained nat

definition rwr_retain where
  "rwr_retain rwr_peer rwr_proof rwr_config_epoch rwr_target rwr_payload rwr_admitted rwr_available rwr_stored =
    (case rwr_admitted of None \<Rightarrow> RWR_Product_Rejected | Some rwr_who \<Rightarrow>
      if \<not> rwr_available then RWR_Unavailable
      else case rwr_stored of None \<Rightarrow> RWR_Outside_Completed_Write
      | Some (rwr_stored_words,rwr_position,rwr_complete) \<Rightarrow>
         if \<not> rwr_active_policy rwr_peer rwr_proof rwr_config_epoch rwr_who rwr_target
             (source_binding_asset (source_payload_binding rwr_payload)) Read_Receipt (proof_epoch rwr_proof)
           then RWR_Product_Rejected
         else if rwr_write_words rwr_payload \<noteq> Some rwr_stored_words then RWR_Product_Rejected
         else if rwr_complete then RWR_Retained rwr_position else RWR_Outside_Completed_Write)"

lemma rwr_receipt_policy_is_the_checked_active_session_policy:
  assumes "rwr_authenticate rwr_token = Some rwr_who"
  shows "retained_receipt_permission (rwr_active_policy rwr_peer rwr_proof rwr_config_epoch) rwr_authenticate rwr_token rwr_proof rwr_target rwr_payload =
    rwr_active_policy rwr_peer rwr_proof rwr_config_epoch rwr_who rwr_target (envelope_asset (payload_envelope rwr_payload))
      Read_Receipt (proof_epoch rwr_proof)"
  using assms by (simp add: retained_receipt_permission_def)

lemma rwr_other_session_does_not_discharge_the_active_receipt_guard:
  assumes other: "code_source_session_call_grant rwr_peer other_session rwr_target Read_Receipt
      (source_binding_asset (source_payload_binding rwr_payload))"
    and missing: "\<not> code_source_session_call_grant rwr_peer (proof_session rwr_proof) rwr_target Read_Receipt
      (source_binding_asset (source_payload_binding rwr_payload))"
  shows "rwr_retain rwr_peer rwr_proof rwr_config_epoch rwr_target rwr_payload (Some rwr_who) True (Some (rwr_stored_words,rwr_position,rwr_complete)) =
    RWR_Product_Rejected"
  using missing by (simp add: rwr_retain_def rwr_active_policy_def)

lemma rwr_exact_completed_write_uses_the_retained_position:
  assumes "rwr_active_policy rwr_peer rwr_proof rwr_config_epoch rwr_who rwr_target (source_binding_asset (source_payload_binding rwr_payload))
    Read_Receipt (proof_epoch rwr_proof)" "rwr_write_words rwr_payload = Some rwr_stored_words"
  shows "rwr_retain rwr_peer rwr_proof rwr_config_epoch rwr_target rwr_payload (Some rwr_who) True (Some (rwr_stored_words,rwr_position,True)) =
    RWR_Retained rwr_position"
  using assms by (simp add: rwr_retain_def)

lemma rwr_execute_authorization_and_endpoint_status_precede_receipt:
  "rwr_retain rwr_peer rwr_proof rwr_config_epoch rwr_target rwr_payload None rwr_available rwr_stored = RWR_Product_Rejected"
  "rwr_retain rwr_peer rwr_proof rwr_config_epoch rwr_target rwr_payload (Some rwr_who) False rwr_stored = RWR_Unavailable"
  by (simp_all add: rwr_retain_def)

fun rwr_result_words where
  "rwr_result_words RWR_Product_Rejected = [0]"
| "rwr_result_words RWR_Unavailable = [2]"
| "rwr_result_words RWR_Outside_Completed_Write = [3]"
| "rwr_result_words (RWR_Retained rwr_position) =
    (case reference_write_code (Authority_Reply (Protocol_Response Data_Updated),Some rwr_position) of
      Some (rwr_code,Some rwr_committed) \<Rightarrow> [1,rwr_code,rwr_committed] | _ \<Rightarrow> [3])"

definition rwr_run :: "nat list list \<Rightarrow> nat list list option" where
  "rwr_run rwr_abi_rows =
    (case rwr_abi_rows of
     [[rwr_deployment,rwr_format,rwr_profile,rwr_config_epoch,rwr_maximum,rwr_max_frame,rwr_max_nesting,rwr_route],
      [rwr_instant,rwr_target,rwr_active_session,rwr_proof_epoch_value,rwr_selected_epoch,rwr_selected_revision],
      [rwr_principal,rwr_domain,rwr_ocid,rwr_rai,rwr_key_number],[rwr_directory_principal,rwr_directory_domain,rwr_directory_ocid,rwr_directory_rai],
      [rwr_ledger_session,rwr_ledger_principal,rwr_ledger_epoch],rwr_endpoints,
      [rwr_namespace,rwr_sequence,rwr_position,rwr_complete],rwr_original_words,rwr_stored_words,rwr_stored_core,
      rwr_caller_key,rwr_issuer,rwr_raw_packet,rwr_original_core,rwr_caller_preimage,rwr_caller_signature,
      rwr_token_preimage,rwr_token_signature,rwr_grant_json,rwr_grant_digest,[rwr_caller_verified,rwr_token_verified],
      [rwr_session_one,rwr_endpoint_one],rwr_execute_one,rwr_receipt_one,[rwr_session_two,rwr_endpoint_two],rwr_execute_two,rwr_receipt_two] \<Rightarrow>
     (case decode_wire_packet rwr_raw_packet of None \<Rightarrow> None | Some rwr_packet \<Rightarrow>
       (let rwr_core = packet_core rwr_packet in
        if rwr_core \<noteq> write_fixture_core \<or> encode_wire_core rwr_core \<noteq> rwr_original_core \<or> rwr_stored_core \<noteq> rwr_original_core \<or>
           envelope_signing_bytes rwr_core \<noteq> rwr_caller_preimage \<or> packet_signature rwr_packet \<noteq> rwr_caller_signature \<or>
           code_check_operation reference_accepts_write rwr_core \<noteq> None
        then None else
         (case code_materialize_source_call rwr_target rwr_core of Inr (Some rwr_request) \<Rightarrow>
           (let rwr_action = source_request_action rwr_request; rwr_payload = code_source_action_payload rwr_action in
            if rwr_write_words rwr_payload \<noteq> Some rwr_original_words \<or> source_request_id rwr_request \<noteq> (rwr_namespace,rwr_sequence) \<or>
               rwr_session_one \<noteq> rwr_active_session \<or> rwr_session_two = rwr_active_session \<or> rwr_endpoint_one \<noteq> rwr_target
            then None else
              (let rwr_identity = \<lparr>identity_principal = rwr_principal,identity_domain = rwr_domain,identity_ocid = rwr_ocid,identity_rai = rwr_rai\<rparr>;
                   rwr_directory = \<lparr>identity_principal = rwr_directory_principal,identity_domain = rwr_directory_domain,
                     identity_ocid = rwr_directory_ocid,identity_rai = rwr_directory_rai\<rparr>;
                   rwr_proof = \<lparr>proof_session = rwr_active_session,proof_epoch = rwr_proof_epoch_value\<rparr>;
                   rwr_snapshot = \<lparr>source_identity_cut = \<lparr>cut_authority_epoch = rwr_selected_epoch,cut_revision = rwr_selected_revision\<rparr>,
                     source_identity_directory = (\<lambda>rwr_actor. if rwr_actor = rwr_directory_principal then Some rwr_directory else None),
                     source_identity_sessions = (\<lambda>rwr_session_id. if rwr_session_id = rwr_ledger_session then
                       Some \<lparr>session_principal = rwr_ledger_principal,session_epoch = rwr_ledger_epoch\<rparr> else None),
                     source_identity_endpoints = set rwr_endpoints\<rparr>;
                   rwr_grant_one = \<lparr>source_call_execute_assets = set rwr_execute_one,source_call_receipt_assets = set rwr_receipt_one\<rparr>;
                   rwr_grant_two = \<lparr>source_call_execute_assets = set rwr_execute_two,source_call_receipt_assets = set rwr_receipt_two\<rparr>;
                   rwr_peer = \<lparr>source_signing_identity = rwr_identity,source_signing_key_number = rwr_key_number,
                     source_signing_public_key = rwr_caller_key,source_signing_sessions =
                       [(rwr_session_one,[(rwr_endpoint_one,rwr_grant_one)]),(rwr_session_two,[(rwr_endpoint_two,rwr_grant_two)])]\<rparr>;
                   rwr_signing = \<lparr>source_signing_deployment = rwr_deployment,source_signing_epoch = rwr_config_epoch,
                     source_signing_targets = set rwr_endpoints,source_signing_route_scope = rwr_route,
                     source_signing_max_frame = rwr_max_frame,source_signing_max_nesting = rwr_max_nesting,
                     source_signing_peers = [(rwr_principal,rwr_peer)]\<rparr>;
                   rwr_token_config = \<lparr>source_session_profile = (rwr_deployment,rwr_format,rwr_profile),source_session_epoch = rwr_config_epoch,
                     source_session_issuer = rwr_issuer,source_session_max_seconds = rwr_maximum,
                     source_session_peers = [(rwr_principal,\<lparr>source_session_identity = rwr_identity,
                         source_session_serialized_grants = [(rwr_session_one,rwr_grant_json)]\<rparr>)]\<rparr>;
                   rwr_sha = (\<lambda>rwr_bytes. if rwr_bytes = code_session_grants_domain @ rwr_grant_json then rwr_grant_digest else []);
                   token_curve = (\<lambda>rwr_pub_key rwr_bytes rwr_sig. rwr_token_verified = 1 \<and> rwr_pub_key = rwr_issuer \<and>
                     rwr_bytes = rwr_token_preimage \<and> rwr_sig = rwr_token_signature);
                   auth = (\<lambda>_ rwr_selected_proof. code_source_authenticate_session_bytes rwr_token_config rwr_sha token_curve
                     rwr_token_preimage rwr_token_signature rwr_selected_proof (Some rwr_instant));
                   rwr_policy = rwr_active_policy rwr_peer rwr_proof rwr_config_epoch;
                   rwr_asset = source_binding_asset (source_payload_binding rwr_payload);
                   rwr_verify = (\<lambda>rwr_who rwr_selected_proof rwr_endpoint rwr_operation rwr_call_id rwr_selected_action.
                     rwr_selected_proof = rwr_proof \<and> rwr_endpoint = rwr_target \<and> rwr_operation = Execute_Ordinary \<and>
                     rwr_call_id = source_request_id rwr_request \<and> rwr_selected_action = rwr_action \<and>
                     length rwr_raw_packet \<le> rwr_max_frame \<and> rwr_max_nesting > 0 \<and>
                     code_source_signature_header rwr_signing rwr_peer rwr_who rwr_proof rwr_target rwr_core \<and> rwr_caller_verified = 1 \<and>
                     code_source_session_call_grant rwr_peer rwr_active_session rwr_target rwr_operation rwr_asset);
                   rwr_admitted = code_source_authorize_call auth rwr_policy rwr_verify () rwr_proof rwr_request Execute_Ordinary rwr_snapshot;
                   rwr_stored = Some (rwr_stored_words,rwr_position,rwr_complete = 1);
                   rwr_finish = rwr_retain rwr_peer rwr_proof rwr_config_epoch rwr_target rwr_payload rwr_admitted
               in Some [map asg_bit [code_source_active_identity auth () rwr_proof rwr_snapshot = Some rwr_identity,
                   rwr_admitted = Some rwr_identity,rwr_policy rwr_identity rwr_target rwr_asset Execute_Ordinary rwr_proof_epoch_value,
                   rwr_policy rwr_identity rwr_target rwr_asset Read_Receipt rwr_proof_epoch_value,
                   code_source_session_call_grant rwr_peer rwr_session_two rwr_target Read_Receipt rwr_asset,
                   rwr_write_words rwr_payload = Some rwr_stored_words,rwr_complete = 1],
                 [cut_revision (source_payload_cut rwr_payload),rwr_selected_revision],
                 rwr_result_words (rwr_finish True rwr_stored),rwr_result_words (rwr_finish False rwr_stored)]))
         | _ \<Rightarrow> None)))
     | _ \<Rightarrow> None)"

definition rwr_submit_integer :: "integer list list \<Rightarrow> integer list list option" where
  "rwr_submit_integer rwr_rows =
    (if list_all (list_all (\<lambda>rwr_word. 0 \<le> rwr_word \<and> rwr_word < 2^64)) rwr_rows then
       map_option (map (map integer_of_nat)) (rwr_run (map (map nat_of_integer) rwr_rows))
     else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms rwr_receipt_policy_is_the_checked_active_session_policy
    rwr_other_session_does_not_discharge_the_active_receipt_guard rwr_exact_completed_write_uses_the_retained_position
    rwr_execute_authorization_and_endpoint_status_precede_receipt
    source_attestation.authorized_exact_write_retry_reads_before_the_fresh_cut
    a_source_authorized_call_consumes_its_exact_current_session_namespace_and_typed_action
    source_session_authentication_keeps_the_current_record_grants_time_and_curve_inputs})
  then () else error "Unexpected oracle in retained Write Receipt checks"
\<close>

export_code rwr_submit_integer in SML module_name Retained_Write_Receipt_ABI file_prefix "retained_write_receipt_abi"

end
