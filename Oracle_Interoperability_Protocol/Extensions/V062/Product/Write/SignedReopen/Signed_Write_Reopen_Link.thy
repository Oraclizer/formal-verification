theory Signed_Write_Reopen_Link
  imports "OIP_Reference_Write_Core_Seed.Reference_Write_Core_Seed"
    "OIP_Reserve_Debit_Finite_Base.Wire_Code_Finite_Closed_Financial"
    "OIP_Message_Code.Wire_Code_Session_Authentication" "HOL-Library.Code_Target_Nat"
begin

definition swr_guard where
  "swr_guard swr_context swr_request swr_generation swr_versions swr_value swr_financial =
    (code_finite_closed_owns swr_context swr_request swr_generation swr_versions swr_financial \<and>
     map_option reservation_phase (map_of (finite_reservations swr_financial)
       (binding_key (request_binding swr_request))) = Some Reservation_Held \<and>
     (request_caller swr_request,binding_asset (request_binding swr_request),swr_value)
       \<in> set (finite_context_write_permissions swr_context))"

lemma swr_guard_is_the_checked_write_guard:
  "swr_guard swr_context swr_request swr_generation swr_versions swr_value swr_financial =
   (owns_current_reservation (code_interpret_finite_context swr_context) swr_request swr_generation
      swr_versions (code_interpret_finite_financial swr_financial) \<and>
    phase_at (code_interpret_finite_financial swr_financial) (binding_key (request_binding swr_request))
      = Some Reservation_Held \<and>
    (request_caller swr_request,binding_asset (request_binding swr_request),swr_value)
      \<in> lock_write_permissions (code_interpret_finite_context swr_context))"
  by (simp add: swr_guard_def closed_ownership_is_exactly_the_interpreted_existing_finite_query
    finite_current_ownership_is_the_exact_existing_current_footprint_test phase_at_def
    code_interpret_finite_context_def code_interpret_finite_financial_def)

context source_attestation
begin

lemma swr_guard_reaches_the_existing_fresh_write:
  assumes swr_connected:
    "call_connection (product_calls (write_source swr_connection swr_before)) = Authority_Connected"
  and swr_current: "envelope_cut (payload_envelope swr_payload) = write_ledger_cut swr_before"
  and swr_ready:
    "reference_write_ready swr_registered swr_actor swr_id swr_payload
      (write_source swr_connection swr_before) swr_before"
  and swr_command:
    "envelope_command (payload_envelope swr_payload) =
      Client_Protocol swr_endpoint swr_index (Write_Intent swr_request swr_generation swr_versions swr_value)"
  and swr_core:
    "call_authority_state (product_calls (write_source swr_connection swr_before)) = swr_selected_core"
  and swr_context: "current_lock_view swr_selected_core swr_endpoint = code_interpret_finite_context swr_finite"
  and swr_financial: "machine_state (core_parent swr_selected_core) = code_interpret_finite_financial swr_opening"
  and swr_passes: "swr_guard swr_finite swr_request swr_generation (vector_lookup swr_versions) swr_value swr_opening"
  shows "reference_write_fresh swr_registered swr_connection swr_actor swr_id swr_payload swr_before =
    record_reference_write swr_id swr_payload (Authority_Reply (Protocol_Response Data_Updated))
      (Some (reference_write_dispatch (write_source swr_connection swr_before) swr_id (payload_envelope swr_payload)))
      swr_before"
  apply (rule a_fresh_write_commits_when_the_current_guards_pass[OF swr_connected swr_current swr_ready swr_command])
  using swr_passes by (simp add: swr_core swr_context swr_financial Let_def swr_guard_is_the_checked_write_guard)

end

definition swr_finite_opening where
  "swr_finite_opening swr_clock swr_asset swr_open_value swr_version swr_active swr_balance swr_reservation =
    (let swr_binding = reservation_binding swr_reservation in
      \<lparr>finite_asset_owners = [(swr_asset,swr_active)],
       finite_reservations = [(binding_key swr_binding,swr_reservation)],
       finite_asset_values = [(swr_asset,swr_open_value)], finite_asset_versions = [(swr_asset,swr_version)],
       finite_source_units = [(source_account_of swr_binding,swr_balance)],
       finite_destination_units = [], finite_funded_units = [], finite_source_effects = [],
       finite_issued_certificates = [], finite_consumed_at = [], finite_credit_history = [],
       finite_descendants = [], finite_clock = swr_clock\<rparr>)"

definition swr_finite_context where
  "swr_finite_context swr_endpoint swr_epoch swr_request swr_grant swr_dependencies swr_writers =
    \<lparr>finite_context_endpoint = swr_endpoint, finite_context_relay_epoch = 0,
      finite_context_authority_epoch = swr_epoch, finite_context_version = request_version swr_request,
      finite_context_permissions = (if swr_grant then
        [Code_Finite_Exact_Binding (request_caller swr_request) (request_binding swr_request)] else []),
      finite_context_readers = [], finite_context_metadata = [], finite_context_metadata_locks = [],
      finite_context_restriction_clear = [],
      finite_context_dependencies = [(binding_asset (request_binding swr_request),swr_dependencies)],
      finite_context_write_permissions = swr_writers, finite_context_spend_permissions = []\<rparr>"

definition swr_recorded_projection where
  "swr_recorded_projection swr_value swr_version swr_revision =
    (case reference_write_code (Authority_Reply (Protocol_Response Data_Updated),Some swr_revision) of
       Some (swr_code,Some swr_position) \<Rightarrow>
         Some [swr_code,swr_position,swr_value,Suc swr_version,Suc swr_revision]
     | _ \<Rightarrow> None)"

definition swr_run :: "nat list list \<Rightarrow> nat list option" where
  "swr_run swr_rows =
    (case swr_rows of
     [[swr_deployment,swr_format,swr_profile,swr_epoch,swr_max_seconds,swr_max_frame,swr_max_nesting,swr_scope],
      [swr_now,swr_target,swr_session,swr_cut_epoch,swr_revision],
      [swr_principal,swr_domain,swr_ocid,swr_rai,swr_key_number],
      [swr_dir_principal,swr_dir_domain,swr_dir_ocid,swr_dir_rai],
      [swr_ledger_session,swr_ledger_principal,swr_ledger_epoch],
      [swr_clock,swr_deadline,swr_holder,swr_generation,swr_asset,swr_open_value,swr_version,swr_balance,
       swr_active_domain,swr_active_event,swr_ctx_epoch,swr_route_grant,swr_value_actor,swr_value_asset,swr_permitted_value],
      swr_endpoints,swr_dependencies,swr_footprint,swr_execute,swr_receipts,swr_key,swr_issuer,
      swr_packet,swr_core_bytes,swr_preimage,swr_sig,swr_token_preimage,swr_token_sig,
      swr_grant_json,swr_grant_digest,[swr_request_verified,swr_token_verified]] \<Rightarrow>
      (case decode_wire_packet swr_packet of None \<Rightarrow> None | Some swr_wire_packet \<Rightarrow>
       (let swr_core = packet_core swr_wire_packet in
        if swr_core \<noteq> write_fixture_core \<or> encode_wire_core swr_core \<noteq> swr_core_bytes \<or>
           envelope_signing_bytes swr_core \<noteq> swr_preimage \<or> packet_signature swr_wire_packet \<noteq> swr_sig \<or>
           code_check_operation reference_accepts_write swr_core \<noteq> None then None
        else
          (let swr_request = sample_request swr_asset in
           case select_reference_write (\<lambda>_. Some swr_request) swr_core of None \<Rightarrow> None
           | Some (swr_id,swr_payload) \<Rightarrow>
            (let swr_envelope = payload_envelope swr_payload in
             case envelope_command swr_envelope of
               Client_Protocol swr_endpoint _ (Write_Intent swr_selected_request swr_expected_generation
                   swr_versions swr_value) \<Rightarrow>
               (let swr_identity = \<lparr>identity_principal = swr_principal, identity_domain = swr_domain,
                      identity_ocid = swr_ocid, identity_rai = swr_rai\<rparr>;
                    swr_directory = \<lparr>identity_principal = swr_dir_principal, identity_domain = swr_dir_domain,
                      identity_ocid = swr_dir_ocid, identity_rai = swr_dir_rai\<rparr>;
                    swr_cut = \<lparr>cut_authority_epoch = swr_cut_epoch, cut_revision = swr_revision\<rparr>;
                    swr_proof = \<lparr>proof_session = swr_session, proof_epoch = swr_cut_epoch\<rparr>;
                    swr_snapshot = \<lparr>source_identity_cut = swr_cut,
                      source_identity_directory = (\<lambda>swr_actor. if swr_actor = swr_dir_principal then Some swr_directory else None),
                      source_identity_sessions = (\<lambda>swr_session_id. if swr_session_id = swr_ledger_session then Some
                        \<lparr>session_principal = swr_ledger_principal, session_epoch = swr_ledger_epoch\<rparr> else None),
                      source_identity_endpoints = set swr_endpoints\<rparr>;
                    swr_grant = \<lparr>source_call_execute_assets = set swr_execute, source_call_receipt_assets = set swr_receipts\<rparr>;
                    swr_peer = \<lparr>source_signing_identity = swr_identity, source_signing_key_number = swr_key_number,
                      source_signing_public_key = swr_key, source_signing_sessions = [(swr_session,[(swr_target,swr_grant)])]\<rparr>;
                    swr_signing = \<lparr>source_signing_deployment = swr_deployment, source_signing_epoch = swr_epoch,
                      source_signing_targets = set swr_endpoints, source_signing_route_scope = swr_scope,
                      source_signing_max_frame = swr_max_frame, source_signing_max_nesting = swr_max_nesting,
                      source_signing_peers = [(swr_principal,swr_peer)]\<rparr>;
                    swr_auth_config = \<lparr>source_session_profile = (swr_deployment,swr_format,swr_profile),
                      source_session_epoch = swr_epoch, source_session_issuer = swr_issuer, source_session_max_seconds = swr_max_seconds,
                      source_session_peers = [(swr_principal,\<lparr>source_session_identity = swr_identity,
                        source_session_serialized_grants = [(swr_session,swr_grant_json)]\<rparr>)]\<rparr>;
                    swr_sha = (\<lambda>swr_bytes. if swr_bytes = code_session_grants_domain @ swr_grant_json then swr_grant_digest else []);
                    swr_token_curve = (\<lambda>swr_public swr_bytes swr_signature. swr_token_verified = 1 \<and>
                      swr_public = swr_issuer \<and> swr_bytes = swr_token_preimage \<and> swr_signature = swr_token_sig);
                    swr_request_curve = (\<lambda>swr_public swr_bytes swr_signature. swr_request_verified = 1 \<and>
                      swr_public = swr_key \<and> swr_bytes = swr_preimage \<and> swr_signature = swr_sig);
                    swr_auth = (\<lambda>_ swr_current_proof. code_source_authenticate_session_bytes swr_auth_config swr_sha
                      swr_token_curve swr_token_preimage swr_token_sig swr_current_proof (Some swr_now));
                    swr_binding = request_binding swr_selected_request;
                    swr_reservation = \<lparr>reservation_binding = swr_binding, reservation_footprint = swr_footprint,
                      reservation_worker = swr_holder, reservation_generation = swr_generation,
                      reservation_deadline = swr_deadline, reservation_phase = Reservation_Held\<rparr>;
                    swr_opening = swr_finite_opening swr_clock swr_asset swr_open_value swr_version
                      (swr_active_domain,swr_active_event) swr_balance swr_reservation;
                    swr_context = swr_finite_context swr_endpoint swr_ctx_epoch swr_selected_request
                      (swr_route_grant = 1) swr_dependencies [(swr_value_actor,swr_value_asset,swr_permitted_value)]
                in if code_source_active_identity swr_auth () swr_proof swr_snapshot = Some swr_identity \<and>
                    code_source_signature_header swr_signing swr_peer swr_identity swr_proof swr_target swr_core \<and>
                    swr_request_curve (source_signing_public_key swr_peer) (envelope_signing_bytes swr_core)
                      (packet_signature swr_wire_packet) \<and>
                    code_source_session_call_grant swr_peer swr_session swr_target Execute_Ordinary swr_asset \<and>
                    swr_endpoint = swr_target \<and> fst swr_id = swr_principal \<and>
                    envelope_session swr_envelope = swr_session \<and> envelope_cut swr_envelope = swr_cut \<and>
                    swr_asset = binding_asset swr_binding \<and> length swr_packet \<le> swr_max_frame \<and>
                    Suc swr_revision < 2^64 \<and> Suc swr_version < 2^64 \<and>
                    swr_guard swr_context swr_selected_request swr_expected_generation
                      (code_model_version_at swr_versions) swr_value swr_opening
                then swr_recorded_projection swr_value swr_version swr_revision else None)
              | _ \<Rightarrow> None))))
     | _ \<Rightarrow> None)"

definition swr_submit_integer :: "integer list list \<Rightarrow> integer list option" where
  "swr_submit_integer swr_rows =
    (if list_all (list_all (\<lambda>swr_word. 0 \<le> swr_word)) swr_rows
     then map_option (map integer_of_nat) (swr_run (map (map nat_of_integer) swr_rows)) else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms swr_guard_is_the_checked_write_guard
      source_attestation.swr_guard_reaches_the_existing_fresh_write
      the_write_seed_selects_the_proved_product_input reference_write_observation_table_exact})
  then () else error "Unexpected oracle in signed Write link"
\<close>

export_code swr_submit_integer write_fixture_integer_core reference_write_vector_rows
  in SML module_name OIP_Signed_Write_ABI file_prefix oip_signed_write

end
