theory Wire_Code_Fixture_Replay_Environment
  imports Wire_Code_Fixture_Primitive_Data "OIP_Reserve_Debit_Finite_Base.Wire_Code_Finite_Source_Slice"
begin

definition code_fixture_identity_7 :: registered_identity where
  "code_fixture_identity_7 = \<lparr>identity_principal = 7,identity_domain = 0,identity_ocid = 107,identity_rai = 207\<rparr>"

definition code_fixture_identity_8 :: registered_identity where
  "code_fixture_identity_8 = \<lparr>identity_principal = 8,identity_domain = 0,identity_ocid = 108,identity_rai = 208\<rparr>"

definition code_fixture_current_identity_snapshot :: "code_finite_source_slice \<Rightarrow> code_source_identity_snapshot" where
  "code_fixture_current_identity_snapshot state =
    \<lparr>source_identity_cut = \<lparr>cut_authority_epoch = 9,cut_revision = slice_revision state\<rparr>,
     source_identity_directory = map_of [(7,code_fixture_identity_7),(8,code_fixture_identity_8)],
     source_identity_sessions = map_of [(1,\<lparr>session_principal = 7,session_epoch = 9\<rparr>),
       (2,\<lparr>session_principal = 7,session_epoch = 9\<rparr>)],source_identity_endpoints = {0,2}\<rparr>"

definition code_fixture_authenticate_session :: "nat \<Rightarrow> code_fixture_token \<Rightarrow> session_proof \<Rightarrow> registered_identity option" where
  "code_fixture_authenticate_session now token proof = code_source_authenticate_session_bytes code_fixture_session_config
    code_fixture_sha256 code_fixture_curve (fixture_token_preimage token) (fixture_token_signature token) proof (Some now)"

definition code_fixture_current_asset_policy :: endpoint_policy where
  "code_fixture_current_asset_policy identity target asset operation epoch =
    (epoch = source_signing_epoch code_fixture_signing_config \<and>
     (case map_of (source_signing_peers code_fixture_signing_config) (identity_principal identity) of None \<Rightarrow> False
      | Some peer \<Rightarrow> source_signing_identity peer = identity \<and>
        list_ex (\<lambda>row. code_source_session_call_grant peer (fst row) target operation asset) (source_signing_sessions peer)))"

definition code_fixture_source_request :: "code_finite_selected_ordinary \<Rightarrow> code_source_action_request" where
  "code_fixture_source_request chosen =
    \<lparr>source_request_target = wire_target_domain (finite_selected_core chosen),
      source_request_id = native_id (finite_selected_native chosen),source_request_expected = native_cut (finite_selected_native chosen),
      source_request_action = Code_Source_Ordinary_Action (finite_selected_payload chosen)\<rparr>"

definition code_fixture_authorize :: "wire_bytes \<Rightarrow> code_finite_selected_ordinary \<Rightarrow> code_fixture_token \<Rightarrow> nat \<Rightarrow>
  endpoint_use \<Rightarrow> code_finite_source_slice \<Rightarrow> registered_identity option" where
  "code_fixture_authorize bytes chosen token now operation state =
    (let proof = \<lparr>proof_session = native_session (finite_selected_native chosen),proof_epoch = 9\<rparr>
     in code_source_authorize_call (code_fixture_authenticate_session now) code_fixture_current_asset_policy
       (\<lambda>identity proof target purpose call_id action.
          code_verify_source_no_proof_call code_fixture_signing_config code_fixture_curve bytes identity proof target purpose call_id action = Code_Source_Call_Verified)
       token proof (code_fixture_source_request chosen) operation (code_fixture_current_identity_snapshot state))"

definition code_fixture_wire_profile :: negotiated_wire_profile where
  "code_fixture_wire_profile = \<lparr>negotiated_version = 6,
    negotiated_families = {Wire_State_Sync,Wire_Regulatory,Wire_Lock,Wire_Query,Wire_Ack,Wire_Heartbeat,Wire_Governance},
    negotiated_atomicities = {1,2,3},negotiated_schemes = {1}\<rparr>"

definition code_fixture_wire_boundary :: "nat \<Rightarrow> wire_boundary" where
  "code_fixture_wire_boundary now = \<lparr>boundary_profile = code_fixture_wire_profile,boundary_deployment = 7,
    boundary_source = 0,boundary_target = 0,boundary_principal = 7,boundary_key = 9,boundary_epoch = 9,
    boundary_route_scope = 1,boundary_now = now,boundary_asset_ttl_floor = 2,boundary_future_skew = 0,
    boundary_max_frame = 1048576,boundary_version_floor = 6,boundary_critical_allowed = False,boundary_threshold_supported = False\<rparr>"

definition code_fixture_packet_admission :: "bool \<Rightarrow> nat \<Rightarrow> wire_bytes \<Rightarrow> wire_refusal option" where
  "code_fixture_packet_admission resolving now bytes =
    (if length bytes > 1048576 then Some Invalid_Wire_Format
     else case code_check_declared_version bytes 1048576 of Some reason \<Rightarrow> Some reason
      | None \<Rightarrow> (case decode_wire_packet bytes of None \<Rightarrow> Some Invalid_Wire_Format | Some packet \<Rightarrow>
        let admitted_now = (if resolving then wire_sent_seconds (packet_core packet) else now)
        in code_admit_packet (\<lambda>core message signature. code_fixture_curve code_fixture_peer_key message signature)
             packet (code_fixture_wire_boundary admitted_now)))"

text \<open>
  This environment is the concrete fixture's host configuration, not a
  generic source configuration parser. The negotiation metadata follows
  channel_for in the frozen observer (version6, families1..7, atomicities1..3,
  scheme1, local/remote0, expiry200), independent of product outputs. The
  final permanent stimulus schema must carry those external channel getter
  values explicitly. This slice uses no expired-channel event.
  Cryptographic values are only the independently checked input facts.
  Unknown requests remain outside this bounded canary's primitive coverage.
  Exact resolution revalidates at signed issue time and does not reapply a
  maximum delivery TTL. Source/current directory and capability checks use
  the same original packet, native session and independent model revision.
\<close>

end
