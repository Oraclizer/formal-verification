theory Wire_Code_Fixture_Input_Data
  imports Wire_Code_Fixture_Input_Bytes
begin

record code_fixture_token =
  fixture_token_preimage :: wire_bytes
  fixture_token_signature :: wire_bytes

datatype code_fixture_api = Code_Fixture_Initialize | Code_Fixture_Receive | Code_Fixture_Receive_Response
  | Code_Fixture_Resolve | Code_Fixture_Resolve_Response

record code_fixture_stimulus =
  fixture_stimulus_id :: nat
  fixture_stimulus_api :: code_fixture_api
  fixture_stimulus_packet :: "wire_bytes option"
  fixture_stimulus_token :: code_fixture_token
  fixture_stimulus_clock :: nat
  fixture_stimulus_close :: "bool option"

definition code_fixture_token_0 :: "code_fixture_token" where
  "code_fixture_token_0 = \<lparr>fixture_token_preimage = code_fixture_claim_preimage_0,fixture_token_signature = code_fixture_claim_signature_0\<rparr>"

definition code_fixture_token_1 :: "code_fixture_token" where
  "code_fixture_token_1 = \<lparr>fixture_token_preimage = code_fixture_claim_preimage_1,fixture_token_signature = code_fixture_claim_signature_1\<rparr>"

definition code_fixture_origin_context :: "code_finite_lock_context" where
  "code_fixture_origin_context = \<lparr>finite_context_endpoint = 0,finite_context_relay_epoch = 9,
    finite_context_authority_epoch = 9,finite_context_version = 0,
    finite_context_permissions = [Code_Finite_Asset_Binding 7 17,Code_Finite_Asset_Binding 8 17],finite_context_readers = [7],
    finite_context_metadata = [((0,17),\<lparr>as_reg_state = ACTIVE\<rparr>),((2,17),\<lparr>as_reg_state = ACTIVE\<rparr>)],
    finite_context_metadata_locks = [],finite_context_restriction_clear = [17],finite_context_dependencies = [(17,[])],
    finite_context_write_permissions = [(7,17,9)],finite_context_spend_permissions = []\<rparr>"

definition code_fixture_receiver_context :: "code_finite_lock_context" where
  "code_fixture_receiver_context = code_fixture_origin_context\<lparr>finite_context_endpoint := 2\<rparr>"

definition code_fixture_initial_machine :: "code_finite_reservation_machine" where
  "code_fixture_initial_machine = \<lparr>finite_machine_state = \<lparr>finite_asset_owners = [],finite_reservations = [],
    finite_asset_values = [(17,0)],finite_asset_versions = [(17,0)],finite_source_units = [((0,17),10)],
    finite_destination_units = [],finite_funded_units = [],finite_source_effects = [],finite_issued_certificates = [],
    finite_consumed_at = [],finite_credit_history = [],finite_descendants = [],finite_clock = 0\<rparr>,
    finite_machine_journal = [],finite_machine_observations = []\<rparr>"

definition code_fixture_source_account_rows :: "((source_account \<times> nat) \<times> nat) list" where
  "code_fixture_source_account_rows = [(((0,17),7),10)]"

definition code_fixture_session_config :: "code_source_session_config" where
  "code_fixture_session_config = \<lparr>source_session_profile = (7,1,99),source_session_epoch = 9,
    source_session_issuer = code_fixture_issuer_key,source_session_max_seconds = 600,
    source_session_peers = [(7,\<lparr>source_session_identity = \<lparr>identity_principal = 7,identity_domain = 0,identity_ocid = 107,identity_rai = 207\<rparr>,
      source_session_serialized_grants = [(1,code_fixture_grants_json_0),(2,code_fixture_grants_json_1)]\<rparr>)]\<rparr>"

definition code_fixture_signing_config :: "code_source_call_signing_config" where
  "code_fixture_signing_config = \<lparr>source_signing_deployment = 7,source_signing_epoch = 9,source_signing_targets = {0},
    source_signing_route_scope = 1,source_signing_max_frame = 1048576,source_signing_max_nesting = 4,
    source_signing_peers = [(7,\<lparr>source_signing_identity = \<lparr>identity_principal = 7,identity_domain = 0,identity_ocid = 107,identity_rai = 207\<rparr>,source_signing_key_number = 9,
      source_signing_public_key = code_fixture_peer_key,source_signing_sessions = [(1,[(0,\<lparr>source_call_execute_assets = {},source_call_receipt_assets = {17}\<rparr>)]),(2,[(0,\<lparr>source_call_execute_assets = {17},source_call_receipt_assets = {17}\<rparr>)])]\<rparr>)]\<rparr>"

definition code_fixture_stimuli :: "code_fixture_stimulus list" where
  "code_fixture_stimuli = [
    \<lparr>fixture_stimulus_id = 0,fixture_stimulus_api = Code_Fixture_Initialize,fixture_stimulus_packet = None,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 105,fixture_stimulus_close = None\<rparr>,
    \<lparr>fixture_stimulus_id = 1,fixture_stimulus_api = Code_Fixture_Receive_Response,fixture_stimulus_packet = Some code_fixture_packet_0,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 105,fixture_stimulus_close = None\<rparr>,
    \<lparr>fixture_stimulus_id = 2,fixture_stimulus_api = Code_Fixture_Receive_Response,fixture_stimulus_packet = Some code_fixture_packet_1,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 105,fixture_stimulus_close = None\<rparr>,
    \<lparr>fixture_stimulus_id = 3,fixture_stimulus_api = Code_Fixture_Receive_Response,fixture_stimulus_packet = Some code_fixture_packet_2,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 105,fixture_stimulus_close = None\<rparr>,
    \<lparr>fixture_stimulus_id = 4,fixture_stimulus_api = Code_Fixture_Receive,fixture_stimulus_packet = Some code_fixture_packet_2,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 105,fixture_stimulus_close = None\<rparr>,
    \<lparr>fixture_stimulus_id = 5,fixture_stimulus_api = Code_Fixture_Receive_Response,fixture_stimulus_packet = Some code_fixture_packet_2,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 105,fixture_stimulus_close = None\<rparr>,
    \<lparr>fixture_stimulus_id = 6,fixture_stimulus_api = Code_Fixture_Receive,fixture_stimulus_packet = Some code_fixture_packet_2,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 106,fixture_stimulus_close = None\<rparr>,
    \<lparr>fixture_stimulus_id = 7,fixture_stimulus_api = Code_Fixture_Resolve,fixture_stimulus_packet = Some code_fixture_packet_2,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 106,fixture_stimulus_close = Some False\<rparr>,
    \<lparr>fixture_stimulus_id = 8,fixture_stimulus_api = Code_Fixture_Resolve_Response,fixture_stimulus_packet = Some code_fixture_packet_2,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 106,fixture_stimulus_close = Some True\<rparr>,
    \<lparr>fixture_stimulus_id = 9,fixture_stimulus_api = Code_Fixture_Resolve,fixture_stimulus_packet = Some code_fixture_packet_2,fixture_stimulus_token = code_fixture_token_1,fixture_stimulus_clock = 106,fixture_stimulus_close = Some False\<rparr>,
    \<lparr>fixture_stimulus_id = 10,fixture_stimulus_api = Code_Fixture_Initialize,fixture_stimulus_packet = None,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 105,fixture_stimulus_close = None\<rparr>,
    \<lparr>fixture_stimulus_id = 11,fixture_stimulus_api = Code_Fixture_Receive_Response,fixture_stimulus_packet = Some code_fixture_packet_0,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 105,fixture_stimulus_close = None\<rparr>,
    \<lparr>fixture_stimulus_id = 12,fixture_stimulus_api = Code_Fixture_Receive_Response,fixture_stimulus_packet = Some code_fixture_packet_1,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 105,fixture_stimulus_close = None\<rparr>,
    \<lparr>fixture_stimulus_id = 13,fixture_stimulus_api = Code_Fixture_Receive_Response,fixture_stimulus_packet = Some code_fixture_packet_3,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 105,fixture_stimulus_close = None\<rparr>,
    \<lparr>fixture_stimulus_id = 14,fixture_stimulus_api = Code_Fixture_Receive,fixture_stimulus_packet = Some code_fixture_packet_3,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 105,fixture_stimulus_close = None\<rparr>]"

definition rdr_same_cut_stimuli :: "code_fixture_stimulus list" where
  "rdr_same_cut_stimuli = [
    \<lparr>fixture_stimulus_id = 0,fixture_stimulus_api = Code_Fixture_Initialize,fixture_stimulus_packet = None,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 105,fixture_stimulus_close = None\<rparr>,
    \<lparr>fixture_stimulus_id = 1,fixture_stimulus_api = Code_Fixture_Receive_Response,fixture_stimulus_packet = Some code_fixture_packet_4,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 105,fixture_stimulus_close = None\<rparr>,
    \<lparr>fixture_stimulus_id = 2,fixture_stimulus_api = Code_Fixture_Receive_Response,fixture_stimulus_packet = Some code_fixture_packet_5,fixture_stimulus_token = code_fixture_token_0,fixture_stimulus_clock = 105,fixture_stimulus_close = None\<rparr>]"

text \<open>Data emitted from the three authorized input corpora only.
  This fixed projection has one initially ACTIVE asset, initial value/version/clock zero,
  relay/binding epoch equal to the supplied epoch, separator zero and no prior allocations.
  These are declared model seed coordinates, not observed after-state values.\<close>

end
