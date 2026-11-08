theory Wire_Code_Source_Call_Signature
  imports Wire_Code_Source_Identity
begin

record code_source_call_grants =
  source_call_execute_assets :: "nat set"
  source_call_receipt_assets :: "nat set"

record code_source_signing_peer =
  source_signing_identity :: registered_identity
  source_signing_key_number :: nat
  source_signing_public_key :: wire_bytes
  source_signing_sessions :: "(nat \<times> (nat \<times> code_source_call_grants) list) list"

record code_source_call_signing_config =
  source_signing_deployment :: nat
  source_signing_epoch :: nat
  source_signing_targets :: "nat set"
  source_signing_route_scope :: nat
  source_signing_max_frame :: nat
  source_signing_max_nesting :: nat
  source_signing_peers :: "(nat \<times> code_source_signing_peer) list"

definition code_source_session_call_grant ::
  "code_source_signing_peer \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> endpoint_use \<Rightarrow> nat \<Rightarrow> bool" where
  "code_source_session_call_grant peer session target operation asset =
    (case map_of (source_signing_sessions peer) session of None \<Rightarrow> False | Some endpoints \<Rightarrow>
      (case map_of endpoints target of None \<Rightarrow> False | Some grants \<Rightarrow>
        if operation = Execute_Ordinary then asset \<in> source_call_execute_assets grants
        else if operation = Read_Receipt then asset \<in> source_call_receipt_assets grants else False))"

definition code_source_signature_header ::
  "code_source_call_signing_config \<Rightarrow> code_source_signing_peer \<Rightarrow> registered_identity \<Rightarrow>
    session_proof \<Rightarrow> nat \<Rightarrow> wire_core \<Rightarrow> bool" where
  "code_source_signature_header signing_config peer identity proof target (core::wire_core) \<longleftrightarrow>
    source_signing_identity peer = identity \<and> proof_epoch proof = source_signing_epoch signing_config \<and>
    target \<in> source_signing_targets signing_config \<and>
    wire_version core = 6 \<and> wire_purpose core = 1 \<and>
    wire_deployment core = source_signing_deployment signing_config \<and>
    wire_source_domain core = identity_domain identity \<and> wire_target_domain core = target \<and>
    wire_principal core = identity_principal identity \<and> wire_key_number core = source_signing_key_number peer \<and>
    wire_authority_epoch core = proof_epoch proof \<and>
    wire_route_scope core = source_signing_route_scope signing_config \<and> wire_signature_scheme core = 1"

fun code_source_no_proof_ordinary_call :: "ordinary_wire_command \<Rightarrow> bool" where
  "code_source_no_proof_ordinary_call (Wire_Reserve duration) = True"
| "code_source_no_proof_ordinary_call (Wire_Dispatch generation) = True"
| "code_source_no_proof_ordinary_call (Wire_Debit generation) = True"
| "code_source_no_proof_ordinary_call (Wire_Deliver reference) = True"
| "code_source_no_proof_ordinary_call Wire_Publish = True"
| "code_source_no_proof_ordinary_call command = False"

datatype code_source_call_verification =
    Code_Source_Call_Verified
  | Code_Source_Call_Verification_Refused
  | Code_Source_Call_Verification_Pending

definition code_verify_source_no_proof_call ::
  "code_source_call_signing_config \<Rightarrow> (wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> bool) \<Rightarrow>
    wire_bytes \<Rightarrow> registered_identity \<Rightarrow> session_proof \<Rightarrow> nat \<Rightarrow> endpoint_use \<Rightarrow>
    client_call_id \<Rightarrow> code_source_product_action \<Rightarrow> code_source_call_verification" where
  "code_verify_source_no_proof_call signing_config verify_curve bytes identity proof target operation call_id action =
    (if length bytes > source_signing_max_frame signing_config then Code_Source_Call_Verification_Refused
     else case map_of (source_signing_peers signing_config) (identity_principal identity) of None \<Rightarrow> Code_Source_Call_Verification_Refused
      | Some peer \<Rightarrow> (case decode_wire_packet bytes of None \<Rightarrow> Code_Source_Call_Verification_Refused | Some packet \<Rightarrow>
        let core = packet_core packet in
        if \<not> code_source_signature_header signing_config peer identity proof target core \<or>
           \<not> verify_curve (source_signing_public_key peer) (envelope_signing_bytes core) (packet_signature packet) \<or>
           source_signing_max_nesting signing_config = 0
        then Code_Source_Call_Verification_Refused
        else if wire_message_family core = Wire_Query \<and> wire_opcode (wire_operation_body core) = 8
        then Code_Source_Call_Verification_Pending
        else (case action of Code_Source_Ordinary_Action expected \<Rightarrow>
          (case code_decode_ordinary core of Code_Ordinary_Refused reason \<Rightarrow> Code_Source_Call_Verification_Refused
           | Code_Ordinary_Ready native credential versions command \<Rightarrow>
              if \<not> code_source_no_proof_ordinary_call command then Code_Source_Call_Verification_Pending
              else if operation \<notin> {Execute_Ordinary,Read_Receipt} \<or>
                   call_id \<noteq> native_id native \<or>
                   expected \<noteq> code_source_payload_from_native core native credential versions command \<or>
                   source_payload_session expected \<noteq> proof_session proof \<or>
                   \<not> code_source_session_call_grant peer (proof_session proof) target operation
                      (source_binding_asset (source_payload_binding expected))
              then Code_Source_Call_Verification_Refused else Code_Source_Call_Verified)
          | _ \<Rightarrow> Code_Source_Call_Verification_Pending)))"

lemma a_source_call_grant_is_for_the_exact_session_target_and_asset:
  assumes "code_source_session_call_grant peer session target operation asset"
  obtains endpoints grants
  where "map_of (source_signing_sessions peer) session = Some endpoints"
    "map_of endpoints target = Some grants"
    "(operation = Execute_Ordinary \<and> asset \<in> source_call_execute_assets grants) \<or>
       (operation = Read_Receipt \<and> asset \<in> source_call_receipt_assets grants)"
  using assms
  by (auto simp: code_source_session_call_grant_def split: option.splits if_splits)

theorem a_verified_source_no_proof_call_consumes_the_original_packet_and_whole_payload:
  assumes verified: "code_verify_source_no_proof_call signing_config verify_curve bytes identity proof target operation call_id action = Code_Source_Call_Verified"
  obtains peer :: code_source_signing_peer and packet :: wire_packet and native :: wire_native_call
    and credential :: "product_lock_credential option" and versions :: "(nat \<times> nat) list"
    and command :: ordinary_wire_command
  where "map_of (source_signing_peers signing_config) (identity_principal identity) = Some peer"
    "decode_wire_packet bytes = Some packet"
    "code_source_signature_header signing_config peer identity proof target (packet_core packet)"
    "verify_curve (source_signing_public_key peer) (envelope_signing_bytes (packet_core packet)) (packet_signature packet)"
    "code_decode_ordinary (packet_core packet) = Code_Ordinary_Ready native credential versions command"
    "code_source_no_proof_ordinary_call command"
    "call_id = native_id native"
    "action = Code_Source_Ordinary_Action (code_source_payload_from_native (packet_core packet) native credential versions command)"
    "source_payload_session (code_source_payload_from_native (packet_core packet) native credential versions command) = proof_session proof"
    "code_source_session_call_grant peer (proof_session proof) target operation (native_asset native)"
proof -
  obtain peer
    where peer: "map_of (source_signing_peers signing_config) (identity_principal identity) = Some peer"
    using verified
    by (cases "map_of (source_signing_peers signing_config) (identity_principal identity)")
       (auto simp: code_verify_source_no_proof_call_def split: if_splits)
  obtain packet
    where packet: "decode_wire_packet bytes = Some packet"
    using verified peer
    by (cases "decode_wire_packet bytes")
       (auto simp: code_verify_source_no_proof_call_def split: if_splits)
  let ?core = "packet_core packet"
  have header: "code_source_signature_header signing_config peer identity proof target ?core"
    and curve: "verify_curve (source_signing_public_key peer) (envelope_signing_bytes ?core) (packet_signature packet)"
    and nesting: "source_signing_max_nesting signing_config \<noteq> 0"
    and direct: "\<not> (wire_message_family ?core = Wire_Query \<and> wire_opcode (wire_operation_body ?core) = 8)"
    using verified peer packet
    by (auto simp: code_verify_source_no_proof_call_def Let_def
      split: code_source_product_action.splits code_ordinary_result.splits if_splits)
  obtain expected
    where action: "action = Code_Source_Ordinary_Action expected"
    using verified peer packet header curve nesting direct
    by (cases action) (auto simp: code_verify_source_no_proof_call_def Let_def split: if_splits)
  obtain native credential versions command
    where decoded: "code_decode_ordinary ?core = Code_Ordinary_Ready native credential versions command"
    using verified peer packet header curve nesting direct action
    by (cases "code_decode_ordinary ?core") (auto simp: code_verify_source_no_proof_call_def Let_def split: if_splits)
  have domain: "code_source_no_proof_ordinary_call command"
    using verified peer packet header curve nesting direct action decoded
    by (auto simp: code_verify_source_no_proof_call_def Let_def split: if_splits)
  have selected: "call_id = native_id native"
    and payload: "expected = code_source_payload_from_native ?core native credential versions command"
    and session: "source_payload_session expected = proof_session proof"
    and grant: "code_source_session_call_grant peer (proof_session proof) target operation
      (source_binding_asset (source_payload_binding expected))"
    using verified peer packet header curve nesting direct action decoded domain
    by (auto simp: code_verify_source_no_proof_call_def Let_def split: if_splits)
  have fixed_action: "action = Code_Source_Ordinary_Action (code_source_payload_from_native ?core native credential versions command)"
    using action payload by simp
  have fixed_session: "source_payload_session (code_source_payload_from_native ?core native credential versions command) = proof_session proof"
    using session payload by simp
  have fixed_grant: "code_source_session_call_grant peer (proof_session proof) target operation (native_asset native)"
    using grant by (simp add: payload code_source_payload_from_native_def code_source_binding_from_native_def)
  show thesis by (rule that[OF peer packet header curve decoded domain selected fixed_action fixed_session fixed_grant])
qed

theorem source_no_proof_verification_cannot_substitute_the_funding_owner_or_signed_command:
  assumes verified: "code_verify_source_no_proof_call signing_config verify_curve bytes identity proof target operation call_id
      (Code_Source_Ordinary_Action expected) = Code_Source_Call_Verified"
  obtains packet :: wire_packet and native :: wire_native_call and credential versions command
  where "decode_wire_packet bytes = Some packet"
    "code_decode_ordinary (packet_core packet) = Code_Ordinary_Ready native credential versions command"
    "source_binding_owner (source_payload_binding expected) = native_funding_owner native"
    "source_payload_command expected = command"
    "source_payload_credential expected = credential"
    "source_payload_versions expected = versions"
proof -
  obtain peer packet native credential versions command
    where peer: "map_of (source_signing_peers signing_config) (identity_principal identity) = Some peer"
      and decoded: "decode_wire_packet bytes = Some packet"
      and header: "code_source_signature_header signing_config peer identity proof target (packet_core packet)"
      and curve: "verify_curve (source_signing_public_key peer) (envelope_signing_bytes (packet_core packet)) (packet_signature packet)"
      and operands: "code_decode_ordinary (packet_core packet) = Code_Ordinary_Ready native credential versions command"
      and domain: "code_source_no_proof_ordinary_call command"
      and selected: "call_id = native_id native"
      and action: "Code_Source_Ordinary_Action expected =
        Code_Source_Ordinary_Action (code_source_payload_from_native (packet_core packet) native credential versions command)"
      and session: "source_payload_session (code_source_payload_from_native (packet_core packet) native credential versions command) = proof_session proof"
      and grant: "code_source_session_call_grant peer (proof_session proof) target operation (native_asset native)"
    by (rule a_verified_source_no_proof_call_consumes_the_original_packet_and_whole_payload[OF verified])
  have same: "expected = code_source_payload_from_native (packet_core packet) native credential versions command"
    using action by simp
  have owner: "source_binding_owner (source_payload_binding expected) = native_funding_owner native"
    and command: "source_payload_command expected = command"
    and credential: "source_payload_credential expected = credential"
    and versions: "source_payload_versions expected = versions"
    by (simp_all add: same code_source_payload_from_native_def code_source_binding_from_native_def)
  show thesis by (rule that[OF decoded operands owner command credential versions])
qed

lemma a_source_signature_header_preserves_the_registered_peer_and_same_typed_proof:
  assumes "code_source_signature_header signing_config peer identity proof target core"
  shows "source_signing_identity peer = identity"
    "wire_principal core = identity_principal identity"
    "wire_source_domain core = identity_domain identity"
    "wire_key_number core = source_signing_key_number peer"
    "wire_authority_epoch core = proof_epoch proof"
    "proof_epoch proof = source_signing_epoch signing_config"
    "wire_target_domain core = target" "target \<in> source_signing_targets signing_config"
  using assms by (auto simp: code_source_signature_header_def)

lemma a_source_no_proof_command_requires_no_terminal_attestation_blob:
  assumes decoded: "code_decode_ordinary core = Code_Ordinary_Ready native credential versions command"
    and domain: "code_source_no_proof_ordinary_call command"
  shows "native_proof_bytes native = []"
proof -
  have allowed: "code_ordinary_proofs_allowed native command"
    by (rule every_source_ordinary_result_retains_the_existing_decoded_operands(6)[OF decoded])
  have count: "code_ordinary_proof_count command = 0" using domain by (cases command) simp_all
  show ?thesis using allowed count by (simp add: code_ordinary_proofs_allowed_def)
qed

text \<open>
  This is the no-proof ordinary Signed::Call slice of Ed25519Security.verify
  (ed25519.rs 570..679). Source SessionGrants are finite session/target rows,
  with asset membership for Execute and Receipt. The exact packet signature
  primitive receives the selected peer public key and envelope preimage.
  The fixed decoder reconstructs and compares the entire source CallPayload,
  including owner and signed command generation; no expected outcome or
  observed product poststate is accepted as a classifier input.
  Nested Receipt, proof-bearing ordinary, Legal and Spend are Pending and
  must not be counted as false/successful full-provider coverage. This helper
  does not repeat ingress TTL checks: the signed TTL is inside the verified
  preimage, while delivery time belongs to the surrounding source path.
  The raw signing_config/maps and curve result still require actual source/ABI
  correspondence. This file does not adopt a whole-provider=true assumption.
\<close>

end
