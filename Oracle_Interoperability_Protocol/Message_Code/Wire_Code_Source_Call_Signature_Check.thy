theory Wire_Code_Source_Call_Signature_Check
  imports Wire_Code_Source_Call_Signature
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      a_source_call_grant_is_for_the_exact_session_target_and_asset
      a_verified_source_no_proof_call_consumes_the_original_packet_and_whole_payload
      source_no_proof_verification_cannot_substitute_the_funding_owner_or_signed_command
      a_source_signature_header_preserves_the_registered_peer_and_same_typed_proof
      a_source_no_proof_command_requires_no_terminal_attestation_blob})
  then () else error "Unexpected oracle in fixed source signature adapter"
\<close>

end
