theory Wire_Code_Session_Authentication_Check
  imports Wire_Code_Session_Authentication
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      the_claim_byte_interpretation_preserves_identity_and_both_separate_crypto_byte_fields
      an_exact_json_prefix_is_the_original_prefix_and_remaining_bytes
      a_decoded_session_signature_preimage_has_the_exact_domain_and_whole_claim
      a_source_digest_or_issuer_array_is_exactly_32_octets
      source_session_authentication_keeps_the_current_record_grants_time_and_curve_inputs
      session_authentication_cannot_use_another_session_from_the_same_principal
      the_session_clock_and_token_lifetime_are_explicit_checks
      a_stale_config_epoch_cannot_authenticate_an_otherwise_signed_session})
  then () else error "Unexpected oracle in exact source session authentication"
\<close>

end
