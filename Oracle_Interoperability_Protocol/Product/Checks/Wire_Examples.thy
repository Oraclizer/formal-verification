theory Wire_Examples
  imports Wire_Byte_Examples "../Wire_Amounts"
begin

lemma actual_wire_query_maps_to_its_exact_product_service_input:
  "decoded_wire_read_action token wire_case_core =
    Some (Invoke_Authenticated_Read token \<lparr>proof_session = 1, proof_epoch = 9\<rparr> 2
      (Current_Data (Application_Value 17) \<lparr>cut_authority_epoch = 9, cut_revision = 0\<rparr>))"
  using an_encoded_current_query_supplies_the_actual_session_cut_and_asset[of wire_case_core 1 0 17 token]
  by (simp add: wire_case_core_def wire_case_body_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    the_exact_wire_message_decodes_from_its_canonical_bytes
    every_accepted_wire_message_has_exactly_the_received_bytes
    authenticated_highest_common_version_cannot_downgrade
    deduplication_changes_only_after_the_original_canonical_signature_and_identity
    source_attestation.the_actual_product_receiver_gets_only_the_action_decoded_from_the_verified_core
    source_attestation.precommit_cancellation_cannot_create_a_wire_binding_or_product_effect
    exact_32_octet_unsigned_amount_has_no_accepted_alias
    concrete_protobuf_query_has_the_exact_signing_preimage
    actual_wire_query_maps_to_its_exact_product_service_input})
  then () else error "Unexpected oracle in the canonical wire conformance proof"
\<close>

end
