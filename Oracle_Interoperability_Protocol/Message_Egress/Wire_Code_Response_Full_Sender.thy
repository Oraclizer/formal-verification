theory Wire_Code_Response_Full_Sender
  imports Wire_Code_Response_Full_Queries
begin

definition code_full_sender ::
  "code_response_full_context \<Rightarrow> response_fixed_observation \<Rightarrow> wire_bytes \<Rightarrow>
    code_full_hash_table \<Rightarrow> code_full_sign_table \<Rightarrow> code_full_verify_table \<Rightarrow>
    (response_fixed_encoding_error + response_fixed_emission)" where
  "code_full_sender = (\<lambda>oip_full_context oip_full_observation oip_full_original
      oip_full_hashes oip_full_signatures oip_full_verifications.
    response_fixed_encode_for_received_original (code_full_hash oip_full_hashes)
      (code_full_sign oip_full_signatures (response_channel_local_key (full_response_channel oip_full_context))) ()
      (code_full_verify oip_full_verifications)
      (full_response_config oip_full_context) (full_response_channel oip_full_context) (full_response_site oip_full_context)
      (full_parameters_clock oip_full_context) (full_signing_clock oip_full_context)
      oip_full_original oip_full_observation (full_response_frame_limit oip_full_context))"

definition code_full_boundary_sender ::
  "code_response_full_context \<Rightarrow> response_fixed_observation \<Rightarrow> wire_bytes \<Rightarrow>
    code_full_hash_table \<Rightarrow> code_full_sign_table \<Rightarrow> code_full_verify_table \<Rightarrow>
    (response_fixed_encoding_error + response_fixed_emission)" where
  "code_full_boundary_sender = (\<lambda>oip_full_context oip_full_observation oip_full_bytes
      oip_full_hashes oip_full_signatures oip_full_verifications.
    case decode_wire_packet oip_full_bytes of None \<Rightarrow> Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Format)
     | Some oip_full_original \<Rightarrow>
       case code_response_caller (packet_core oip_full_original) of
         Inl oip_full_reason \<Rightarrow> Inl (Response_Fixed_Encoding_Refused oip_full_reason)
       | Inr oip_full_call \<Rightarrow>
         response_fixed_encode (code_full_hash oip_full_hashes)
           (code_full_sign oip_full_signatures (response_channel_local_key (full_response_channel oip_full_context))) ()
           (code_full_verify oip_full_verifications)
           (full_response_config oip_full_context) (full_response_channel oip_full_context)
           (full_parameters_clock oip_full_context) (full_signing_clock oip_full_context)
           (packet_core oip_full_original) oip_full_call oip_full_observation (full_response_frame_limit oip_full_context))"

definition code_full_kind_number :: "reference_response_kind \<Rightarrow> nat" where
  "code_full_kind_number = (\<lambda>oip_full_kind. case oip_full_kind of
    Recorded_Result \<Rightarrow> 1 | Delivery_Refusal \<Rightarrow> 2 | Validation_Refusal \<Rightarrow> 3)"

definition code_full_result_row ::
  "(client_call_id \<times> reference_response_kind \<times> nat \<times> nat option) \<Rightarrow> nat list" where
  "code_full_result_row = (\<lambda>(oip_full_call,oip_full_kind,oip_full_number,oip_full_position).
    [fst oip_full_call,snd oip_full_call,code_full_kind_number oip_full_kind,oip_full_number,
      if oip_full_position = None then 0 else 1,(case oip_full_position of None \<Rightarrow> 0 | Some oip_full_optional_position \<Rightarrow> oip_full_optional_position)])"

definition code_full_clock_row :: "code_response_full_context \<Rightarrow> nat list" where
  "code_full_clock_row = (\<lambda>oip_full_context.
    (case full_parameters_clock oip_full_context of None \<Rightarrow> [0,0] | Some oip_full_now \<Rightarrow> [1,oip_full_now]) @
    (case full_signing_clock oip_full_context of None \<Rightarrow> [0,0] | Some oip_full_now \<Rightarrow> [1,oip_full_now]))"

definition code_full_emission_rows ::
  "code_response_full_context \<Rightarrow> code_full_hash_table \<Rightarrow> response_fixed_emission \<Rightarrow> nat list list" where
  "code_full_emission_rows = (\<lambda>oip_full_context oip_full_hashes oip_full_emission.
    let oip_full_parameters = response_emission_parameters oip_full_emission;
        oip_full_packet = response_emission_packet oip_full_emission;
        oip_full_binding_message = response_emission_binding_preimage oip_full_emission;
        oip_full_binding = code_full_hash oip_full_hashes oip_full_binding_message;
        oip_full_uuid_message = response_fixed_uuid_preimage (full_response_config oip_full_context)
          oip_full_binding (response_parameter_issued oip_full_parameters)
    in [code_full_result_row (response_emission_converted oip_full_emission),
        code_full_result_row (response_emission_verified oip_full_emission),
        wire_words (wire_operation_body (packet_core oip_full_packet)),
        encode_wire_core (response_emission_original oip_full_emission),
        oip_full_binding_message,oip_full_binding,oip_full_uuid_message,
        code_full_hash oip_full_hashes oip_full_uuid_message,response_parameter_uuid oip_full_parameters,
        encode_wire_core (packet_core oip_full_packet),response_emission_signing_preimage oip_full_emission,
        packet_signature oip_full_packet,response_emission_bytes oip_full_emission,
        [response_parameter_principal oip_full_parameters,response_parameter_key oip_full_parameters,
         response_parameter_epoch oip_full_parameters,response_parameter_issued oip_full_parameters,
         response_parameter_ttl oip_full_parameters,response_parameter_route oip_full_parameters],
        code_full_clock_row oip_full_context])"

definition code_full_pack_sender ::
  "code_response_full_context \<Rightarrow> code_full_hash_table \<Rightarrow>
    (response_fixed_encoding_error + response_fixed_emission) \<Rightarrow> (integer \<times> integer list list)" where
  "code_full_pack_sender = (\<lambda>oip_full_context oip_full_hashes oip_full_result.
    case oip_full_result of
      Inl (Response_Fixed_Encoding_Refused oip_full_reason) \<Rightarrow>
        (integer_of_nat (code_transport_refusal_number oip_full_reason),[])
    | Inl Response_Fixed_Signature_Unavailable \<Rightarrow> (51,[])
    | Inr oip_full_emission \<Rightarrow>
        (0,map (map integer_of_nat) (code_full_emission_rows oip_full_context oip_full_hashes oip_full_emission)))"

definition code_full_without_result ::
  "code_response_full_context \<Rightarrow> wire_bytes \<Rightarrow> code_full_verify_table \<Rightarrow> (integer \<times> integer list list)" where
  "code_full_without_result = (\<lambda>oip_full_context oip_full_bytes oip_full_verifications.
    case code_full_original_selection oip_full_context oip_full_bytes oip_full_verifications of
      (oip_full_selected,oip_full_queries) \<Rightarrow>
        if oip_full_queries \<noteq> [] then (-2,[])
        else case response_fixed_original_preflight (full_response_config oip_full_context)
            (full_response_channel oip_full_context) (full_response_site oip_full_context)
            (code_full_verify oip_full_verifications) (full_response_frame_limit oip_full_context) oip_full_bytes of
          Inl oip_full_reason \<Rightarrow> (integer_of_nat (code_transport_refusal_number oip_full_reason),[])
        | Inr oip_full_original \<Rightarrow> (-1,[]))"

definition code_full_sender_integer ::
  "bool \<Rightarrow> integer list list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow> (integer \<times> integer list list)" where
  "code_full_sender_integer = (\<lambda>oip_full_include_original oip_full_rows oip_full_mode oip_full_reply
      oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows.
    case code_full_sender_input oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained
        oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows of None \<Rightarrow> (-1,[])
     | Some (oip_full_context,oip_full_observation,oip_full_bytes,oip_full_hashes,oip_full_signatures,oip_full_verifications) \<Rightarrow>
       (case oip_full_observation of None \<Rightarrow>
          (if oip_full_include_original then code_full_without_result oip_full_context oip_full_bytes oip_full_verifications
           else (-1,[]))
        | Some oip_full_actual \<Rightarrow>
          if code_full_sender_queries oip_full_include_original oip_full_context oip_full_actual oip_full_bytes
              oip_full_hashes oip_full_signatures oip_full_verifications \<noteq> [] then (-2,[])
          else code_full_pack_sender oip_full_context oip_full_hashes
            (if oip_full_include_original then code_full_sender oip_full_context oip_full_actual oip_full_bytes
               oip_full_hashes oip_full_signatures oip_full_verifications
             else code_full_boundary_sender oip_full_context oip_full_actual oip_full_bytes
               oip_full_hashes oip_full_signatures oip_full_verifications)))"

definition code_response_egress_flat_oracle where
  "code_response_egress_flat_oracle = code_full_sender_integer True"

definition code_response_encode_boundary_flat_oracle where
  "code_response_encode_boundary_flat_oracle = code_full_sender_integer False"

text \<open>
  The True/False parameter is internal role selection behind two distinct
  exported names. It is never a caller-supplied consumer success Boolean.
  Both entries independently decode the typed result IR. Only the whole
  sender includes the original preflight; the boundary sender matches the
  source enum encoder fixture and does not establish dispatcher provenance.
  Refusal ordering comes from the existing Fixed entry, not the catalog.
  Full-only mode3 means that no product boundary result exists. It runs
  only the actual preflight: refused noncalls/filter cases retain their
  original errors, while a ready call with no result is incomplete metadata.
  No dummy Outcome is constructed for those absent-result paths.
\<close>

end
