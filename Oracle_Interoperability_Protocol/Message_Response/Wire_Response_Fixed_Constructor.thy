theory Wire_Response_Fixed_Constructor
  imports Wire_Response_Fixed_Validation
begin

datatype response_fixed_encoding_error =
    Response_Fixed_Encoding_Refused wire_refusal | Response_Fixed_Signature_Unavailable

record response_fixed_emission =
  response_emission_bytes :: wire_bytes
  response_emission_packet :: wire_packet
  response_emission_original :: wire_core
  response_emission_converted :: "client_call_id \<times> reference_response_kind \<times> nat \<times> nat option"
  response_emission_verified :: "client_call_id \<times> reference_response_kind \<times> nat \<times> nat option"
  response_emission_parameters :: response_fixed_parameters
  response_emission_binding_preimage :: wire_bytes
  response_emission_signing_preimage :: wire_bytes

definition response_fixed_post_boundary where
  "response_fixed_post_boundary channel parameters frame_limit =
    \<lparr>boundary_profile = response_channel_profile channel,boundary_deployment = response_channel_deployment channel,
      boundary_source = response_channel_local channel,boundary_target = response_channel_remote channel,
      boundary_principal = response_parameter_principal parameters,boundary_key = response_parameter_key parameters,
      boundary_epoch = response_parameter_epoch parameters,boundary_route_scope = response_parameter_route parameters,
      boundary_now = response_parameter_issued parameters,boundary_asset_ttl_floor = 0,boundary_future_skew = 0,
      boundary_max_frame = frame_limit,boundary_version_floor = 6,boundary_critical_allowed = False,
      boundary_threshold_supported = False\<rparr>"

definition response_fixed_encode where
  "response_fixed_encode hash curve_sign signing_key curve_verify config channel parameters_clock signing_clock
      original call_id observation frame_limit =
    (case response_fixed_words call_id (response_fixed_result observation) of None \<Rightarrow> Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Format)
     | Some (kind,number,position,words) \<Rightarrow>
       case response_fixed_atomicity channel of None \<Rightarrow> Inl (Response_Fixed_Encoding_Refused Unsupported_Wire_Version)
        | Some atomicity \<Rightarrow>
          let binding_preimage = response_fixed_binding_preimage (encode_wire_core original) atomicity words in
          case response_fixed_parameters_from hash config channel parameters_clock (hash binding_preimage) of
            None \<Rightarrow> Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Source)
          | Some parameters \<Rightarrow>
            if response_parameter_issued parameters > response_channel_expires channel then Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Source)
            else let core = response_fixed_core channel parameters atomicity words (encode_wire_core original) in
              case code_typed_encode_core core of None \<Rightarrow> Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Format)
              | Some core_bytes \<Rightarrow>
                if length core_bytes \<ge> 2^32 then Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Format)
                else let signing_preimage = envelope_signing_bytes core in
                  case response_fixed_sign curve_sign signing_key config signing_clock signing_preimage of
                    None \<Rightarrow> Inl Response_Fixed_Signature_Unavailable
                  | Some signature \<Rightarrow>
                    let packet = \<lparr>packet_core = core,packet_signature = signature\<rparr> in
                    case code_encode_packet packet of None \<Rightarrow> Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Format)
                    | Some encoded \<Rightarrow>
                      if length encoded > frame_limit then Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Format)
                      else case decode_wire_packet encoded of None \<Rightarrow> Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Format)
                      | Some parsed \<Rightarrow>
                        case code_admit_packet (\<lambda>core bytes signature. curve_verify (response_channel_local_key channel) bytes signature)
                           parsed (response_fixed_post_boundary channel parameters frame_limit) of
                          Some reason \<Rightarrow> Inl (Response_Fixed_Encoding_Refused reason)
                        | None \<Rightarrow> case response_fixed_validate 2 original parsed of
                            Inl reason \<Rightarrow> Inl (Response_Fixed_Encoding_Refused reason)
                          | Inr verified \<Rightarrow> Inr \<lparr>response_emission_bytes = encoded,response_emission_packet = parsed,
                              response_emission_original = original,response_emission_converted = (call_id,kind,number,position),
                              response_emission_verified = verified,response_emission_parameters = parameters,
                              response_emission_binding_preimage = binding_preimage,response_emission_signing_preimage = signing_preimage\<rparr>)"

lemma response_fixed_encoding_has_actual_source_getter_preimage_and_postcheck_evidence:
  assumes "response_fixed_encode hash curve_sign signing_key curve_verify config channel parameters_clock signing_clock
      original call_id observation frame_limit = Inr emission"
  obtains kind number position words atomicity parameters core signature packet encoded
  where
    "response_fixed_words call_id (response_fixed_result observation) = Some (kind,number,position,words)"
    "response_fixed_atomicity channel = Some atomicity"
    "response_emission_binding_preimage emission = response_fixed_binding_preimage (encode_wire_core original) atomicity words"
    "response_fixed_parameters_from hash config channel parameters_clock
       (hash (response_emission_binding_preimage emission)) = Some parameters"
    "response_emission_parameters emission = parameters"
    "core = response_fixed_core channel parameters atomicity words (encode_wire_core original)"
    "response_emission_signing_preimage emission = envelope_signing_bytes core"
    "response_fixed_sign curve_sign signing_key config signing_clock (envelope_signing_bytes core) = Some signature"
    "packet = \<lparr>packet_core = core,packet_signature = signature\<rparr>"
    "code_encode_packet packet = Some encoded"
    "decode_wire_packet encoded = Some (response_emission_packet emission)"
    "response_emission_bytes emission = encoded"
    "response_emission_original emission = original"
    "response_emission_converted emission = (call_id,kind,number,position)"
    "code_admit_packet (\<lambda>core bytes signature. curve_verify (response_channel_local_key channel) bytes signature)
       (response_emission_packet emission) (response_fixed_post_boundary channel parameters frame_limit) = None"
    "response_fixed_validate 2 original (response_emission_packet emission) = Inr (response_emission_verified emission)"
  using assms by (auto simp: response_fixed_encode_def Let_def split: option.splits sum.splits prod.splits if_splits)

lemma response_fixed_typed_packet_decodes_to_the_same_source_value:
  assumes encoded: "code_encode_packet packet = Some bytes"
  shows "decode_wire_packet bytes = Some packet" "wire_packet_wellformed packet"
proof -
  have exact: "wire_packet_wellformed packet \<and> encode_wire_packet packet = bytes"
    by (rule the_typed_source_packet_encoder_discharges_the_reencoding_obligation[
      unfolded code_packet_encoder_sound_def,rule_format,OF encoded])
  show "decode_wire_packet bytes = Some packet"
    using the_exact_wire_message_decodes_from_its_canonical_bytes[OF conjunct1[OF exact]] exact by simp
  show "wire_packet_wellformed packet" using exact by simp
qed

theorem response_fixed_emission_keeps_the_actual_canonical_packet_bytes:
  assumes emitted: "response_fixed_encode hash curve_sign signing_key curve_verify config channel parameters_clock signing_clock
      original call_id observation frame_limit = Inr emission"
  shows "encode_wire_packet (response_emission_packet emission) = response_emission_bytes emission"
    "wire_packet_wellformed (response_emission_packet emission)"
proof -
  obtain encoded where parsed: "decode_wire_packet encoded = Some (response_emission_packet emission)"
    and bytes: "response_emission_bytes emission = encoded"
    by (rule response_fixed_encoding_has_actual_source_getter_preimage_and_postcheck_evidence[OF emitted]) blast
  show "encode_wire_packet (response_emission_packet emission) = response_emission_bytes emission"
    "wire_packet_wellformed (response_emission_packet emission)"
    using every_accepted_wire_message_has_exactly_the_received_bytes[OF parsed] bytes by auto
qed

theorem response_fixed_emission_sends_only_the_exact_constructed_preimage_to_the_signer:
  assumes emitted: "response_fixed_encode hash curve_sign signing_key curve_verify config channel parameters_clock signing_clock
      original call_id observation frame_limit = Inr emission"
  obtains core now signature
  where
    "packet_core (response_emission_packet emission) = core"
    "response_emission_signing_preimage emission = envelope_signing_bytes core"
    "response_fixed_unframe (response_emission_signing_preimage emission) = Some core"
    "signing_clock = Some now" "response_fixed_signable config now core"
    "curve_sign signing_key (response_emission_signing_preimage emission) = signature"
proof -
  obtain core signature packet encoded where preimage: "response_emission_signing_preimage emission = envelope_signing_bytes core"
    and signed: "response_fixed_sign curve_sign signing_key config signing_clock (envelope_signing_bytes core) = Some signature"
    and packet: "packet = \<lparr>packet_core = core,packet_signature = signature\<rparr>"
    and encoded: "code_encode_packet packet = Some encoded"
    and parsed_packet: "decode_wire_packet encoded = Some (response_emission_packet emission)"
    by (rule response_fixed_encoding_has_actual_source_getter_preimage_and_postcheck_evidence[OF emitted]) blast
  have exact_packet: "response_emission_packet emission = packet"
    using parsed_packet response_fixed_typed_packet_decodes_to_the_same_source_value(1)[OF encoded] by simp
  have domain: "wire_core_wellformed core" and width: "length (encode_wire_core core) < 256^4"
    using response_fixed_typed_packet_decodes_to_the_same_source_value(2)[OF encoded] packet
    by (auto simp: wire_packet_wellformed_def)
  have recovered: "response_fixed_unframe (envelope_signing_bytes core) = Some core"
    by (rule response_fixed_unframe_recovers_exactly_the_core_that_was_signed[OF domain width])
  obtain parsed now where framing: "response_fixed_unframe (envelope_signing_bytes core) = Some parsed"
    and clock: "signing_clock = Some now" and allowed: "response_fixed_signable config now parsed"
    and primitive: "curve_sign signing_key (envelope_signing_bytes core) = signature"
    by (rule response_fixed_sign_forwards_the_exact_framed_bytes_to_the_curve_primitive[OF signed]) blast
  have parsed_core: "parsed = core" using framing recovered by simp
  show thesis by (rule that[OF _ preimage _ clock _ _])
    (use packet exact_packet recovered allowed primitive preimage parsed_core in simp_all)
qed

theorem response_fixed_emission_returns_the_exact_converted_kind_code_and_position:
  assumes emitted: "response_fixed_encode hash curve_sign signing_key curve_verify config channel parameters_clock signing_clock
      original call_id observation frame_limit = Inr emission"
  shows "response_emission_verified emission = response_emission_converted emission"
proof -
  obtain kind number position words atomicity parameters core signature packet encoded
  where
    selected: "response_fixed_words call_id (response_fixed_result observation) = Some (kind,number,position,words)"
    and core: "core = response_fixed_core channel parameters atomicity words (encode_wire_core original)"
    and packet: "packet = \<lparr>packet_core = core,packet_signature = signature\<rparr>"
    and encoded: "code_encode_packet packet = Some encoded"
    and parsed: "decode_wire_packet encoded = Some (response_emission_packet emission)"
    and converted: "response_emission_converted emission = (call_id,kind,number,position)"
    and checked: "response_fixed_validate 2 original (response_emission_packet emission) = Inr (response_emission_verified emission)"
    by (rule response_fixed_encoding_has_actual_source_getter_preimage_and_postcheck_evidence[OF emitted]) blast
  have same_packet: "response_emission_packet emission = packet"
    using parsed response_fixed_typed_packet_decodes_to_the_same_source_value(1)[OF encoded] by simp
  have words: "code_response_words call_id kind number position = Some words"
    using selected by (cases "response_fixed_result observation")
      (auto simp: response_fixed_words_def split: option.splits prod.splits if_splits)
  have actual_words: "words = wire_words (reference_response_body call_id kind number position original)"
    by (rule source_response_words_have_the_existing_model_word_sequence(1)[OF words])
  have fixed_parse: "response_result_words words = Some (call_id,kind,number,position)"
    unfolding actual_words by (rule the_reference_response_words_recover_the_typed_result)
  obtain actual_id actual_kind actual_number actual_position where result:
      "response_emission_verified emission = (actual_id,actual_kind,actual_number,actual_position)"
    by (cases "response_emission_verified emission" rule: prod_cases4) auto
  have actual_checked: "response_fixed_validate (Suc 1) original (response_emission_packet emission) =
      Inr (actual_id,actual_kind,actual_number,actual_position)"
    using checked result by (simp only: numeral_2_eq_2 One_nat_def)
  obtain viewed where viewed: "response_fixed_parse_response 1 (packet_core (response_emission_packet emission)) = Inr viewed"
    and projected_fields: "response_decoded_id viewed = actual_id" "response_decoded_kind viewed = actual_kind"
      "response_decoded_number viewed = actual_number" "response_decoded_position viewed = actual_position"
    by (rule response_fixed_validation_keeps_the_exact_original_and_caller[OF actual_checked]) blast
  have actual_parse: "response_result_words (wire_words (wire_operation_body (packet_core (response_emission_packet emission)))) =
      Some (actual_id,actual_kind,actual_number,actual_position)"
    by (rule response_fixed_parser_preserves_the_actual_nested_fields_and_checks[OF viewed])
      (use projected_fields in blast)
  show ?thesis using actual_parse fixed_parse core packet same_packet converted result
    by (simp add: response_fixed_core_def)
qed

theorem response_fixed_emission_for_a_direct_debit_reaches_the_existing_correlation_consumer:
  assumes emitted: "response_fixed_encode hash curve_sign signing_key curve_verify config channel parameters_clock signing_clock
      original call_id observation frame_limit = Inr emission"
    and original: "wire_core_wellformed original"
    and family: "wire_message_family original = Wire_State_Sync"
    and operation: "wire_opcode (wire_operation_body original) = 1"
    and decoded: "code_decode_ordinary original = Code_Ordinary_Ready native credential versions (Wire_Debit generation)"
  shows "code_correlate_reference_response original (response_emission_packet emission) = Some (response_emission_verified emission)"
proof -
  have checked_source: "response_fixed_validate 2 original (response_emission_packet emission) = Inr (response_emission_verified emission)"
    by (rule response_fixed_encoding_has_actual_source_getter_preimage_and_postcheck_evidence[OF emitted]) blast
  have checked: "response_fixed_validate (Suc (Suc 0)) original (response_emission_packet emission) = Inr (response_emission_verified emission)"
    using checked_source by (simp only: numeral_2_eq_2)
  obtain actual_id kind number position where result:
      "response_emission_verified emission = (actual_id,kind,number,position)"
    by (cases "response_emission_verified emission" rule: prod_cases4) auto
  show ?thesis unfolding result
    by (rule response_fixed_direct_debit_validation_consumes_the_existing_hol_correlation[OF original family operation decoded])
      (use checked result in simp)
qed

text \<open>
  This is response.rs encode_response with a fixed Ed25519 signer and source
  typed encoders. No product runner or correct-response Boolean is an input.
  The actual selected Outcome is data; its retained/product provenance is a
  separate consumer obligation. The output observation augments Rust's bytes
  with projected_fields already computed on this path. Client receipt admission uses a
  separate current boundary and must not reuse this emitter boundary silently.
\<close>

end
