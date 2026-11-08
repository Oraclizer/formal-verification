theory Wire_Response_Fixed_Receiver
  imports Wire_Response_Fixed_Constructor Wire_Response_Fixed_Original
begin

record response_fixed_client_boundary =
  response_client_scope :: wire_boundary
  response_client_public_key :: wire_bytes
  response_client_max_nesting :: nat

definition response_fixed_encode_for_received_original where
  "response_fixed_encode_for_received_original hash curve_sign signing_key curve_verify config channel site
      parameters_clock signing_clock original_bytes observation frame_limit =
    (case response_fixed_original_preflight config channel site curve_verify frame_limit original_bytes of
       Inl reason \<Rightarrow> Inl (Response_Fixed_Encoding_Refused reason)
     | Inr (original,call_id) \<Rightarrow> response_fixed_encode hash curve_sign signing_key curve_verify config channel
         parameters_clock signing_clock (packet_core original) call_id observation frame_limit)"

theorem response_fixed_received_original_cannot_be_replaced_at_the_encoding_interface:
  assumes "response_fixed_encode_for_received_original hash curve_sign signing_key curve_verify config channel site
      parameters_clock signing_clock original_bytes observation frame_limit = Inr emission"
  obtains original call_id
  where
    "response_fixed_original_preflight config channel site curve_verify frame_limit original_bytes = Inr (original,call_id)"
    "response_emission_original emission = packet_core original"
    "response_fixed_raw_core original_bytes = Some (encode_wire_core (response_emission_original emission))"
proof -
  obtain original call_id where selected:
      "response_fixed_original_preflight config channel site curve_verify frame_limit original_bytes = Inr (original,call_id)"
    and encoded: "response_fixed_encode hash curve_sign signing_key curve_verify config channel parameters_clock signing_clock
        (packet_core original) call_id observation frame_limit = Inr emission"
    using assms by (auto simp: response_fixed_encode_for_received_original_def split: sum.splits prod.splits)
  have same: "response_emission_original emission = packet_core original"
    by (rule response_fixed_encoding_has_actual_source_getter_preimage_and_postcheck_evidence[OF encoded]) blast
  have raw: "response_fixed_raw_core original_bytes = Some (encode_wire_core (response_emission_original emission))"
    using response_fixed_preflight_selects_one_canonical_original_and_exact_peer_preimage(2)[OF selected] same by simp
  show thesis by (rule that[OF selected same raw])
qed

definition response_fixed_received_status where
  "response_fixed_received_status result =
    (case result of (call_id,kind,number,position) \<Rightarrow>
      code_decode_response_status kind number (position \<noteq> None))"

definition response_fixed_admit where
  "response_fixed_admit curve_verify channel current expected bytes =
    (let scope = response_client_scope current in
     if response_channel_local channel \<noteq> boundary_target scope \<or>
        response_channel_remote channel \<noteq> boundary_source scope \<or>
        response_channel_deployment channel \<noteq> boundary_deployment scope \<or>
        boundary_now scope > response_channel_expires channel \<or>
        response_client_public_key current \<noteq> response_channel_remote_key channel
     then Inl Invalid_Wire_Source
     else case code_check_declared_version bytes (boundary_max_frame scope) of Some reason \<Rightarrow> Inl reason
      | None \<Rightarrow> (case decode_wire_packet bytes of None \<Rightarrow> Inl Invalid_Wire_Format | Some packet \<Rightarrow>
          case code_admit_packet
            (\<lambda>core preimage signature. curve_verify (response_client_public_key current) preimage signature)
            packet (scope\<lparr>boundary_profile := response_channel_profile channel\<rparr>) of Some reason \<Rightarrow> Inl reason
          | None \<Rightarrow> case response_fixed_validate (response_client_max_nesting current) (packet_core expected) packet of
              Inl reason \<Rightarrow> Inl reason
            | Inr result \<Rightarrow> Inr (result,response_fixed_received_status result)))"

lemma response_fixed_admission_keeps_the_actual_client_boundary_and_parsed_value:
  assumes "response_fixed_admit curve_verify channel current expected bytes = Inr (result,status)"
  obtains packet where "decode_wire_packet bytes = Some packet"
    "response_channel_local channel = boundary_target (response_client_scope current)"
    "response_channel_remote channel = boundary_source (response_client_scope current)"
    "response_channel_deployment channel = boundary_deployment (response_client_scope current)"
    "boundary_now (response_client_scope current) \<le> response_channel_expires channel"
    "response_client_public_key current = response_channel_remote_key channel"
    "code_admit_packet (\<lambda>core preimage signature. curve_verify (response_client_public_key current) preimage signature)
       packet ((response_client_scope current)\<lparr>boundary_profile := response_channel_profile channel\<rparr>) = None"
    "response_fixed_validate (response_client_max_nesting current) (packet_core expected) packet = Inr result"
    "status = response_fixed_received_status result"
  using assms by (auto simp: response_fixed_admit_def Let_def split: option.splits sum.splits if_splits)

theorem response_fixed_client_admission_verifies_the_exact_received_preimage_with_the_current_peer:
  assumes admitted: "response_fixed_admit curve_verify channel current expected bytes = Inr (result,status)"
  obtains packet where "decode_wire_packet bytes = Some packet"
    "curve_verify (response_channel_remote_key channel)
      (envelope_signing_bytes (packet_core packet)) (packet_signature packet)"
proof -
  obtain packet where parsed: "decode_wire_packet bytes = Some packet"
    and key: "response_client_public_key current = response_channel_remote_key channel"
    and gate: "code_admit_packet (\<lambda>core preimage signature. curve_verify (response_client_public_key current) preimage signature)
       packet ((response_client_scope current)\<lparr>boundary_profile := response_channel_profile channel\<rparr>) = None"
    by (rule response_fixed_admission_keeps_the_actual_client_boundary_and_parsed_value[OF admitted]) blast
  have verified: "curve_verify (response_channel_remote_key channel)
      (envelope_signing_bytes (packet_core packet)) (packet_signature packet)"
    using gate key by (auto simp: code_admit_packet_def Let_def split: option.splits if_splits)
  show thesis by (rule that[OF parsed verified])
qed

lemma response_fixed_original_byte_conflict_is_a_replay_refusal_after_shape_and_caller:
  assumes "response_fixed_parse_response fuel (packet_core packet) = Inr viewed"
    "code_response_caller original = Inr call_id"
    "response_decoded_original_bytes viewed \<noteq> encode_wire_core original"
  shows "response_fixed_validate (Suc fuel) original packet = Inl Conflicting_Wire_Replay"
proof -
  obtain decoded where actual_expected: "response_fixed_expected_decode original = Inr decoded"
    by (rule response_fixed_existing_caller_success_has_an_actual_expected_decoding[OF assms(2)]) blast
  show ?thesis
    using assms(1,3) actual_expected
    by (simp add: response_fixed_validate_def)
qed

theorem response_fixed_client_debit_admission_consumes_the_hol_response_relation:
  assumes admitted: "response_fixed_admit curve_verify channel current expected bytes = Inr (result,status)"
    and depth: "response_client_max_nesting current = Suc (Suc fuel)"
    and expected: "wire_core_wellformed (packet_core expected)"
    and family: "wire_message_family (packet_core expected) = Wire_State_Sync"
    and operation: "wire_opcode (wire_operation_body (packet_core expected)) = 1"
    and decoded: "code_decode_ordinary (packet_core expected) = Code_Ordinary_Ready native credential versions (Wire_Debit generation)"
  shows "map_option (code_correlate_reference_response (packet_core expected)) (decode_wire_packet bytes) = Some (Some result)"
proof -
  obtain packet where parsed: "decode_wire_packet bytes = Some packet"
    and checked: "response_fixed_validate (response_client_max_nesting current) (packet_core expected) packet = Inr result"
    by (rule response_fixed_admission_keeps_the_actual_client_boundary_and_parsed_value[OF admitted]) blast
  obtain call_id kind number position where result: "result = (call_id,kind,number,position)"
    by (cases result rule: prod_cases4) auto
  have correlated: "code_correlate_reference_response (packet_core expected) packet = Some result"
    unfolding result
    by (rule response_fixed_direct_debit_validation_consumes_the_existing_hol_correlation[OF expected family operation decoded])
      (use checked depth result in simp)
  show ?thesis by (simp add: parsed correlated)
qed

lemma response_fixed_unknown_status_remains_a_category_observation:
  assumes "\<not> code_known_response_number number"
  shows "response_fixed_received_status (call_id,kind,number,position) =
    (if kind = Recorded_Result \<or> position = None then Some (Code_Unknown_Response kind number) else None)"
  using assms by (simp add: response_fixed_received_status_def
    an_unknown_number_is_accepted_only_as_its_declared_category)

theorem response_fixed_client_admission_always_has_a_typed_known_or_unknown_status:
  assumes "response_fixed_admit curve_verify channel current expected bytes = Inr (result,status)"
  shows "status \<noteq> None"
proof -
  obtain packet where checked:
      "response_fixed_validate (response_client_max_nesting current) (packet_core expected) (packet::wire_packet) = Inr result"
    and status: "status = response_fixed_received_status result"
    by (rule response_fixed_admission_keeps_the_actual_client_boundary_and_parsed_value[OF assms]) blast
  show ?thesis using checked status
    by (cases "response_client_max_nesting current"; cases result rule: prod_cases4)
      (auto simp: response_fixed_validate_def response_fixed_received_status_def
        split: option.splits sum.splits if_splits)
qed

text \<open>
  Client response admission has its own Channel and current Boundary/public
  key/nesting projection. It is never identified with the server signer config.
  Original and response signatures bind the exact canonical ENVELOPE preimages;
  no scalar verified-response or validated-whole-path input is accepted.
  Unknown codes remain Code_Unknown_Response observations and are not promoted
  to known product outcomes. The direct Debit consumer is the bounded first
  correlation slice, not a retained-state provenance or whole resolver theorem.
\<close>

end
