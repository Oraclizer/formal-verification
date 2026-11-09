theory Response_Egress_V061_Packet
  imports Response_Egress_V061_Fields
begin

definition response_v061_packet_caller where
  "response_v061_packet_caller raw = (case sync_decode_packet raw of None \<Rightarrow> Inl Invalid_Wire_Format
    | Some packet \<Rightarrow> map_sum id (Pair packet) (response_v061_original_caller (packet_core packet)))"

definition response_v061_original_preflight where
  "response_v061_original_preflight context accept_sync accept_current selected_mode verify raw =
    (let channel = full_response_channel context; profile = response_channel_profile channel;
         config = full_response_config context; site = full_response_site context;
         frame_limit = full_response_frame_limit context
     in if negotiated_version profile \<noteq> 6 \<or> \<not> code_profile_allows profile Wire_Ack 2
        then Inl Unsupported_Wire_Version
        else if response_site_ordered_control site = None \<or>
          response_site_security_ordered_profile site \<noteq> Some (response_site_profile site) \<or>
          \<not> response_fixed_channel_current config channel \<or> response_channel_deployment channel \<noteq> fst (response_site_profile site)
        then Inl Invalid_Wire_Source
        else case code_check_declared_version raw frame_limit of Some reason \<Rightarrow> Inl reason
         | None \<Rightarrow> (case sync_decode_packet raw of None \<Rightarrow> Inl Invalid_Wire_Format | Some packet \<Rightarrow>
           let core = packet_core packet in
           if code_check_operation (response_v061_accepts accept_sync accept_current) core \<noteq> None then Inl Unsupported_Wire_Version
           else if wire_version core \<noteq> negotiated_version profile \<or> wire_deployment core \<noteq> response_channel_deployment channel \<or>
             wire_source_domain core \<noteq> response_channel_remote channel \<or> wire_target_domain core \<noteq> response_channel_local channel
           then Inl Invalid_Wire_Source
           else case response_v061_original_caller core of Inl reason \<Rightarrow> Inl reason | Inr call \<Rightarrow>
             (case code_response_measurement selected_mode (length (encode_wire_core core)) of Inl reason \<Rightarrow> Inl reason
              | Inr measured \<Rightarrow> if measured > frame_limit then Inl Invalid_Wire_Format
                else case response_fixed_original_signature verify channel packet of Some reason \<Rightarrow> Inl reason
                 | None \<Rightarrow> Inr (packet,call))))"

lemma response_v061_original_preflight_keeps_old_configured_operations:
  assumes decoded: "decode_wire_packet raw = Some packet"
    and op: "sync_operation (packet_core packet) \<notin>
      {(Wire_Lock,7),(Wire_State_Sync,7),(Wire_Query,9),(Wire_Query,8),(Wire_Ack,2)}"
    and mode: "selected_mode = response_fixed_atomicity (full_response_channel context)"
  shows "response_v061_original_preflight context accept_sync accept_current selected_mode verify raw =
    response_fixed_original_preflight (full_response_config context) (full_response_channel context)
      (full_response_site context) verify (full_response_frame_limit context) raw"
proof -
  have legacy_op: "code_check_operation (response_v061_accepts accept_sync accept_current) (packet_core packet) =
      code_check_operation code_reference_accepts (packet_core packet)"
    using op by (auto simp: sync_operation_def code_check_operation_def response_v061_accepts_def reference_accepts_write_def)
  have v061_caller: "response_v061_original_caller (packet_core packet) = code_response_caller (packet_core packet)"
    by (rule response_v061_leaf_keeps_its_decoded_legacy_caller) (use op in auto)
  show ?thesis
    by (simp add: response_v061_original_preflight_def response_fixed_original_preflight_def
      code_original_response_preflight_def response_fixed_channel_guard_def response_fixed_original_signature_def
      Let_def decoded sync_preserves_every_decoded_legacy_packet[OF decoded] mode legacy_op v061_caller
      cong: if_cong option.case_cong sum.case_cong)
qed

lemma response_v061_preflight_verifies_the_exact_original_before_signing:
  assumes "response_v061_original_preflight context accept_sync accept_current selected_mode verify raw = Inr (packet,call)"
  shows "sync_decode_packet raw = Some packet"
    "encode_wire_packet packet = raw"
    "response_v061_original_caller (packet_core packet) = Inr call"
    "verify (response_channel_remote_key (full_response_channel context))
       (envelope_signing_bytes (packet_core packet)) (packet_signature packet)"
  using assms sync_decoded_packet_has_the_exact_bytes
  by (auto simp: response_v061_original_preflight_def response_fixed_original_signature_def
      code_original_signature_refusal_def Let_def split: if_splits option.splits sum.splits)

definition response_v061_signable where
  "response_v061_signable config v061_now core \<longleftrightarrow>
    wire_sent_seconds core \<le> v061_now \<and> wire_sent_seconds core + response_config_ttl config < 2^64 \<and>
    v061_now \<le> wire_sent_seconds core + response_config_ttl config \<and> wire_version core = 6 \<and> wire_purpose core = 1 \<and>
    wire_deployment core = response_config_deployment config \<and>
    wire_source_domain core \<in> response_config_local_endpoints config \<and>
    wire_target_domain core \<in> fst ` response_config_peers config \<and>
    wire_principal core = response_config_principal config \<and> wire_key_number core = response_config_key config \<and>
    wire_authority_epoch core = response_config_epoch config \<and> wire_route_scope core = response_config_route config \<and>
    wire_ttl_seconds core = response_config_ttl config \<and> wire_signature_scheme core = 1 \<and>
    response_v061_operand (response_config_max_nesting config) core =
      Inr (Response_V061_Legacy_Operand Code_Nested_Response)"

definition response_v061_sign_guard where
  "response_v061_sign_guard context preimage =
    (case response_fixed_unframe preimage of None \<Rightarrow> False | Some core \<Rightarrow>
     case full_signing_clock context of None \<Rightarrow> False | Some v061_now \<Rightarrow>
       response_v061_signable (full_response_config context) v061_now core)"

lemma response_v061_signable_keeps_all_existing_getter_checks:
  assumes "(response_v061_operand (response_config_max_nesting config) core = Inr (Response_V061_Legacy_Operand Code_Nested_Response)) =
    (code_decode_operand_tree (response_config_max_nesting config) core = Code_Tree_Ready Code_Nested_Response)"
  shows "response_v061_signable config v061_now core = response_fixed_signable config v061_now core"
  using assms by (simp add: response_v061_signable_def response_fixed_signable_def)

definition response_v061_encoding_refused where
  "response_v061_encoding_refused reason = Inl (Response_Fixed_Encoding_Refused reason)"

definition response_v061_encode where
  "response_v061_encode hash curve_sign curve_verify context selected_mode original call result =
    (let channel = full_response_channel context; config = full_response_config context;
         frame_limit = full_response_frame_limit context; exact = encode_wire_core original
     in case response_v061_words call result of None \<Rightarrow> response_v061_encoding_refused Invalid_Wire_Format
     | Some (kind,number,position,words) \<Rightarrow> (case selected_mode of None \<Rightarrow> response_v061_encoding_refused Unsupported_Wire_Version
        | Some atomicity \<Rightarrow> let binding_message = response_fixed_binding_preimage exact atomicity words in
          case response_fixed_parameters_from hash config channel (full_parameters_clock context) (hash binding_message) of
            None \<Rightarrow> response_v061_encoding_refused Invalid_Wire_Source
          | Some parameters \<Rightarrow>
            if response_parameter_issued parameters > response_channel_expires channel then response_v061_encoding_refused Invalid_Wire_Source
            else let core = response_fixed_core channel parameters atomicity words exact in
              case code_typed_encode_core core of None \<Rightarrow> response_v061_encoding_refused Invalid_Wire_Format
              | Some core_bytes \<Rightarrow>
                if length core_bytes \<ge> 2^32 then response_v061_encoding_refused Invalid_Wire_Format
                else let preimage = envelope_signing_bytes core in
                  if \<not> response_v061_sign_guard context preimage then Inl Response_Fixed_Signature_Unavailable
                  else let packet = \<lparr>packet_core = core,packet_signature = curve_sign (response_channel_local_key channel) preimage\<rparr> in
                    case code_encode_packet packet of None \<Rightarrow> response_v061_encoding_refused Invalid_Wire_Format
                    | Some encoded \<Rightarrow>
                      if length encoded > frame_limit then response_v061_encoding_refused Invalid_Wire_Format
                      else case sync_decode_packet encoded of None \<Rightarrow> response_v061_encoding_refused Invalid_Wire_Format
                      | Some parsed \<Rightarrow>
                        case code_admit_packet (\<lambda>_ bytes signature. curve_verify (response_channel_local_key channel) bytes signature)
                           parsed (response_fixed_post_boundary channel parameters frame_limit) of
                          Some reason \<Rightarrow> response_v061_encoding_refused reason
                        | None \<Rightarrow> case response_v061_validate 2 original parsed of Inl reason \<Rightarrow> response_v061_encoding_refused reason
                          | Inr (verified,status) \<Rightarrow> Inr \<lparr>response_emission_bytes = encoded,response_emission_packet = parsed,
                              response_emission_original = original,response_emission_converted = (call,kind,number,position),
                              response_emission_verified = verified,response_emission_parameters = parameters,
                              response_emission_binding_preimage = binding_message,response_emission_signing_preimage = preimage\<rparr>))"

lemma response_v061_encoding_projects_the_exact_preimages_and_packet:
  assumes "response_v061_encode hash v061_sign verify context selected_mode original call result = Inr emission"
  obtains kind number position words atomicity parameters core_bytes core status where
    "response_v061_words call result = Some (kind,number,position,words)"
    "selected_mode = Some atomicity"
    "response_emission_original emission = original"
    "response_emission_converted emission = (call,kind,number,position)"
    "response_emission_binding_preimage emission = response_fixed_binding_preimage (encode_wire_core original) atomicity words"
    "response_fixed_parameters_from hash (full_response_config context) (full_response_channel context)
       (full_parameters_clock context) (hash (response_emission_binding_preimage emission)) = Some parameters"
    "core = response_fixed_core (full_response_channel context) parameters atomicity words (encode_wire_core original)"
    "code_typed_encode_core core = Some core_bytes"
    "response_emission_signing_preimage emission = envelope_signing_bytes core"
    "response_v061_sign_guard context (response_emission_signing_preimage emission)"
    "code_encode_packet \<lparr>packet_core = core,packet_signature = v061_sign (response_channel_local_key (full_response_channel context))
        (response_emission_signing_preimage emission)\<rparr> = Some (response_emission_bytes emission)"
    "sync_decode_packet (response_emission_bytes emission) = Some (response_emission_packet emission)"
    "response_v061_validate 2 original (response_emission_packet emission) = Inr (response_emission_verified emission,status)"
  using assms by (auto simp: response_v061_encode_def response_v061_encoding_refused_def Let_def
    split: option.splits sum.splits prod.splits if_splits)

definition response_v061_admit where
  "response_v061_admit curve_verify channel current expected bytes =
    (let scope = response_client_scope current in
     if response_channel_local channel \<noteq> boundary_target scope \<or>
        response_channel_remote channel \<noteq> boundary_source scope \<or>
        response_channel_deployment channel \<noteq> boundary_deployment scope \<or>
        boundary_now scope > response_channel_expires channel \<or>
        response_client_public_key current \<noteq> response_channel_remote_key channel
     then Inl Invalid_Wire_Source
     else case code_check_declared_version bytes (boundary_max_frame scope) of Some reason \<Rightarrow> Inl reason
      | None \<Rightarrow> (case sync_decode_packet bytes of None \<Rightarrow> Inl Invalid_Wire_Format | Some packet \<Rightarrow>
          case code_admit_packet (\<lambda>_ preimage signature. curve_verify (response_client_public_key current) preimage signature)
            packet (scope\<lparr>boundary_profile := response_channel_profile channel\<rparr>) of Some reason \<Rightarrow> Inl reason
          | None \<Rightarrow> response_v061_validate (response_client_max_nesting current) (packet_core expected) packet))"

lemma response_v061_admission_uses_the_current_client_verifier_and_exact_packet:
  assumes "response_v061_admit verify channel current expected raw = Inr received"
  obtains packet where "sync_decode_packet raw = Some packet" "encode_wire_packet packet = raw"
    "verify (response_client_public_key current) (envelope_signing_bytes (packet_core packet)) (packet_signature packet)"
    "response_v061_validate (response_client_max_nesting current) (packet_core expected) packet = Inr received"
  using assms sync_decoded_packet_has_the_exact_bytes
  by (auto simp: response_v061_admit_def code_admit_packet_def Let_def split: if_splits option.splits)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms response_v061_original_preflight_keeps_old_configured_operations
    response_v061_preflight_verifies_the_exact_original_before_signing response_v061_signable_keeps_all_existing_getter_checks
    response_v061_encoding_projects_the_exact_preimages_and_packet
    response_v061_admission_uses_the_current_client_verifier_and_exact_packet})
  then () else error "Unexpected oracle in the v0.6.1 signed packet boundary"
\<close>

end
