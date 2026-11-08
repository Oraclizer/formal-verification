theory Wire_Code_Response_Selected_Encode
  imports Wire_Code_Response_Selected_Preflight
begin

definition code_exec_fixed_encode where
  "code_exec_fixed_encode = (\<lambda>(oip_exec_selected_mode :: nat option) oip_exec_low_hash oip_exec_low_curve_sign oip_exec_low_signing_key oip_exec_low_curve_verify oip_exec_low_config oip_exec_low_channel oip_exec_low_parameters_clock oip_exec_low_signing_clock oip_exec_low_original oip_exec_low_call_id oip_exec_low_observation oip_exec_low_frame_limit.
    (case response_fixed_words oip_exec_low_call_id (response_fixed_result oip_exec_low_observation) of None \<Rightarrow> Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Format)
     | Some (oip_exec_low_kind,oip_exec_low_number,oip_exec_low_position,oip_exec_low_words) \<Rightarrow>
       case oip_exec_selected_mode of None \<Rightarrow> Inl (Response_Fixed_Encoding_Refused Unsupported_Wire_Version)
        | Some oip_exec_low_atomicity \<Rightarrow>
          let oip_exec_low_binding_preimage = response_fixed_binding_preimage (encode_wire_core oip_exec_low_original) oip_exec_low_atomicity oip_exec_low_words in
          case response_fixed_parameters_from oip_exec_low_hash oip_exec_low_config oip_exec_low_channel oip_exec_low_parameters_clock (oip_exec_low_hash oip_exec_low_binding_preimage) of
            None \<Rightarrow> Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Source)
          | Some oip_exec_low_parameters \<Rightarrow>
            if response_parameter_issued oip_exec_low_parameters > response_channel_expires oip_exec_low_channel then Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Source)
            else let oip_exec_low_core = response_fixed_core oip_exec_low_channel oip_exec_low_parameters oip_exec_low_atomicity oip_exec_low_words (encode_wire_core oip_exec_low_original) in
              case code_typed_encode_core oip_exec_low_core of None \<Rightarrow> Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Format)
              | Some oip_exec_low_core_bytes \<Rightarrow>
                if length oip_exec_low_core_bytes \<ge> 2^32 then Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Format)
                else let oip_exec_low_signing_preimage = envelope_signing_bytes oip_exec_low_core in
                  case response_fixed_sign oip_exec_low_curve_sign oip_exec_low_signing_key oip_exec_low_config oip_exec_low_signing_clock oip_exec_low_signing_preimage of
                    None \<Rightarrow> Inl Response_Fixed_Signature_Unavailable
                  | Some oip_exec_low_signature \<Rightarrow>
                    let oip_exec_low_packet = \<lparr>packet_core = oip_exec_low_core,packet_signature = oip_exec_low_signature\<rparr> in
                    case code_encode_packet oip_exec_low_packet of None \<Rightarrow> Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Format)
                    | Some oip_exec_low_encoded \<Rightarrow>
                      if length oip_exec_low_encoded > oip_exec_low_frame_limit then Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Format)
                      else case decode_wire_packet oip_exec_low_encoded of None \<Rightarrow> Inl (Response_Fixed_Encoding_Refused Invalid_Wire_Format)
                      | Some oip_exec_low_parsed \<Rightarrow>
                        case code_admit_packet (\<lambda>oip_exec_low_core oip_exec_low_bytes oip_exec_low_signature. oip_exec_low_curve_verify (response_channel_local_key oip_exec_low_channel) oip_exec_low_bytes oip_exec_low_signature)
                           oip_exec_low_parsed (response_fixed_post_boundary oip_exec_low_channel oip_exec_low_parameters oip_exec_low_frame_limit) of
                          Some oip_exec_low_reason \<Rightarrow> Inl (Response_Fixed_Encoding_Refused oip_exec_low_reason)
                        | None \<Rightarrow> case response_fixed_validate 2 oip_exec_low_original oip_exec_low_parsed of
                            Inl oip_exec_low_reason \<Rightarrow> Inl (Response_Fixed_Encoding_Refused oip_exec_low_reason)
                          | Inr oip_exec_low_verified \<Rightarrow> Inr \<lparr>response_emission_bytes = oip_exec_low_encoded,response_emission_packet = oip_exec_low_parsed,
                              response_emission_original = oip_exec_low_original,response_emission_converted = (oip_exec_low_call_id,oip_exec_low_kind,oip_exec_low_number,oip_exec_low_position),
                              response_emission_verified = oip_exec_low_verified,response_emission_parameters = oip_exec_low_parameters,
                              response_emission_binding_preimage = oip_exec_low_binding_preimage,response_emission_signing_preimage = oip_exec_low_signing_preimage\<rparr>))"

lemma code_exec_fixed_encode_is_original:
  fixes oip_exec_selected_mode :: "nat option"
  assumes oip_exec_mode_matches: "oip_exec_selected_mode = response_fixed_atomicity oip_exec_low_channel"
  shows "code_exec_fixed_encode oip_exec_selected_mode oip_exec_low_hash oip_exec_low_curve_sign oip_exec_low_signing_key oip_exec_low_curve_verify oip_exec_low_config oip_exec_low_channel oip_exec_low_parameters_clock oip_exec_low_signing_clock oip_exec_low_original oip_exec_low_call_id oip_exec_low_observation oip_exec_low_frame_limit =
    response_fixed_encode oip_exec_low_hash oip_exec_low_curve_sign oip_exec_low_signing_key oip_exec_low_curve_verify oip_exec_low_config oip_exec_low_channel oip_exec_low_parameters_clock oip_exec_low_signing_clock oip_exec_low_original oip_exec_low_call_id oip_exec_low_observation oip_exec_low_frame_limit"
  using oip_exec_mode_matches
  by (simp add: code_exec_fixed_encode_def response_fixed_encode_def Let_def 
    cong: sum.case_cong option.case_cong)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms code_exec_fixed_encode_is_original})
  then () else error "Unexpected oracle in selected-mode sender encoding"
\<close>

end
