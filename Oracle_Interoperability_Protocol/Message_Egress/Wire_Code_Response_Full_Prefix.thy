theory Wire_Code_Response_Full_Prefix
  imports Wire_Code_Response_Full_Client
begin

definition code_full_sign_guard :: "code_response_full_context \<Rightarrow> wire_bytes \<Rightarrow> bool" where
  "code_full_sign_guard = (\<lambda>oip_full_context oip_full_message.
    case response_fixed_unframe oip_full_message of None \<Rightarrow> False | Some oip_full_core \<Rightarrow>
      case full_signing_clock oip_full_context of None \<Rightarrow> False | Some oip_full_now \<Rightarrow>
        response_fixed_signable (full_response_config oip_full_context) oip_full_now oip_full_core)"

definition code_full_prefix_after_uuid ::
  "code_response_full_context \<Rightarrow> wire_core \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
    wire_bytes \<Rightarrow> code_full_hash_table \<Rightarrow> code_full_sign_table \<Rightarrow> nat list list \<Rightarrow> nat list list" where
  "code_full_prefix_after_uuid = (\<lambda>oip_full_context oip_full_original oip_full_atomicity oip_full_words
      oip_full_binding oip_full_hashes oip_full_signatures oip_full_rows.
    case response_fixed_parameters_from (code_full_hash oip_full_hashes) (full_response_config oip_full_context)
        (full_response_channel oip_full_context) (full_parameters_clock oip_full_context) oip_full_binding of
      None \<Rightarrow> oip_full_rows
    | Some oip_full_parameters \<Rightarrow>
      let oip_full_with_parameters =
            (oip_full_rows[8 := response_parameter_uuid oip_full_parameters])[9 :=
              [response_parameter_principal oip_full_parameters,response_parameter_key oip_full_parameters,
               response_parameter_epoch oip_full_parameters,response_parameter_issued oip_full_parameters,
               response_parameter_ttl oip_full_parameters,response_parameter_route oip_full_parameters]];
          oip_full_core = response_fixed_core (full_response_channel oip_full_context) oip_full_parameters
            oip_full_atomicity oip_full_words (encode_wire_core oip_full_original)
      in if response_parameter_issued oip_full_parameters >
           response_channel_expires (full_response_channel oip_full_context) then oip_full_with_parameters
      else case code_typed_encode_core oip_full_core of None \<Rightarrow> oip_full_with_parameters
       | Some oip_full_core_bytes \<Rightarrow>
         if length oip_full_core_bytes \<ge> 2^32 then oip_full_with_parameters
         else let oip_full_message = envelope_signing_bytes oip_full_core;
                  oip_full_allowed = code_full_sign_guard oip_full_context oip_full_message;
                  oip_full_attempt =
                    (((oip_full_with_parameters[10 := oip_full_core_bytes])[11 := oip_full_message])
                      [12 := [if oip_full_allowed then 1 else 0]])
              in if \<not> oip_full_allowed then oip_full_attempt
                 else case code_full_lookup_sign oip_full_signatures
                     (response_channel_local_key (full_response_channel oip_full_context)) oip_full_message of
                   None \<Rightarrow> oip_full_attempt
                 | Some oip_full_signature \<Rightarrow> oip_full_attempt[13 := oip_full_signature])"

definition code_full_prefix_selected ::
  "code_response_full_context \<Rightarrow> response_fixed_observation \<Rightarrow> wire_packet \<Rightarrow> client_call_id \<Rightarrow>
    code_full_hash_table \<Rightarrow> code_full_sign_table \<Rightarrow> nat list list" where
  "code_full_prefix_selected = (\<lambda>oip_full_context oip_full_observation oip_full_original oip_full_call
      oip_full_hashes oip_full_signatures.
    let (oip_full_number,oip_full_position) = response_fixed_result oip_full_observation;
        oip_full_base = ((replicate 14 [])[0 :=
          [oip_full_number,if oip_full_position = None then 0 else 1,(case oip_full_position of None \<Rightarrow> 0 | Some oip_full_optional_position \<Rightarrow> oip_full_optional_position)]])
          [3 := encode_wire_core (packet_core oip_full_original)]
    in case response_fixed_words oip_full_call (response_fixed_result oip_full_observation) of None \<Rightarrow> oip_full_base
     | Some (oip_full_kind,oip_full_code,oip_full_commit,oip_full_words) \<Rightarrow>
       let oip_full_with_words = oip_full_base[1 := oip_full_words]
       in case response_fixed_atomicity (full_response_channel oip_full_context) of None \<Rightarrow> oip_full_with_words
        | Some oip_full_atomicity \<Rightarrow>
          let oip_full_binding_message = response_fixed_binding_preimage
                (encode_wire_core (packet_core oip_full_original)) oip_full_atomicity oip_full_words;
              oip_full_with_binding = (oip_full_with_words[2 := [oip_full_atomicity]])[4 := oip_full_binding_message]
          in case code_full_lookup_hash oip_full_hashes oip_full_binding_message of None \<Rightarrow> oip_full_with_binding
           | Some oip_full_binding \<Rightarrow>
             let oip_full_with_digest = oip_full_with_binding[5 := oip_full_binding]
             in if \<not> response_fixed_channel_current (full_response_config oip_full_context)
                 (full_response_channel oip_full_context) then oip_full_with_digest
             else case full_parameters_clock oip_full_context of None \<Rightarrow> oip_full_with_digest
              | Some oip_full_issued \<Rightarrow>
                let oip_full_uuid_message = response_fixed_uuid_preimage (full_response_config oip_full_context)
                      oip_full_binding oip_full_issued;
                    oip_full_with_uuid_message = oip_full_with_digest[6 := oip_full_uuid_message]
                in case code_full_lookup_hash oip_full_hashes oip_full_uuid_message of
                     None \<Rightarrow> oip_full_with_uuid_message
                   | Some oip_full_uuid_digest \<Rightarrow>
                     code_full_prefix_after_uuid oip_full_context (packet_core oip_full_original) oip_full_atomicity
                       oip_full_words oip_full_binding oip_full_hashes oip_full_signatures
                       (oip_full_with_uuid_message[7 := oip_full_uuid_digest]))"

definition code_full_prefix_integer ::
  "bool \<Rightarrow> integer list list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow> (integer \<times> integer list list)" where
  "code_full_prefix_integer = (\<lambda>oip_full_include_original oip_full_rows oip_full_mode oip_full_reply
      oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows.
    case code_full_sender_input oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained
        oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows of None \<Rightarrow> (-1,[])
     | Some (oip_full_context,oip_full_observation,oip_full_bytes,oip_full_hashes,oip_full_signatures,oip_full_verifications) \<Rightarrow>
       (case oip_full_observation of None \<Rightarrow>
          (if \<not> oip_full_include_original then (-1,[])
           else case code_full_without_result oip_full_context oip_full_bytes oip_full_verifications of
             (oip_full_status,oip_full_output) \<Rightarrow>
               if oip_full_status = -1 \<or> oip_full_status = -2 then (oip_full_status,[]) else (0,[]))
        | Some oip_full_actual \<Rightarrow>
          if code_full_sender_queries oip_full_include_original oip_full_context oip_full_actual oip_full_bytes
              oip_full_hashes oip_full_signatures oip_full_verifications \<noteq> [] then (-2,[])
          else let oip_full_selected =
            (if oip_full_include_original then fst (code_full_original_selection oip_full_context oip_full_bytes oip_full_verifications)
             else case decode_wire_packet oip_full_bytes of None \<Rightarrow> None | Some oip_full_packet \<Rightarrow>
               case code_response_caller (packet_core oip_full_packet) of Inl oip_full_reason \<Rightarrow> None
                | Inr oip_full_call \<Rightarrow> Some (oip_full_packet,oip_full_call))
          in case oip_full_selected of None \<Rightarrow> (0,[])
           | Some (oip_full_packet,oip_full_call) \<Rightarrow> (0,map (map integer_of_nat)
               (code_full_prefix_selected oip_full_context oip_full_actual oip_full_packet oip_full_call
                 oip_full_hashes oip_full_signatures))))"

definition code_response_egress_prefix_flat where
  "code_response_egress_prefix_flat = code_full_prefix_integer True"

definition code_response_encode_boundary_prefix_flat where
  "code_response_encode_boundary_prefix_flat = code_full_prefix_integer False"

lemma a_refused_signer_guard_does_not_invent_a_curve_signature:
  fixes oip_full_context :: code_response_full_context and oip_full_message :: wire_bytes
    and oip_full_signatures :: code_full_sign_table
  assumes "\<not> code_full_sign_guard oip_full_context oip_full_message"
  shows "response_fixed_sign
      (code_full_sign oip_full_signatures (response_channel_local_key (full_response_channel oip_full_context))) ()
      (full_response_config oip_full_context) (full_signing_clock oip_full_context) oip_full_message = None"
  using assms by (auto simp: code_full_sign_guard_def response_fixed_sign_def split: option.splits if_splits)

text \<open>
  Prefix rows are observations of the message constructor before its final
  result. A signer-method attempt with guard=False can have a preimage and
  no curve call/signature. It is not a signed packet or a sender success.
  The final status and returned packet remain those of the existing Fixed
  encoder. No source observed partial output enters this computation.
\<close>

end
