theory Wire_Code_Response_Full_Queries
  imports Wire_Code_Response_Full_Primitives
begin

definition code_full_signing_queries ::
  "code_response_full_context \<Rightarrow> response_fixed_parameters \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> wire_core \<Rightarrow>
    code_full_sign_table \<Rightarrow> code_full_verify_table \<Rightarrow> nat list list" where
  "code_full_signing_queries = (\<lambda>oip_full_context oip_full_parameters oip_full_atomicity oip_full_words
      oip_full_original oip_full_signatures oip_full_verifications.
    let oip_full_channel = full_response_channel oip_full_context;
        oip_full_config = full_response_config oip_full_context;
        oip_full_core = response_fixed_core oip_full_channel oip_full_parameters oip_full_atomicity
          oip_full_words (encode_wire_core oip_full_original);
        oip_full_message = envelope_signing_bytes oip_full_core;
        oip_full_key = response_channel_local_key oip_full_channel
    in if response_parameter_issued oip_full_parameters > response_channel_expires oip_full_channel then []
    else case code_typed_encode_core oip_full_core of None \<Rightarrow> [] | Some oip_full_core_bytes \<Rightarrow>
      if length oip_full_core_bytes \<ge> 2^32 then []
      else case response_fixed_unframe oip_full_message of None \<Rightarrow> [] | Some oip_full_framed_core \<Rightarrow>
        case full_signing_clock oip_full_context of None \<Rightarrow> [] | Some oip_full_now \<Rightarrow>
          if \<not> response_fixed_signable oip_full_config oip_full_now oip_full_framed_core then []
          else case code_full_lookup_sign oip_full_signatures oip_full_key oip_full_message of
            None \<Rightarrow> [code_full_sign_query oip_full_key oip_full_message]
          | Some oip_full_signature \<Rightarrow>
              code_full_need_verify oip_full_verifications oip_full_key oip_full_message oip_full_signature)"

definition code_full_after_binding_queries ::
  "code_response_full_context \<Rightarrow> wire_core \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> wire_bytes \<Rightarrow>
    code_full_hash_table \<Rightarrow> code_full_sign_table \<Rightarrow> code_full_verify_table \<Rightarrow> nat list list" where
  "code_full_after_binding_queries = (\<lambda>oip_full_context oip_full_original oip_full_atomicity oip_full_words
      oip_full_binding oip_full_hashes oip_full_signatures oip_full_verifications.
    let oip_full_config = full_response_config oip_full_context;
        oip_full_channel = full_response_channel oip_full_context
    in if \<not> response_fixed_channel_current oip_full_config oip_full_channel then []
    else case full_parameters_clock oip_full_context of None \<Rightarrow> [] | Some oip_full_issued \<Rightarrow>
      let oip_full_uuid_message = response_fixed_uuid_preimage oip_full_config oip_full_binding oip_full_issued
      in case code_full_lookup_hash oip_full_hashes oip_full_uuid_message of
           None \<Rightarrow> [code_full_hash_query oip_full_uuid_message]
         | Some oip_full_uuid_digest \<Rightarrow>
             (case response_fixed_parameters_from (code_full_hash oip_full_hashes) oip_full_config oip_full_channel
                 (full_parameters_clock oip_full_context) oip_full_binding of None \<Rightarrow> []
              | Some oip_full_parameters \<Rightarrow> code_full_signing_queries oip_full_context oip_full_parameters
                  oip_full_atomicity oip_full_words oip_full_original oip_full_signatures oip_full_verifications))"

definition code_full_original_selection ::
  "code_response_full_context \<Rightarrow> wire_bytes \<Rightarrow> code_full_verify_table \<Rightarrow>
    ((wire_packet \<times> client_call_id) option \<times> nat list list)" where
  "code_full_original_selection = (\<lambda>oip_full_context oip_full_bytes oip_full_verifications.
    let oip_full_channel = full_response_channel oip_full_context;
        oip_full_attempt = response_fixed_original_preflight (full_response_config oip_full_context)
          oip_full_channel (full_response_site oip_full_context) (code_full_probe_verify oip_full_verifications)
          (full_response_frame_limit oip_full_context) oip_full_bytes
    in case oip_full_attempt of Inr oip_full_selected \<Rightarrow> (Some oip_full_selected,[])
     | Inl oip_full_reason \<Rightarrow>
       if oip_full_reason \<noteq> Invalid_Wire_Signature then (None,[])
       else case decode_wire_packet oip_full_bytes of None \<Rightarrow> (None,[]) | Some oip_full_original \<Rightarrow>
         if wire_signature_scheme (packet_core oip_full_original) = 2 \<or>
           wire_signature_scheme (packet_core oip_full_original) \<notin> negotiated_schemes (response_channel_profile oip_full_channel)
         then (None,[])
         else (None,code_full_need_verify oip_full_verifications
           (response_channel_remote_key oip_full_channel)
           (envelope_signing_bytes (packet_core oip_full_original)) (packet_signature oip_full_original)))"

definition code_full_selected_sender_queries ::
  "code_response_full_context \<Rightarrow> response_fixed_observation \<Rightarrow> wire_packet \<Rightarrow> client_call_id \<Rightarrow>
    code_full_hash_table \<Rightarrow> code_full_sign_table \<Rightarrow> code_full_verify_table \<Rightarrow> nat list list" where
  "code_full_selected_sender_queries = (\<lambda>oip_full_context oip_full_observation oip_full_original oip_full_call
      oip_full_hashes oip_full_signatures oip_full_verifications.
    case response_fixed_words oip_full_call (response_fixed_result oip_full_observation) of None \<Rightarrow> []
     | Some (oip_full_kind,oip_full_number,oip_full_position,oip_full_words) \<Rightarrow>
       case response_fixed_atomicity (full_response_channel oip_full_context) of None \<Rightarrow> []
        | Some oip_full_atomicity \<Rightarrow>
          let oip_full_binding_message = response_fixed_binding_preimage
                (encode_wire_core (packet_core oip_full_original)) oip_full_atomicity oip_full_words
          in case code_full_lookup_hash oip_full_hashes oip_full_binding_message of
               None \<Rightarrow> [code_full_hash_query oip_full_binding_message]
             | Some oip_full_binding \<Rightarrow> code_full_after_binding_queries oip_full_context
                 (packet_core oip_full_original) oip_full_atomicity oip_full_words oip_full_binding
                 oip_full_hashes oip_full_signatures oip_full_verifications)"

definition code_full_sender_queries ::
  "bool \<Rightarrow> code_response_full_context \<Rightarrow> response_fixed_observation \<Rightarrow> wire_bytes \<Rightarrow>
    code_full_hash_table \<Rightarrow> code_full_sign_table \<Rightarrow> code_full_verify_table \<Rightarrow> nat list list" where
  "code_full_sender_queries = (\<lambda>oip_full_include_original oip_full_context oip_full_observation oip_full_bytes
      oip_full_hashes oip_full_signatures oip_full_verifications.
    if oip_full_include_original then
      (case code_full_original_selection oip_full_context oip_full_bytes oip_full_verifications of
         (None,oip_full_queries) \<Rightarrow> oip_full_queries
       | (Some (oip_full_original,oip_full_call),oip_full_queries) \<Rightarrow>
           code_full_selected_sender_queries oip_full_context oip_full_observation oip_full_original oip_full_call
             oip_full_hashes oip_full_signatures oip_full_verifications)
    else case decode_wire_packet oip_full_bytes of None \<Rightarrow> [] | Some oip_full_original \<Rightarrow>
      case code_response_caller (packet_core oip_full_original) of Inl oip_full_reason \<Rightarrow> []
       | Inr oip_full_call \<Rightarrow>
         code_full_selected_sender_queries oip_full_context oip_full_observation oip_full_original oip_full_call
           oip_full_hashes oip_full_signatures oip_full_verifications)"

definition code_full_sender_input ::
  "integer list list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow>
    (code_response_full_context \<times> response_fixed_observation option \<times> wire_bytes \<times>
      code_full_hash_table \<times> code_full_sign_table \<times> code_full_verify_table) option" where
  "code_full_sender_input = (\<lambda>oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained
      oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows.
    if \<not> code_integer_u64_values (oip_full_mode # oip_full_reply @ oip_full_retained) \<or>
       \<not> code_integer_octet_values oip_full_original then None
    else Option.bind (code_full_context_from_integer oip_full_rows) (\<lambda>oip_full_context.
      Option.bind
        (if oip_full_mode = 3 then
           (if oip_full_reply = [] \<and> \<not> oip_full_retained_present \<and> oip_full_retained = []
            then Some None else None)
         else map_option Some (code_rbound_observation (nat_of_integer oip_full_mode) (map nat_of_integer oip_full_reply)
           oip_full_retained_present (map nat_of_integer oip_full_retained))) (\<lambda>oip_full_observation.
        map_option (\<lambda>(oip_full_hashes,oip_full_signatures,oip_full_verifications).
          (oip_full_context,oip_full_observation,map nat_of_integer oip_full_original,
            oip_full_hashes,oip_full_signatures,oip_full_verifications))
          (code_full_tables_from_integer oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows))))"

definition code_full_queries_integer ::
  "bool \<Rightarrow> integer list list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow> (integer \<times> integer list list)" where
  "code_full_queries_integer = (\<lambda>oip_full_include_original oip_full_rows oip_full_mode oip_full_reply
      oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows.
    case code_full_sender_input oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present oip_full_retained
        oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows of None \<Rightarrow> (-1,[])
     | Some (oip_full_context,oip_full_observation,oip_full_bytes,oip_full_hashes,oip_full_signatures,oip_full_verifications) \<Rightarrow>
       (case oip_full_observation of
          None \<Rightarrow>
            (if \<not> oip_full_include_original then (-1,[])
             else case code_full_original_selection oip_full_context oip_full_bytes oip_full_verifications of
               (Some oip_full_selected,oip_full_queries) \<Rightarrow> (-1,[])
             | (None,oip_full_queries) \<Rightarrow> (0,map (map integer_of_nat) oip_full_queries))
        | Some oip_full_actual \<Rightarrow>
            (0,map (map integer_of_nat) (code_full_sender_queries oip_full_include_original oip_full_context
              oip_full_actual oip_full_bytes oip_full_hashes oip_full_signatures oip_full_verifications))))"

definition code_response_egress_queries_flat where
  "code_response_egress_queries_flat = code_full_queries_integer True"

definition code_response_encode_boundary_queries_flat where
  "code_response_encode_boundary_queries_flat = code_full_queries_integer False"

text \<open>
  Request rows are computed from the same decoded original, typed result
  converter, current finite getters and existing preimage constructors.
  The whole sender does not expose binding/UUID/signing requests until its
  existing original preflight succeeds with a true keyed verification row.
  This is a conservative catalog for filling the remaining transcript, not
  a claim about the source's executed post-verification query trace on a
  refused path.
  Actual encoder/client values below always come from the existing exact
  functions; an unexpected missing primitive callback aborts execution.
\<close>

end
