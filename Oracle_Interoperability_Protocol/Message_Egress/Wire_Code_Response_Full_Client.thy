theory Wire_Code_Response_Full_Client
  imports Wire_Code_Response_Full_Sender
begin

type_synonym code_full_client_value =
  "(client_call_id \<times> reference_response_kind \<times> nat \<times> nat option) \<times> code_response_status option"

definition code_full_client ::
  "response_fixed_channel \<Rightarrow> response_fixed_client_boundary \<Rightarrow> wire_packet \<Rightarrow> wire_bytes \<Rightarrow>
    code_full_verify_table \<Rightarrow> (wire_refusal + code_full_client_value)" where
  "code_full_client = (\<lambda>oip_full_channel oip_full_current oip_full_expected oip_full_received oip_full_verifications.
    response_fixed_admit (code_full_verify oip_full_verifications)
      oip_full_channel oip_full_current oip_full_expected oip_full_received)"

definition code_full_client_queries ::
  "response_fixed_channel \<Rightarrow> response_fixed_client_boundary \<Rightarrow> wire_packet \<Rightarrow> wire_bytes \<Rightarrow>
    code_full_verify_table \<Rightarrow> nat list list" where
  "code_full_client_queries = (\<lambda>oip_full_channel oip_full_current oip_full_expected oip_full_received oip_full_verifications.
    case response_fixed_admit (code_full_probe_verify oip_full_verifications)
        oip_full_channel oip_full_current oip_full_expected oip_full_received of
      Inr oip_full_result \<Rightarrow> []
    | Inl oip_full_reason \<Rightarrow>
        if oip_full_reason \<noteq> Invalid_Wire_Signature then []
        else case decode_wire_packet oip_full_received of None \<Rightarrow> [] | Some oip_full_packet \<Rightarrow>
          if wire_signature_scheme (packet_core oip_full_packet) = 2 \<or>
            wire_signature_scheme (packet_core oip_full_packet) \<notin>
              negotiated_schemes (response_channel_profile oip_full_channel) then []
          else code_full_need_verify oip_full_verifications (response_client_public_key oip_full_current)
            (envelope_signing_bytes (packet_core oip_full_packet)) (packet_signature oip_full_packet))"

definition code_full_client_input ::
  "integer list list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list list \<Rightarrow>
    (response_fixed_channel \<times> response_fixed_client_boundary \<times> wire_packet \<times> wire_bytes \<times>
      code_full_verify_table) option" where
  "code_full_client_input = (\<lambda>oip_full_rows oip_full_expected_bytes oip_full_received_bytes oip_full_verify_rows.
    if \<not> code_integer_octet_values (oip_full_expected_bytes @ oip_full_received_bytes) then None
    else Option.bind (code_full_client_from_integer oip_full_rows) (\<lambda>(oip_full_channel,oip_full_current).
      Option.bind (decode_wire_packet (map nat_of_integer oip_full_expected_bytes)) (\<lambda>oip_full_expected.
        map_option (\<lambda>(oip_full_hashes,oip_full_signatures,oip_full_verifications).
          (oip_full_channel,oip_full_current,oip_full_expected,map nat_of_integer oip_full_received_bytes,oip_full_verifications))
          (code_full_tables_from_integer [] [] oip_full_verify_rows))))"

definition code_full_pack_client ::
  "(wire_refusal + code_full_client_value) \<Rightarrow> (integer \<times> integer list)" where
  "code_full_pack_client = (\<lambda>oip_full_result.
    case oip_full_result of Inl oip_full_reason \<Rightarrow> (integer_of_nat (code_transport_refusal_number oip_full_reason),[])
     | Inr (oip_full_selected,None) \<Rightarrow> (-1,[])
     | Inr (oip_full_selected,Some (Code_Known_Response oip_full_kind oip_full_number)) \<Rightarrow>
         (0,map integer_of_nat (code_full_result_row oip_full_selected @
           [1,code_full_kind_number oip_full_kind,oip_full_number]))
     | Inr (oip_full_selected,Some (Code_Unknown_Response oip_full_kind oip_full_number)) \<Rightarrow>
         (0,map integer_of_nat (code_full_result_row oip_full_selected @
           [0,code_full_kind_number oip_full_kind,oip_full_number])))"

definition code_response_admit_queries_flat ::
  "integer list list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list list \<Rightarrow>
    (integer \<times> integer list list)" where
  "code_response_admit_queries_flat = (\<lambda>oip_full_rows oip_full_expected_bytes oip_full_received_bytes oip_full_verify_rows.
    case code_full_client_input oip_full_rows oip_full_expected_bytes oip_full_received_bytes oip_full_verify_rows of
      None \<Rightarrow> (-1,[])
    | Some (oip_full_channel,oip_full_current,oip_full_expected,oip_full_received,oip_full_verifications) \<Rightarrow>
        (0,map (map integer_of_nat) (code_full_client_queries
          oip_full_channel oip_full_current oip_full_expected oip_full_received oip_full_verifications)))"

definition code_response_admit_flat_oracle ::
  "integer list list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list list \<Rightarrow>
    (integer \<times> integer list)" where
  "code_response_admit_flat_oracle = (\<lambda>oip_full_rows oip_full_expected_bytes oip_full_received_bytes oip_full_verify_rows.
    case code_full_client_input oip_full_rows oip_full_expected_bytes oip_full_received_bytes oip_full_verify_rows of
      None \<Rightarrow> (-1,[])
    | Some (oip_full_channel,oip_full_current,oip_full_expected,oip_full_received,oip_full_verifications) \<Rightarrow>
        if code_full_client_queries oip_full_channel oip_full_current oip_full_expected oip_full_received
            oip_full_verifications \<noteq> [] then (-2,[])
        else code_full_pack_client (code_full_client
          oip_full_channel oip_full_current oip_full_expected oip_full_received oip_full_verifications))"

definition code_response_egress_and_admit_flat_oracle ::
  "integer list list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow>
    integer list list \<Rightarrow> integer list list \<Rightarrow>
    (integer \<times> integer list list \<times> integer \<times> integer list)" where
  "code_response_egress_and_admit_flat_oracle = (\<lambda>oip_full_sender_rows oip_full_mode oip_full_reply
      oip_full_retained_present oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows
      oip_full_client_rows oip_full_client_verify_rows.
    let (oip_full_sender_status,oip_full_output) =
      code_response_egress_flat_oracle oip_full_sender_rows oip_full_mode oip_full_reply oip_full_retained_present
        oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows
    in if oip_full_sender_status \<noteq> 0 then (oip_full_sender_status,oip_full_output,-3,[])
    else let (oip_full_client_status,oip_full_client_output) =
      code_response_admit_flat_oracle oip_full_client_rows oip_full_original (oip_full_output ! 12) oip_full_client_verify_rows
    in (oip_full_sender_status,oip_full_output,oip_full_client_status,oip_full_client_output))"

lemma an_unknown_client_status_is_preserved_as_unknown:
  fixes oip_full_selected :: "client_call_id \<times> reference_response_kind \<times> nat \<times> nat option"
    and oip_full_kind :: reference_response_kind and oip_full_number :: nat
  shows "code_full_pack_client (Inr (oip_full_selected,Some (Code_Unknown_Response oip_full_kind oip_full_number))) =
    (0,map integer_of_nat (code_full_result_row oip_full_selected @
      [0,code_full_kind_number oip_full_kind,oip_full_number]))"
  by (simp add: code_full_pack_client_def)

text \<open>
  The standalone client accepts an original network fixture input or bytes
  generated by the model sender. It does not use a source-observed sender
  output as the model sender answer. The combined entry has no response
  input argument: its packet is row12 of the model sender's own result.
  Current client key/scope/nesting remain separate from emitter getters.
  Status -3 means that no client call was made after a failed sender.
\<close>

end
