theory Wire_Code_Response_Binding_Boundary
  imports Wire_Code_Response_Boundary_Result
    "Wire_Response_Fixed_Preimage"
begin

definition code_rbound_atomicity :: "nat list \<Rightarrow> nat option" where
  "code_rbound_atomicity oip_binder_numbers =
    (if oip_binder_numbers = [] then None else Some (Min (set oip_binder_numbers)))"

lemma the_boundary_mode_is_the_existing_finite_channel_atomicity:
  assumes "negotiated_atomicities (response_channel_profile oip_binder_channel) = set oip_binder_numbers"
  shows "code_rbound_atomicity oip_binder_numbers = response_fixed_atomicity oip_binder_channel"
  using assms by (simp add: code_rbound_atomicity_def response_fixed_atomicity_def Let_def)

definition code_rbound_binding_stage ::
  "response_fixed_observation \<Rightarrow> wire_packet \<Rightarrow> nat list \<Rightarrow>
    (wire_refusal + (nat \<times> nat option \<times> nat \<times> nat list \<times> wire_bytes \<times> wire_bytes))" where
  "code_rbound_binding_stage oip_binder_observation oip_binder_original oip_binder_numbers =
    (case code_response_caller (packet_core oip_binder_original) of Inl oip_binder_reason \<Rightarrow> Inl oip_binder_reason
     | Inr oip_binder_call_id \<Rightarrow>
       case response_fixed_words oip_binder_call_id (response_fixed_result oip_binder_observation) of None \<Rightarrow> Inl Invalid_Wire_Format
        | Some (oip_binder_kind,oip_binder_number,oip_binder_position,oip_binder_words) \<Rightarrow>
          case code_rbound_atomicity oip_binder_numbers of None \<Rightarrow> Inl Unsupported_Wire_Version
           | Some oip_binder_atomicity \<Rightarrow>
             let oip_binder_core = encode_wire_core (packet_core oip_binder_original) in
             Inr (oip_binder_number,oip_binder_position,oip_binder_atomicity,oip_binder_words,oip_binder_core,response_fixed_binding_preimage oip_binder_core oip_binder_atomicity oip_binder_words))"

definition code_response_binding_flat_oracle ::
  "integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow>
    integer list \<Rightarrow> integer list \<Rightarrow>
    (bool \<times> integer \<times> integer \<times> bool \<times> integer \<times> integer \<times>
      integer list \<times> integer list \<times> integer list)" where
  "code_response_binding_flat_oracle oip_binder_mode oip_binder_values oip_binder_retained_present oip_binder_retained oip_binder_original_bytes oip_binder_atomicities =
    (if \<not> code_integer_u64_values (oip_binder_mode # oip_binder_values @ oip_binder_retained @ oip_binder_atomicities) \<or>
        \<not> code_integer_octet_values oip_binder_original_bytes then (False,-1,0,False,0,0,[],[],[])
     else case code_rbound_observation (nat_of_integer oip_binder_mode) (map nat_of_integer oip_binder_values)
         oip_binder_retained_present (map nat_of_integer oip_binder_retained) of None \<Rightarrow> (False,-1,0,False,0,0,[],[],[])
      | Some oip_binder_observation \<Rightarrow>
        case decode_wire_packet (map nat_of_integer oip_binder_original_bytes) of
          None \<Rightarrow> (True,70,0,False,0,0,[],[],[])
        | Some oip_binder_original \<Rightarrow>
          case code_rbound_binding_stage oip_binder_observation oip_binder_original (map nat_of_integer oip_binder_atomicities) of
            Inl oip_binder_reason \<Rightarrow> (True,integer_of_nat (code_transport_refusal_number oip_binder_reason),0,False,0,0,[],[],[])
          | Inr (oip_binder_number,oip_binder_position,oip_binder_atomicity,oip_binder_words,oip_binder_core,oip_binder_preimage) \<Rightarrow>
            (True,0,integer_of_nat oip_binder_number,oip_binder_position \<noteq> None,integer_of_nat ((case oip_binder_position of None \<Rightarrow> 0 | Some oip_option_value \<Rightarrow> oip_option_value)),
              integer_of_nat oip_binder_atomicity,map integer_of_nat oip_binder_words,map integer_of_nat oip_binder_core,map integer_of_nat oip_binder_preimage))"

lemma the_boundary_binding_uses_the_exact_existing_result_words_and_original:
  assumes "code_rbound_binding_stage oip_binder_observation oip_binder_original oip_binder_numbers =
    Inr (oip_binder_number,oip_binder_position,oip_binder_atomicity,oip_binder_words,oip_binder_core,oip_binder_preimage)"
  obtains oip_binder_call_id oip_binder_kind
  where
    "code_response_caller (packet_core oip_binder_original) = Inr oip_binder_call_id"
    "response_fixed_words oip_binder_call_id (response_fixed_result oip_binder_observation) =
      Some (oip_binder_kind,oip_binder_number,oip_binder_position,oip_binder_words)"
    "code_rbound_atomicity oip_binder_numbers = Some oip_binder_atomicity"
    "oip_binder_core = encode_wire_core (packet_core oip_binder_original)"
    "oip_binder_preimage = response_fixed_binding_preimage
      (encode_wire_core (packet_core oip_binder_original)) oip_binder_atomicity oip_binder_words"
  using assms by (auto simp: code_rbound_binding_stage_def Let_def
    split: sum.splits option.splits prod.splits)

definition code_rbound_uuid_preimage :: "wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> nat \<Rightarrow> wire_bytes" where
  "code_rbound_uuid_preimage oip_binder_policy_binding oip_binder_response_binding oip_binder_issued =
    [111,105,112,47,114,101,102,101,114,101,110,99,101,45,114,101,115,112,111,110,115,101,45,117,117,105,100,47,118,49,0] @
    oip_binder_policy_binding @ oip_binder_response_binding @ response_fixed_be64 oip_binder_issued"

lemma the_uuid_primitive_request_is_the_existing_config_getter_preimage:
  "code_rbound_uuid_preimage (response_config_policy_binding oip_binder_config) oip_binder_response_binding oip_binder_issued =
    response_fixed_uuid_preimage oip_binder_config oip_binder_response_binding oip_binder_issued"
  by (simp add: code_rbound_uuid_preimage_def response_fixed_uuid_preimage_def)

definition code_response_uuid_preimage_flat_oracle ::
  "integer list \<Rightarrow> integer list \<Rightarrow> integer \<Rightarrow> (bool \<times> integer list)" where
  "code_response_uuid_preimage_flat_oracle oip_binder_policy_binding oip_binder_response_binding oip_binder_issued =
    (if \<not> code_integer_octet_values (oip_binder_policy_binding @ oip_binder_response_binding) \<or>
        length oip_binder_response_binding \<noteq> 32 \<or> \<not> code_integer_u64_values [oip_binder_issued]
     then (False,[])
     else (True,map integer_of_nat (code_rbound_uuid_preimage
       (map nat_of_integer oip_binder_policy_binding) (map nat_of_integer oip_binder_response_binding) (nat_of_integer oip_binder_issued))))"

text \<open>
  This is a lower message-stage observation, not a replacement for the
  source sender's original preflight or whole response acceptance. Its
  caller must already have the actual original, typed boundary return and
  channel atomicity getter. Whole sender order remains the received
  response_fixed_encode_for_received_original entry.
  SHA256(response binding preimage) is a named primitive result. It must be
  independently computed from the first model request before the second
  UUID request is evaluated; an observed source digest/UUID is not an input.
\<close>

end
