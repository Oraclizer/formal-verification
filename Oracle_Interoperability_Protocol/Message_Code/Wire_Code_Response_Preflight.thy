theory Wire_Code_Response_Preflight
  imports Wire_Code_Operand_Tree Wire_Code_Response_Size Wire_Code_Path_Guards
begin

definition code_response_caller where
  "code_response_caller core =
    (case code_decode_operand_tree 1 core of
       Code_Tree_Ready (Code_Nested_Ordinary native command) \<Rightarrow> Inr (native_id native)
     | Code_Tree_Ready (Code_Nested_Legal call_id) \<Rightarrow> Inr call_id
     | Code_Tree_Ready (Code_Nested_Spend call_id) \<Rightarrow> Inr call_id
     | Code_Tree_Refused reason \<Rightarrow> Inl reason
     | _ \<Rightarrow> Inl Invalid_Wire_Format)"

definition code_original_signature_refusal where
  "code_original_signature_refusal profile verify_peer packet =
    (let core = packet_core packet in
     if wire_signature_scheme core = 2 then Some Invalid_Wire_Threshold
     else if wire_signature_scheme core \<notin> negotiated_schemes profile \<or>
       \<not> verify_peer core (envelope_signing_bytes core) (packet_signature packet)
     then Some Invalid_Wire_Signature else None)"

definition code_response_measurement :: "nat option \<Rightarrow> nat \<Rightarrow> wire_refusal + nat" where
  "code_response_measurement selected_atomicity original_length =
    (case selected_atomicity of None \<Rightarrow> Inl Unsupported_Wire_Version | Some mode \<Rightarrow>
      if mode \<notin> {1..3} \<or> code_response_core_length 6 original_length \<ge> 2^32
      then Inl Invalid_Wire_Format else Inr (code_response_packet_length 6 original_length))"

text \<open>
  selected_atomicity is the value projection of BTreeSet::first on the
  negotiated atomicity set.  Its minimum-selection correspondence is a
  separate FFI obligation.  The booleans below are source attachment and
  channel-configuration checks, not a substitute for decoding a caller.
\<close>

definition code_original_response_preflight where
  "code_original_response_preflight profile channel ordered_available revocation_matches registered_deployment
      frame_limit selected_atomicity verify_peer bytes =
    (if negotiated_version profile \<noteq> 6 \<or> \<not> code_profile_allows profile Wire_Ack 2
     then Inl Unsupported_Wire_Version
     else if \<not> ordered_available \<or> \<not> revocation_matches \<or> \<not> guard_channel_current channel \<or>
       guard_channel_deployment channel \<noteq> registered_deployment then Inl Invalid_Wire_Source
     else case code_check_declared_version bytes frame_limit of Some reason \<Rightarrow> Inl reason
      | None \<Rightarrow> (case decode_wire_packet bytes of None \<Rightarrow> Inl Invalid_Wire_Format | Some packet \<Rightarrow>
         let core = packet_core packet in
         if code_check_operation code_reference_accepts core \<noteq> None then Inl Unsupported_Wire_Version
         else if wire_version core \<noteq> negotiated_version profile \<or>
           wire_deployment core \<noteq> guard_channel_deployment channel \<or>
           wire_source_domain core \<noteq> guard_channel_remote channel \<or>
           wire_target_domain core \<noteq> guard_channel_local channel
         then Inl Invalid_Wire_Source
         else case code_response_caller core of Inl reason \<Rightarrow> Inl reason | Inr call_id \<Rightarrow>
           (case code_response_measurement selected_atomicity (length (encode_wire_core core)) of
              Inl reason \<Rightarrow> Inl reason | Inr measured \<Rightarrow>
                if measured > frame_limit then Inl Invalid_Wire_Format
                else case code_original_signature_refusal profile verify_peer packet of
                  Some reason \<Rightarrow> Inl reason | None \<Rightarrow> Inr (packet,call_id))))"

lemma a_preflight_original_is_verified_with_the_peer_key_before_a_response:
  assumes "code_original_response_preflight profile channel ordered_available revocation_matches registered_deployment
      frame_limit selected_atomicity verify_peer bytes = Inr (packet,call_id)"
  shows "verify_peer (packet_core packet) (envelope_signing_bytes (packet_core packet)) (packet_signature packet)"
    "decode_wire_packet bytes = Some packet"
  using assms by (auto simp: code_original_response_preflight_def code_original_signature_refusal_def Let_def
    split: option.splits sum.splits prod.splits if_splits)

definition code_receive_signed_response where
  "code_receive_signed_response preflight signer_available run encode bytes state =
    (case preflight bytes of Inl reason \<Rightarrow> (state,Inl (Code_Path_Validation reason))
     | Inr (packet,call_id) \<Rightarrow>
       if \<not> signer_available then (state,Inl (Code_Path_Validation Invalid_Wire_Source))
       else let (after,outcome) = run packet call_id state in
         case encode packet call_id outcome of None \<Rightarrow> (after,Inl Code_Path_Response_Lost)
          | Some response \<Rightarrow> (after,Inr response))"

lemma a_failed_original_preflight_has_no_product_effect_or_signed_response:
  assumes "preflight bytes = Inl reason"
  shows "code_receive_signed_response preflight signer_available run encode bytes state =
    (state,Inl (Code_Path_Validation reason))"
  using assms by (simp add: code_receive_signed_response_def)

lemma every_signed_response_passes_the_original_preflight:
  assumes "code_receive_signed_response preflight signer_available run encode bytes state = (after,Inr response)"
  obtains packet call_id where "preflight bytes = Inr (packet,call_id)" "signer_available"
  using assms by (auto simp: code_receive_signed_response_def Let_def
    split: sum.splits prod.splits option.splits if_splits)

theorem every_signed_response_to_the_source_preflight_has_a_verified_original:
  assumes actual: "code_receive_signed_response
      (code_original_response_preflight profile channel ordered_available revocation_matches registered_deployment
        frame_limit selected_atomicity verify_peer) signer_available run encode bytes state = (after,Inr response)"
  obtains packet call_id where "decode_wire_packet bytes = Some packet"
    "verify_peer (packet_core packet) (envelope_signing_bytes (packet_core packet)) (packet_signature packet)"
proof -
  obtain packet call_id where preflight: "code_original_response_preflight profile channel ordered_available
      revocation_matches registered_deployment frame_limit selected_atomicity verify_peer bytes = Inr (packet,call_id)"
    by (rule every_signed_response_passes_the_original_preflight[OF actual])
  note checked = a_preflight_original_is_verified_with_the_peer_key_before_a_response[OF preflight]
  show thesis by (rule that[OF checked(2,1)])
qed

end
