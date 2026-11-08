theory Wire_Product_Execution
  imports Wire_Product_Read
begin

record wire_native_call =
  native_reference :: nat
  native_id :: client_call_id
  native_session :: product_session_id
  native_cut :: product_cut
  native_origin_epoch :: nat
  native_origin :: source_key
  native_asset :: product_asset
  native_funding_owner :: product_principal
  native_destination :: nat
  native_recipient :: nat
  native_amount :: nat
  native_tail_words :: "nat list"
  native_proof_bytes :: "wire_bytes list"

definition decode_native_call_prefix where
  "decode_native_call_prefix core =
    (let body = wire_operation_body core; words = wire_words body in
      if length words < 11 then None else
      case wire_blobs body of [] \<Rightarrow> None | amount # proofs \<Rightarrow>
        if length amount \<noteq> 32 \<or> \<not> wire_octets amount then None else Some
          \<lparr>native_reference = words ! 0, native_id = (wire_principal core, words ! 1), native_session = words ! 2,
            native_cut = \<lparr>cut_authority_epoch = wire_authority_epoch core, cut_revision = words ! 3\<rparr>,
            native_origin_epoch = words ! 4, native_origin = (words ! 5, words ! 6),
            native_asset = words ! 7, native_funding_owner = words ! 8, native_destination = words ! 9,
            native_recipient = words ! 10, native_amount = get_le_octets (rev amount),
            native_tail_words = drop 11 words, native_proof_bytes = proofs\<rparr>)"

lemma native_transport_never_truncates_the_caller_namespace_or_epoch:
  assumes "decode_native_call_prefix core = Some native"
  shows "fst (native_id native) = wire_principal core \<and>
    cut_authority_epoch (native_cut native) = wire_authority_epoch core"
  using assms by (auto simp: decode_native_call_prefix_def Let_def split: list.splits if_splits)

definition native_envelope_matches where
  "native_envelope_matches core native call_id payload \<longleftrightarrow>
    (let envelope = payload_envelope payload in
      call_id = native_id native \<and> envelope_message envelope = native_reference native \<and>
      envelope_caller envelope = wire_principal core \<and> envelope_session envelope = native_session native \<and>
      envelope_cut envelope = native_cut native \<and> envelope_origin envelope = native_origin native \<and>
      envelope_asset envelope = native_asset native \<and> payload_origin_epoch payload = native_origin_epoch native \<and>
      command_target envelope (envelope_command envelope) = wire_target_domain core)"

lemma accepted_native_payload_consumes_the_signed_identity_and_exact_cut:
  assumes "decode_native_call_prefix core = Some native"
    "native_envelope_matches core native call_id payload"
  shows "fst call_id = wire_principal core \<and>
    envelope_caller (payload_envelope payload) = wire_principal core \<and>
    cut_authority_epoch (envelope_cut (payload_envelope payload)) = wire_authority_epoch core \<and>
    command_target (payload_envelope payload) (envelope_command (payload_envelope payload)) = wire_target_domain core"
  using assms native_transport_never_truncates_the_caller_namespace_or_epoch[OF assms(1)]
  by (simp add: native_envelope_matches_def Let_def)

context source_attestation
begin

definition consume_wire_in_current_product where
  "consume_wire_in_current_product verify_signature source_verified body_allowed authority decode run bytes cache retained =
    (case receive_canonical_wire verify_signature source_verified body_allowed authority bytes cache of
       (updated, Wire_First packet) \<Rightarrow>
         (case decode (packet_core packet) of None \<Rightarrow> (cache, retained, None)
          | Some action \<Rightarrow> let result = run action retained in (updated, fst result, Some (snd result)))
     | (updated, Wire_Identical packet) \<Rightarrow>
         (case decode (packet_core packet) of None \<Rightarrow> (cache, retained, None)
          | Some action \<Rightarrow> let result = run action retained in (updated, fst result, Some (snd result)))
     | (_, Wire_Rejected _) \<Rightarrow> (cache, retained, None))"

lemma a_rejected_wire_envelope_cannot_enter_the_product_consumer:
  assumes "wire_gate verify_signature source_verified body_allowed authority bytes = Gate_Refused reason"
  shows "consume_wire_in_current_product verify_signature source_verified body_allowed authority decode run bytes cache retained =
    (cache, retained, None)"
  using assms by (simp add: consume_wire_in_current_product_def receive_canonical_wire_def)

lemma the_actual_product_receiver_gets_only_the_action_decoded_from_the_verified_core:
  assumes "consume_wire_in_current_product verify_signature source_verified body_allowed authority decode run bytes cache retained =
    (updated, after, Some reply)"
  obtains packet action where "wire_gate verify_signature source_verified body_allowed authority bytes = Gate_Admitted packet"
    "decode (packet_core packet) = Some action" "run action retained = (after, reply)"
  using assms
  by (cases "wire_gate verify_signature source_verified body_allowed authority bytes")
    (auto simp: consume_wire_in_current_product_def receive_canonical_wire_def Let_def split: option.splits if_splits)

end

end
