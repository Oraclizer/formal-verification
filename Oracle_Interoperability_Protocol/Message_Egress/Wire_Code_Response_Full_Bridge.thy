theory Wire_Code_Response_Full_Bridge
  imports Wire_Code_Response_Full_Prefix
begin

lemma the_full_sender_is_the_existing_original_preflight_encoder:
  fixes oip_full_context :: code_response_full_context and oip_full_observation :: response_fixed_observation
    and oip_full_original :: wire_bytes and oip_full_hashes :: code_full_hash_table
    and oip_full_signatures :: code_full_sign_table and oip_full_verifications :: code_full_verify_table
  shows "code_full_sender oip_full_context oip_full_observation oip_full_original
      oip_full_hashes oip_full_signatures oip_full_verifications =
    response_fixed_encode_for_received_original (code_full_hash oip_full_hashes)
      (code_full_sign oip_full_signatures (response_channel_local_key (full_response_channel oip_full_context))) ()
      (code_full_verify oip_full_verifications)
      (full_response_config oip_full_context) (full_response_channel oip_full_context) (full_response_site oip_full_context)
      (full_parameters_clock oip_full_context) (full_signing_clock oip_full_context)
      oip_full_original oip_full_observation (full_response_frame_limit oip_full_context)"
  by (simp add: code_full_sender_def)

lemma a_full_emission_keeps_its_actual_original_preflight:
  fixes oip_full_context :: code_response_full_context and oip_full_observation :: response_fixed_observation
    and oip_full_bytes :: wire_bytes and oip_full_hashes :: code_full_hash_table
    and oip_full_signatures :: code_full_sign_table and oip_full_verifications :: code_full_verify_table
    and oip_full_emission :: response_fixed_emission
  assumes emitted: "code_full_sender oip_full_context oip_full_observation oip_full_bytes
    oip_full_hashes oip_full_signatures oip_full_verifications = Inr oip_full_emission"
  obtains oip_full_original oip_full_call
  where
    "response_fixed_original_preflight (full_response_config oip_full_context)
       (full_response_channel oip_full_context) (full_response_site oip_full_context)
       (code_full_verify oip_full_verifications) (full_response_frame_limit oip_full_context)
       oip_full_bytes = Inr (oip_full_original,oip_full_call)"
    "response_emission_original oip_full_emission = packet_core oip_full_original"
    "response_fixed_raw_core oip_full_bytes = Some (encode_wire_core (response_emission_original oip_full_emission))"
proof -
  have actual: "response_fixed_encode_for_received_original (code_full_hash oip_full_hashes)
      (code_full_sign oip_full_signatures (response_channel_local_key (full_response_channel oip_full_context))) ()
      (code_full_verify oip_full_verifications)
      (full_response_config oip_full_context) (full_response_channel oip_full_context) (full_response_site oip_full_context)
      (full_parameters_clock oip_full_context) (full_signing_clock oip_full_context)
      oip_full_bytes oip_full_observation (full_response_frame_limit oip_full_context) = Inr oip_full_emission"
    using emitted by (simp only: code_full_sender_def)
  show thesis
    by (rule response_fixed_received_original_cannot_be_replaced_at_the_encoding_interface[OF actual])
      (use that in blast)
qed

lemma a_boundary_emission_is_the_existing_encoder_of_its_decoded_input:
  fixes oip_full_context :: code_response_full_context and oip_full_observation :: response_fixed_observation
    and oip_full_bytes :: wire_bytes and oip_full_hashes :: code_full_hash_table
    and oip_full_signatures :: code_full_sign_table and oip_full_verifications :: code_full_verify_table
    and oip_full_emission :: response_fixed_emission
  assumes "code_full_boundary_sender oip_full_context oip_full_observation oip_full_bytes
    oip_full_hashes oip_full_signatures oip_full_verifications = Inr oip_full_emission"
  obtains oip_full_original oip_full_call
  where
    "decode_wire_packet oip_full_bytes = Some oip_full_original"
    "code_response_caller (packet_core oip_full_original) = Inr oip_full_call"
    "response_fixed_encode (code_full_hash oip_full_hashes)
      (code_full_sign oip_full_signatures (response_channel_local_key (full_response_channel oip_full_context))) ()
      (code_full_verify oip_full_verifications)
      (full_response_config oip_full_context) (full_response_channel oip_full_context)
      (full_parameters_clock oip_full_context) (full_signing_clock oip_full_context)
      (packet_core oip_full_original) oip_full_call oip_full_observation
      (full_response_frame_limit oip_full_context) = Inr oip_full_emission"
  using assms by (auto simp: code_full_boundary_sender_def split: option.splits sum.splits)

lemma a_boundary_emission_returns_the_actual_converted_kind_number_and_position:
  fixes oip_full_context :: code_response_full_context and oip_full_observation :: response_fixed_observation
    and oip_full_bytes :: wire_bytes and oip_full_hashes :: code_full_hash_table
    and oip_full_signatures :: code_full_sign_table and oip_full_verifications :: code_full_verify_table
    and oip_full_emission :: response_fixed_emission
  assumes emitted: "code_full_boundary_sender oip_full_context oip_full_observation oip_full_bytes
    oip_full_hashes oip_full_signatures oip_full_verifications = Inr oip_full_emission"
  shows "response_emission_verified oip_full_emission = response_emission_converted oip_full_emission"
proof (rule a_boundary_emission_is_the_existing_encoder_of_its_decoded_input[OF emitted])
  fix oip_bridge_original :: wire_packet and oip_bridge_call :: client_call_id
  assume oip_bridge_decoded: "decode_wire_packet oip_full_bytes = Some oip_bridge_original"
    and oip_bridge_caller: "code_response_caller (packet_core oip_bridge_original) = Inr oip_bridge_call"
    and oip_bridge_encoded:
      "response_fixed_encode (code_full_hash oip_full_hashes)
        (code_full_sign oip_full_signatures (response_channel_local_key (full_response_channel oip_full_context))) ()
        (code_full_verify oip_full_verifications)
        (full_response_config oip_full_context) (full_response_channel oip_full_context)
        (full_parameters_clock oip_full_context) (full_signing_clock oip_full_context)
        (packet_core oip_bridge_original) oip_bridge_call oip_full_observation
        (full_response_frame_limit oip_full_context) = Inr oip_full_emission"
  show "response_emission_verified oip_full_emission = response_emission_converted oip_full_emission"
    by (rule response_fixed_emission_returns_the_exact_converted_kind_code_and_position[OF oip_bridge_encoded])
qed

lemma the_full_client_does_not_substitute_the_emitters_boundary:
  fixes oip_full_channel :: response_fixed_channel and oip_full_current :: response_fixed_client_boundary
    and oip_full_expected :: wire_packet and oip_full_received :: wire_bytes
    and oip_full_verifications :: code_full_verify_table
  shows "code_full_client oip_full_channel oip_full_current oip_full_expected oip_full_received oip_full_verifications =
    response_fixed_admit (code_full_verify oip_full_verifications)
      oip_full_channel oip_full_current oip_full_expected oip_full_received"
  by (simp add: code_full_client_def)

lemma an_admitted_client_uses_its_own_peer_key_and_received_preimage:
  fixes oip_full_channel :: response_fixed_channel and oip_full_current :: response_fixed_client_boundary
    and oip_full_expected :: wire_packet and oip_full_received :: wire_bytes
    and oip_full_verifications :: code_full_verify_table and oip_full_result :: "client_call_id \<times> reference_response_kind \<times> nat \<times> nat option"
    and oip_full_status :: "code_response_status option"
  assumes admitted: "code_full_client oip_full_channel oip_full_current oip_full_expected
    oip_full_received oip_full_verifications = Inr (oip_full_result,oip_full_status)"
  obtains oip_full_packet
  where
    "decode_wire_packet oip_full_received = Some oip_full_packet"
    "code_full_verify oip_full_verifications (response_channel_remote_key oip_full_channel)
      (envelope_signing_bytes (packet_core oip_full_packet)) (packet_signature oip_full_packet)"
proof -
  have actual: "response_fixed_admit (code_full_verify oip_full_verifications)
      oip_full_channel oip_full_current oip_full_expected oip_full_received = Inr (oip_full_result,oip_full_status)"
    using admitted by (simp only: code_full_client_def)
  show thesis
    by (rule response_fixed_client_admission_verifies_the_exact_received_preimage_with_the_current_peer[OF actual])
      (use that in blast)
qed

lemma an_admitted_client_keeps_a_typed_known_or_unknown_status:
  fixes oip_full_channel :: response_fixed_channel and oip_full_current :: response_fixed_client_boundary
    and oip_full_expected :: wire_packet and oip_full_received :: wire_bytes
    and oip_full_verifications :: code_full_verify_table and oip_full_result :: "client_call_id \<times> reference_response_kind \<times> nat \<times> nat option"
    and oip_full_status :: "code_response_status option"
  assumes "code_full_client oip_full_channel oip_full_current oip_full_expected
    oip_full_received oip_full_verifications = Inr (oip_full_result,oip_full_status)"
  shows "oip_full_status \<noteq> None"
proof -
  have actual: "response_fixed_admit (code_full_verify oip_full_verifications)
      oip_full_channel oip_full_current oip_full_expected oip_full_received = Inr (oip_full_result,oip_full_status)"
    using assms by (simp only: code_full_client_def)
  show ?thesis by (rule response_fixed_client_admission_always_has_a_typed_known_or_unknown_status[OF actual])
qed

lemma an_admitted_general_client_consumes_the_existing_hol_correlation:
  fixes oip_full_channel :: response_fixed_channel and oip_full_current :: response_fixed_client_boundary
    and oip_full_expected :: wire_packet and oip_full_received :: wire_bytes
    and oip_full_verifications :: code_full_verify_table and oip_full_result :: "client_call_id \<times> reference_response_kind \<times> nat \<times> nat option"
    and oip_full_status :: "code_response_status option" and oip_full_fuel :: nat
    and oip_full_operand :: code_source_call_operand
  assumes admitted: "code_full_client oip_full_channel oip_full_current oip_full_expected
    oip_full_received oip_full_verifications = Inr (oip_full_result,oip_full_status)"
    and depth: "response_client_max_nesting oip_full_current = Suc oip_full_fuel"
    and formed: "wire_core_wellformed (packet_core oip_full_expected)"
    and selected: "response_general_nonordinary (packet_core oip_full_expected) = Some oip_full_operand"
  shows "map_option (code_correlate_reference_response (packet_core oip_full_expected))
    (decode_wire_packet oip_full_received) = Some (Some oip_full_result)"
proof -
  have actual: "response_fixed_admit (code_full_verify oip_full_verifications)
      oip_full_channel oip_full_current oip_full_expected oip_full_received = Inr (oip_full_result,oip_full_status)"
    using admitted by (simp only: code_full_client_def)
  show ?thesis
    by (rule response_general_current_client_correlates_the_same_legal_or_spend_original[OF actual depth formed selected])
qed

lemma combined_client_input_is_only_the_model_senders_packet:
  fixes oip_full_rows oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows oip_full_client_rows oip_full_client_verify_rows :: "integer list list"
    and oip_full_mode :: integer and oip_full_reply oip_full_retained oip_full_original :: "integer list"
    and oip_full_retained_present :: bool and oip_full_output :: "integer list list"
  assumes sender: "code_response_egress_flat_oracle oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present
    oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows = (0,oip_full_output)"
  shows "code_response_egress_and_admit_flat_oracle oip_full_rows oip_full_mode oip_full_reply oip_full_retained_present
      oip_full_retained oip_full_original oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows
      oip_full_client_rows oip_full_client_verify_rows =
    (0,oip_full_output,
      fst (code_response_admit_flat_oracle oip_full_client_rows oip_full_original (oip_full_output ! 12) oip_full_client_verify_rows),
      snd (code_response_admit_flat_oracle oip_full_client_rows oip_full_original (oip_full_output ! 12) oip_full_client_verify_rows))"
  using sender by (simp add: code_response_egress_and_admit_flat_oracle_def Let_def split: prod.splits)

lemma the_whole_planner_has_no_response_requests_before_original_preflight:
  fixes oip_full_context :: code_response_full_context and oip_full_observation :: response_fixed_observation
    and oip_full_bytes :: wire_bytes and oip_full_hashes :: code_full_hash_table
    and oip_full_signatures :: code_full_sign_table and oip_full_verifications :: code_full_verify_table
    and oip_full_queries :: "nat list list"
  assumes "code_full_original_selection oip_full_context oip_full_bytes oip_full_verifications = (None,oip_full_queries)"
  shows "code_full_sender_queries True oip_full_context oip_full_observation oip_full_bytes
    oip_full_hashes oip_full_signatures oip_full_verifications = oip_full_queries"
  using assms by (simp add: code_full_sender_queries_def)

lemma an_absent_boundary_result_preserves_the_existing_preflight_refusal:
  fixes oip_full_context :: code_response_full_context and oip_full_bytes :: wire_bytes
    and oip_full_verifications :: code_full_verify_table
    and oip_full_selected :: "(wire_packet \<times> client_call_id) option" and oip_full_reason :: wire_refusal
  assumes planned: "code_full_original_selection oip_full_context oip_full_bytes oip_full_verifications = (oip_full_selected,[])"
    and refused: "response_fixed_original_preflight (full_response_config oip_full_context)
      (full_response_channel oip_full_context) (full_response_site oip_full_context)
      (code_full_verify oip_full_verifications) (full_response_frame_limit oip_full_context)
      oip_full_bytes = Inl oip_full_reason"
  shows "code_full_without_result oip_full_context oip_full_bytes oip_full_verifications =
    (integer_of_nat (code_transport_refusal_number oip_full_reason),[])"
  using planned refused by (simp add: code_full_without_result_def)

lemma a_ready_call_without_an_actual_boundary_result_is_incomplete:
  fixes oip_full_context :: code_response_full_context and oip_full_bytes :: wire_bytes
    and oip_full_verifications :: code_full_verify_table
    and oip_full_selected :: "(wire_packet \<times> client_call_id) option"
    and oip_full_original :: wire_packet and oip_full_call :: client_call_id
  assumes planned: "code_full_original_selection oip_full_context oip_full_bytes oip_full_verifications = (oip_full_selected,[])"
    and ready: "response_fixed_original_preflight (full_response_config oip_full_context)
      (full_response_channel oip_full_context) (full_response_site oip_full_context)
      (code_full_verify oip_full_verifications) (full_response_frame_limit oip_full_context)
      oip_full_bytes = Inr (oip_full_original,oip_full_call)"
  shows "code_full_without_result oip_full_context oip_full_bytes oip_full_verifications = (-1,[])"
  using planned ready by (simp add: code_full_without_result_def)

end
