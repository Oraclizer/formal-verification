theory Response_Egress_V061_Preservation
  imports "OIP_Response_Egress_V061_V5.Response_Egress_V061_Packet"
begin

lemma response_v061_config_flags_are_independent:
  "response_v061_accepts accept_sync accept_current Wire_State_Sync 7 = accept_sync"
  "response_v061_accepts accept_sync accept_current Wire_Query 9 = accept_current"
  by (simp_all add: response_v061_accepts_def reference_accepts_write_def)

lemma response_v061_legacy_canonical_packet_preserves_opcode_and_bytes:
  assumes "decode_wire_packet raw = Some packet"
  shows "sync_decode_packet raw = Some packet" "encode_wire_packet packet = raw"
    "valid_family_opcode (wire_message_family (packet_core packet)) (wire_opcode (wire_operation_body (packet_core packet)))"
proof -
  show "sync_decode_packet raw = Some packet"
    by (rule sync_preserves_every_decoded_legacy_packet[OF assms])
  then show "encode_wire_packet packet = raw" by (rule sync_decoded_packet_has_the_exact_bytes)
  have "wire_packet_wellformed packet"
    using every_accepted_wire_message_has_exactly_the_received_bytes[OF assms] by blast
  then show "valid_family_opcode (wire_message_family (packet_core packet)) (wire_opcode (wire_operation_body (packet_core packet)))"
    by (auto simp: wire_packet_wellformed_def wire_core_wellformed_def)
qed

lemma response_v061_legacy_status_preserves_the_old_known_and_unknown_value:
  assumes "\<not> sync_added_status number" "sync_operation original \<noteq> (Wire_State_Sync,7)"
  shows "response_v061_status original kind number position =
    (if code_known_response_number number \<and>
        \<not> reference_response_compatible (wire_message_family original) (wire_opcode (wire_operation_body original))
          kind number (position \<noteq> None)
     then None else code_decode_response_status kind number (position \<noteq> None))"
  using assms by (auto simp: response_v061_status_def Let_def sync_added_status_def sync_operation_def
    response_extended_status_def response_extended_compatible_def sync_response_lookup_is_exact sync_response_operation_def
    code_response_compatible_def code_decode_response_status_def split: if_splits)

lemma response_v061_query_eight_and_ack_two_are_not_original_callers:
  assumes "sync_operation core \<in> {(Wire_Query,8),(Wire_Ack,2)}"
  shows "response_v061_original_caller core = Inl Invalid_Wire_Format"
    "code_response_caller core = Inl Invalid_Wire_Format"
proof -
  have query_case: "response_v061_original_caller core = Inl Invalid_Wire_Format \<and>
      code_response_caller core = Inl Invalid_Wire_Format"
    if query: "sync_operation core = (Wire_Query,8)"
  proof
    show "response_v061_original_caller core = Inl Invalid_Wire_Format"
      using query by (simp add: response_v061_original_caller_def One_nat_def Let_def)
    have "wire_message_family core = Wire_Query" using query by (simp add: sync_operation_def)
    then show "code_response_caller core = Inl Invalid_Wire_Format"
      by (rule response_general_query_has_no_depth_one_response_caller)
  qed
  have ack_case: "response_v061_original_caller core = Inl Invalid_Wire_Format \<and>
      code_response_caller core = Inl Invalid_Wire_Format"
    if ack: "sync_operation core = (Wire_Ack,2)"
  proof
    have new_layer: "response_v061_parse_layer True (response_v061_operand 0) core = Inl Invalid_Wire_Format"
      by (simp add: response_v061_parse_layer_def ack Let_def split: list.splits option.splits)
    show "response_v061_original_caller core = Inl Invalid_Wire_Format"
      by (simp add: response_v061_original_caller_def One_nat_def Let_def ack new_layer)
    have family: "wire_message_family core = Wire_Ack"
      and opcode: "wire_opcode (wire_operation_body core) = 2"
      using ack by (simp_all add: sync_operation_def)
    show "code_response_caller core = Inl Invalid_Wire_Format"
      by (simp add: code_response_caller_def One_nat_def Let_def family opcode
        an_inner_failure_precedes_every_response_word_or_header_check split: list.splits option.splits)
  qed
  have both: "response_v061_original_caller core = Inl Invalid_Wire_Format \<and>
      code_response_caller core = Inl Invalid_Wire_Format"
    using assms query_case ack_case by auto
  from both show "response_v061_original_caller core = Inl Invalid_Wire_Format" by simp
  from both show "code_response_caller core = Inl Invalid_Wire_Format" by simp
qed

lemma response_v061_original_preflight_keeps_all_other_legacy_originals:
  assumes decoded: "decode_wire_packet raw = Some packet"
    and op: "sync_operation (packet_core packet) \<notin> {(Wire_Lock,7),(Wire_State_Sync,7),(Wire_Query,9)}"
    and mode: "selected_mode = response_fixed_atomicity (full_response_channel context)"
  shows "response_v061_original_preflight context accept_sync accept_current selected_mode verify raw =
    response_fixed_original_preflight (full_response_config context) (full_response_channel context)
      (full_response_site context) verify (full_response_frame_limit context) raw"
proof (cases "sync_operation (packet_core packet) \<in> {(Wire_Query,8),(Wire_Ack,2)}")
  case False
  show ?thesis
    by (rule response_v061_original_preflight_keeps_old_configured_operations[OF decoded _ mode]) (use False op in auto)
next
  case True
  have legacy_op: "code_check_operation (response_v061_accepts accept_sync accept_current) (packet_core packet) =
      code_check_operation code_reference_accepts (packet_core packet)"
    using op by (auto simp: sync_operation_def code_check_operation_def response_v061_accepts_def reference_accepts_write_def)
  have v061_caller: "response_v061_original_caller (packet_core packet) = code_response_caller (packet_core packet)"
    using response_v061_query_eight_and_ack_two_are_not_original_callers[OF True] by simp
  show ?thesis
    by (simp add: response_v061_original_preflight_def response_fixed_original_preflight_def code_original_response_preflight_def
      response_fixed_channel_guard_def response_fixed_original_signature_def Let_def decoded
      sync_preserves_every_decoded_legacy_packet[OF decoded] mode legacy_op v061_caller
      cong: if_cong option.case_cong sum.case_cong)
qed

theorem response_v061_success_preserves_legacy_signed_bytes:
  assumes prior: "response_fixed_encode hash (\<lambda>_ preimage. v061_sign (response_channel_local_key (full_response_channel context)) preimage) ()
    verify (full_response_config context) (full_response_channel context) (full_parameters_clock context) (full_signing_clock context)
    original call observation (full_response_frame_limit context) = Inr before"
    and current: "response_v061_encode hash v061_sign verify context selected_mode original call (response_fixed_result observation) = Inr after"
    and mode: "selected_mode = response_fixed_atomicity (full_response_channel context)"
  shows "response_emission_binding_preimage after = response_emission_binding_preimage before"
    "response_emission_signing_preimage after = response_emission_signing_preimage before"
    "response_emission_bytes after = response_emission_bytes before"
proof -
  let ?channel = "full_response_channel context"
  let ?config = "full_response_config context"
  let ?v061_key = "response_channel_local_key ?channel"
  let ?old_sign = "\<lambda>(_ :: unit) preimage. v061_sign ?v061_key preimage"
  let ?result = "response_fixed_result observation"
  obtain old_kind old_code old_position old_words old_mode old_params old_core old_sig old_packet old_bytes where old:
    "response_fixed_words call ?result = Some (old_kind,old_code,old_position,old_words)"
    "response_fixed_atomicity ?channel = Some old_mode"
    "response_emission_binding_preimage before = response_fixed_binding_preimage (encode_wire_core original) old_mode old_words"
    "response_fixed_parameters_from hash ?config ?channel (full_parameters_clock context)
      (hash (response_emission_binding_preimage before)) = Some old_params"
    "old_core = response_fixed_core ?channel old_params old_mode old_words (encode_wire_core original)"
    "response_emission_signing_preimage before = envelope_signing_bytes old_core"
    "response_fixed_sign ?old_sign () ?config (full_signing_clock context) (envelope_signing_bytes old_core) = Some old_sig"
    "old_packet = \<lparr>packet_core = old_core,packet_signature = old_sig\<rparr>"
    "code_encode_packet old_packet = Some old_bytes"
    "response_emission_bytes before = old_bytes"
    by (rule response_fixed_encoding_has_actual_source_getter_preimage_and_postcheck_evidence[OF prior]) blast
  obtain new_kind new_code new_position new_words new_mode new_params new_core core_bytes status where new:
    "response_v061_words call ?result = Some (new_kind,new_code,new_position,new_words)"
    "selected_mode = Some new_mode"
    "response_emission_binding_preimage after = response_fixed_binding_preimage (encode_wire_core original) new_mode new_words"
    "response_fixed_parameters_from hash ?config ?channel (full_parameters_clock context)
      (hash (response_emission_binding_preimage after)) = Some new_params"
    "new_core = response_fixed_core ?channel new_params new_mode new_words (encode_wire_core original)"
    "response_emission_signing_preimage after = envelope_signing_bytes new_core"
    "code_encode_packet \<lparr>packet_core = new_core,packet_signature = v061_sign ?v061_key (response_emission_signing_preimage after)\<rparr> =
      Some (response_emission_bytes after)"
    by (rule response_v061_encoding_projects_the_exact_preimages_and_packet[OF current]) blast
  obtain original_number original_position where result: "?result = (original_number,original_position)"
    by (cases ?result) blast
  have old_words: "response_fixed_words call (original_number,original_position) = Some (old_kind,old_code,old_position,old_words)"
    using old(1) by (simp add: result)
  have descriptor: "response_fixed_descriptor original_number = Some (old_kind,original_position \<noteq> None)"
    by (rule response_fixed_words_keep_the_actual_position_without_replacing_it_by_a_cut(4)[OF old_words])
  have member: "original_number \<in> reference_result_codes old_kind (original_position \<noteq> None)"
    using descriptor response_fixed_descriptor_is_the_literal_source_kind_commit_table by blast
  have known: "code_known_response_number (fst ?result)"
    using member by (cases old_kind; cases "original_position = None")
      (auto simp: result code_known_response_number_def reference_result_codes_def)
  have code: "\<not> sync_added_status (fst ?result)"
  proof
    assume added: "sync_added_status (fst ?result)"
    have allocated: "fst ?result \<in> {29,39,40,41}" using added unfolding sync_added_status_def .
    have unknown: "\<not> code_known_response_number (fst ?result)"
      by (rule sync_response_numbers_are_legacy_unknown[OF allocated])
    from known unknown show False by contradiction
  qed
  have words_eq: "response_v061_words call ?result = response_fixed_words call ?result"
    using code by (cases ?result) (simp add: response_v061_legacy_words_are_byte_inputs_of_the_old_encoder)
  have new_words: "new_words = old_words" using words_eq old(1) new(1) by simp
  have new_mode: "new_mode = old_mode" using mode old(2) new(2) by simp
  show binding: "response_emission_binding_preimage after = response_emission_binding_preimage before"
    using new_words new_mode old(3) new(3) by simp
  have new_params: "new_params = old_params" using old(4) new(4) binding by simp
  have new_core: "new_core = old_core" using new_words new_mode new_params old(5) new(5) by simp
  show preimage: "response_emission_signing_preimage after = response_emission_signing_preimage before"
    using old(6) new(6) new_core by simp
  have sig: "old_sig = v061_sign ?v061_key (envelope_signing_bytes old_core)"
    using old(7) by (auto simp: response_fixed_sign_def split: option.splits if_splits)
  show "response_emission_bytes after = response_emission_bytes before"
    using old(8-10) new(7) new_core new(6) sig by simp
qed

theorem response_v061_sync_signed_correlation_uses_the_exact_direct_original:
  assumes outer: "sync_operation (packet_core packet) = (Wire_Ack,2)"
    "wire_deadline (wire_operation_body (packet_core packet)) = Deadline_Absent"
    "wire_blobs (wire_operation_body (packet_core packet)) = [exact]"
    and original: "sync_decode_core exact = Some expected"
    "sync_operation expected = (Wire_State_Sync,7)" "sync_read_operands expected = Some request"
    and words: "response_result_words (wire_words (wire_operation_body (packet_core packet))) =
      Some (sync_call request,kind,number,position)"
    and header: "sync_link_response_header (packet_core packet) expected (sync_call request)"
    and shape: "kind = Recorded_Result \<or> position = None"
    and status: "response_v061_status expected kind number position = Some actual_status"
  shows "response_v061_validate (Suc (Suc fuel)) expected packet = Inr ((sync_call request,kind,number,position),Some actual_status)"
proof -
  let ?view = "\<lparr>response_decoded_id = sync_call request,response_decoded_kind = kind,
    response_decoded_number = number,response_decoded_position = position,
    response_decoded_original_bytes = exact,response_decoded_original = expected\<rparr>"
  have no_bad_kind: "\<not> (kind \<noteq> Recorded_Result \<and> position \<noteq> None)" using shape by blast
  have parsed: "response_v061_parse False (Suc (Suc fuel)) (packet_core packet) = Inr ?view"
    using outer original words header no_bad_kind
    by (simp add: response_v061_parse_def response_v061_parse_layer_def response_v061_finish_parse_def
      response_v061_check_enclosed_def Let_def)
  have encoded: "encode_wire_core expected = exact" by (rule sync_decoded_core_has_the_exact_bytes[OF original(1)])
  show ?thesis using parsed original(2,3) encoded status
    by (simp add: response_v061_validate_def response_v061_result_of_view_def One_nat_def Let_def)
qed

theorem response_v061_successful_sync_signed_result_uses_the_selected_position:
  assumes selected: "sync_reference_product transport gate verify (packet_core original) state = (next,Sync_Reference_Outcome (Sync_Committed position))"
    and emitted: "response_v061_encode hash v061_sign curve_verify context selected_mode (packet_core original) call
      (response_v061_result (response_v061_sync_product_observation (packet_core original) next
          (Sync_Reference_Outcome (Sync_Committed position)))) = Inr emission"
  shows "response_emission_converted emission = (call,Recorded_Result,29,Some position)"
    "response_emission_original emission = packet_core original"
proof -
  have converted: "response_v061_result (response_v061_sync_product_observation (packet_core original) next
      (Sync_Reference_Outcome (Sync_Committed position))) = (29,Some position)"
    using response_v061_sync_product_projects_the_selected_outcome[OF selected] by simp
  have encoded: "response_v061_encode hash v061_sign curve_verify context selected_mode (packet_core original) call (29,Some position) = Inr emission"
    using emitted converted by simp
  obtain kind code commit words where actual:
    "response_v061_words call (29,Some position) = Some (kind,code,commit,words)"
    "response_emission_original emission = packet_core original"
    "response_emission_converted emission = (call,kind,code,commit)"
    by (rule response_v061_encoding_projects_the_exact_preimages_and_packet[OF encoded]) blast
  show "response_emission_converted emission = (call,Recorded_Result,29,Some position)"
    using actual response_v061_new_words_keep_the_result_commit_position(1)[of "fst call" "snd call" position] by simp
  show "response_emission_original emission = packet_core original" by (rule actual(2))
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms response_v061_config_flags_are_independent
    response_v061_legacy_canonical_packet_preserves_opcode_and_bytes
    response_v061_legacy_status_preserves_the_old_known_and_unknown_value
    response_v061_original_preflight_keeps_all_other_legacy_originals
    response_v061_success_preserves_legacy_signed_bytes
    response_v061_sync_signed_correlation_uses_the_exact_direct_original
    response_v061_successful_sync_signed_result_uses_the_selected_position})
  then () else error "Unexpected oracle in v0.6.1 response preservation"
\<close>

end
