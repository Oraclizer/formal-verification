theory Raw_Terminal_Read_Model_Link
  imports "OIP_Secondary_Read_Export.Secondary_Read_Export"
begin

text \<open>
  The packet and semantic read selector use the existing canonical decoder.
  Status reuses Secondary_Read_G0. The raw two-slot priority below relates
  the a70 ReadProjection source to a bounded current-prefix observation.
  The older canonical raw receipt observation has one terminal-record map.
\<close>

definition rtr_raw_source_terminal :: "nat list secondary_slot option \<Rightarrow>
    nat list secondary_slot option \<Rightarrow> (nat list,nat list) secondary_terminal option" where
  "rtr_raw_source_terminal rtr_transfer rtr_legal =
    (case secondary_slot_decision rtr_legal of
       Some rtr_payload \<Rightarrow> Some (Secondary_Legal rtr_payload)
     | None \<Rightarrow> map_option Secondary_Transfer (secondary_slot_decision rtr_transfer))"

lemma rtr_canonical_terminal_receipt_uses_one_record_map:
  "stored_query (Terminal_Receipt rtr_origin) rtr_snapshot =
    Receipt_Value (snapshot_records rtr_snapshot rtr_origin)"
  by simp

lemma rtr_current_prefix_relation:
  assumes "rtr_revision < length rtr_prefixes"
    "rtr_prefixes ! rtr_revision = (rtr_transfer,rtr_legal)"
  shows "native_history_read_value True
    (\<lambda>rtr_slots. rtr_raw_source_terminal (fst rtr_slots) (snd rtr_slots)) rtr_revision rtr_prefixes =
    Some (rtr_revision,rtr_raw_source_terminal rtr_transfer rtr_legal)"
  using assms by (simp add: native_history_read_value_def)

lemma rtr_raw_source_legal_priority:
  "secondary_slot_decision rtr_legal = Some rtr_payload \<Longrightarrow>
    rtr_raw_source_terminal rtr_transfer rtr_legal = Some (Secondary_Legal rtr_payload)"
  by (simp add: rtr_raw_source_terminal_def)

lemma rtr_raw_source_transfer_fallback:
  "secondary_slot_decision rtr_legal = None \<Longrightarrow>
    rtr_raw_source_terminal rtr_transfer rtr_legal =
      map_option Secondary_Transfer (secondary_slot_decision rtr_transfer)"
  by (simp add: rtr_raw_source_terminal_def)

lemma rtr_raw_terminal_wire_shape:
  assumes "wire_message_family rtr_core = Wire_Query"
    "wire_opcode (wire_operation_body rtr_core) = 3"
    "wire_words (wire_operation_body rtr_core) = [rtr_session,6,rtr_domain,rtr_event]"
    "wire_blobs (wire_operation_body rtr_core) = []"
    "wire_deadline (wire_operation_body rtr_core) = Deadline_Absent"
  shows "code_source_nonreceipt_read_service rtr_token rtr_core = Some
    (Service_Read rtr_token
      \<lparr>proof_session = rtr_session,proof_epoch = wire_authority_epoch rtr_core\<rparr>
      (wire_target_domain rtr_core) (Raw_Data (Terminal_Receipt (rtr_domain,rtr_event))) None)"
  using assms by (simp add: code_source_nonreceipt_read_service_def code_decode_query_nonreceipt_def
      decode_wire_query_body_def parse_wire_application_query_def Let_def)

fun rtr_slot_from_nat :: "nat list \<Rightarrow> nat list secondary_slot option option" where
  "rtr_slot_from_nat (rtr_present # rtr_decision # rtr_published # rtr_slot_length # rtr_decision_length # rtr_bytes) =
    (if rtr_present \<le> 1 \<and> rtr_decision \<le> rtr_present \<and> rtr_published \<le> rtr_present
        \<and> (rtr_present = 0) = (rtr_slot_length = 0)
        \<and> (rtr_decision = 0) = (rtr_decision_length = 0)
        \<and> length rtr_bytes = rtr_slot_length + rtr_decision_length
        \<and> list_all (\<lambda>rtr_byte. rtr_byte < 256) rtr_bytes
     then Some (secondary_export_slot rtr_present rtr_decision rtr_published (drop rtr_slot_length rtr_bytes))
     else None)"
| "rtr_slot_from_nat _ = None"

fun rtr_read_rows :: "nat list \<Rightarrow> wire_core \<Rightarrow>
    nat list secondary_slot option \<Rightarrow> nat list secondary_slot option \<Rightarrow>
    nat list secondary_slot option \<Rightarrow> nat list secondary_slot option \<Rightarrow> nat list list option" where
  "rtr_read_rows [rtr_scope,rtr_epoch,rtr_revision,rtr_prefix_index,rtr_phase_present,rtr_phase,rtr_pending]
      rtr_core rtr_raw_transfer rtr_raw_legal rtr_live_transfer rtr_live_legal =
    (if (rtr_scope \<noteq> 1 \<and> rtr_scope \<noteq> 2) \<or> rtr_prefix_index \<noteq> rtr_revision \<or>
        rtr_phase_present > 1 \<or> (rtr_phase_present = 0 \<and> rtr_phase \<noteq> 0) \<or>
        (rtr_scope = 1 \<and> ((rtr_raw_transfer \<noteq> None \<and> rtr_raw_legal \<noteq> None) \<or>
                              (rtr_live_transfer \<noteq> None \<and> rtr_live_legal \<noteq> None)))
     then None else
     case code_source_nonreceipt_read_service (0::nat) rtr_core of
       Some (Service_Read _ rtr_proof rtr_target (Raw_Data (Terminal_Receipt rtr_origin)) None) \<Rightarrow>
         (if proof_epoch rtr_proof = rtr_epoch \<and> rtr_target = fst rtr_origin then
            Some [[3,proof_session rtr_proof,proof_epoch rtr_proof,rtr_target,fst rtr_origin,snd rtr_origin],
              [1],secondary_export_terminal (rtr_raw_source_terminal rtr_raw_transfer rtr_raw_legal)] else None)
     | Some (Service_Read _ rtr_proof rtr_target (Operation_Status rtr_origin) None) \<Rightarrow>
         (if proof_epoch rtr_proof = rtr_epoch then
            Some [[4,proof_session rtr_proof,proof_epoch rtr_proof,rtr_target,fst rtr_origin,snd rtr_origin],
              [2],secondary_export_status_fields (secondary_status True True rtr_target rtr_origin
                (if rtr_phase_present = 1 then Some rtr_phase else None) rtr_pending rtr_live_transfer rtr_live_legal)] else None)
     | _ \<Rightarrow> None)"
| "rtr_read_rows _ _ _ _ _ _ = None"

fun rtr_packet_rows :: "nat list list \<Rightarrow> nat list list option" where
  "rtr_packet_rows [rtr_meta,rtr_packet_bytes,rtr_expected_core,rtr_expected_preimage,rtr_expected_signature,
      rtr_prefix_transfer,rtr_prefix_legal,rtr_primary_transfer,rtr_primary_legal] =
    (case decode_wire_packet rtr_packet_bytes of None \<Rightarrow> None | Some rtr_packet \<Rightarrow>
      let rtr_core = packet_core rtr_packet; rtr_core_bytes = encode_wire_core rtr_core in
        if wire_version rtr_core \<noteq> 6 \<or> wire_signature_scheme rtr_core \<noteq> 1 \<or>
           encode_wire_packet rtr_packet \<noteq> rtr_packet_bytes \<or> rtr_core_bytes \<noteq> rtr_expected_core \<or>
           envelope_signing_bytes rtr_core \<noteq> rtr_expected_preimage \<or>
           packet_signature rtr_packet \<noteq> rtr_expected_signature
        then None else
        (case (rtr_slot_from_nat rtr_prefix_transfer,rtr_slot_from_nat rtr_prefix_legal,
               rtr_slot_from_nat rtr_primary_transfer,rtr_slot_from_nat rtr_primary_legal) of
          (Some rtr_raw_transfer,Some rtr_raw_legal,Some rtr_live_transfer,Some rtr_live_legal) \<Rightarrow>
            map_option (\<lambda>rtr_result. [take 4 rtr_meta,rtr_core_bytes,
              [wire_deployment rtr_core,wire_source_domain rtr_core,wire_principal rtr_core,wire_key_number rtr_core],
              wire_uuid rtr_core,wire_words (wire_operation_body rtr_core)] @ rtr_result)
              (rtr_read_rows rtr_meta rtr_core rtr_raw_transfer rtr_raw_legal rtr_live_transfer rtr_live_legal)
        | _ \<Rightarrow> None))"
| "rtr_packet_rows _ = None"

definition rtr_integer_abi :: "integer list list \<Rightarrow> integer list list option" where
  "rtr_integer_abi rtr_input =
    (if list_all (list_all (\<lambda>rtr_word. 0 \<le> rtr_word \<and> rtr_word < 18446744073709551616)) rtr_input
     then map_option (map (map integer_of_nat)) (rtr_packet_rows (map (map nat_of_integer) rtr_input))
     else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms rtr_canonical_terminal_receipt_uses_one_record_map
      rtr_current_prefix_relation rtr_raw_source_legal_priority rtr_raw_source_transfer_fallback
      rtr_raw_terminal_wire_shape secondary_wire_status_keeps_the_origin_and_target_separate
      secondary_transfer_terminal_has_priority secondary_legal_fallback_preserves_the_actual_payload
      every_accepted_wire_message_has_exactly_the_received_bytes})
  then () else error "Unexpected oracle in raw terminal and Status link"
\<close>

export_code rtr_integer_abi in SML
  module_name OIP_Raw_Terminal_Read_Link file_prefix "oip_raw_terminal_read_link"

end
