theory Sync_V061_Structure_Seeds
  imports "OIP_Sync_V061_Extraction_V1.Sync_V061_Observation_Export"
begin

definition sync_seed_statement where
  "sync_seed_statement =
    \<lparr>sync_format = 1, sync_claim = 1, sync_deployment = 10, sync_origin = 30, sync_roster = 17, sync_asset = 20,
      sync_item = \<lparr>sync_commitment = replicate 32 165, sync_position = 41, sync_origin_epoch = 6, sync_event = 91\<rparr>,
      sync_predecessor = Some (replicate 32 0)\<rparr>"

definition sync_seed_votes :: sync_votes where
  "sync_seed_votes = [(101, replicate 64 161), (102, replicate 64 162)]"

definition sync_seed_proof where
  "sync_seed_proof = sync_proof_bytes sync_seed_statement sync_seed_votes"

definition sync_seed_sync_core where
  "sync_seed_sync_core =
    \<lparr>wire_version = 6, wire_purpose = 1, wire_deployment = 10, wire_source_domain = 31,
      wire_target_domain = 70, wire_principal = 50, wire_key_number = 51, wire_authority_epoch = 2,
      wire_sent_seconds = 72, wire_ttl_seconds = 120, wire_uuid = [0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15],
      wire_message_family = Wire_State_Sync, wire_primary_code = 1, wire_secondary_code = None,
      wire_signature_scheme = 1, wire_operation_body = \<lparr>wire_opcode = 7,
        wire_words = [52,53,60,0,6,30,91,20,41,2],
        wire_blobs = [sync_commitment (sync_item sync_seed_statement),replicate 32 0,sync_seed_proof],
        wire_deadline = Deadline_Absent\<rparr>, wire_atomicity = 1, wire_priority = 3, wire_route_scope = 55\<rparr>"

definition sync_seed_query_core where
  "sync_seed_query_core =
    sync_seed_sync_core\<lparr>wire_uuid := [0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,16],
      wire_message_family := Wire_Query, wire_operation_body :=
        \<lparr>wire_opcode = 9, wire_words = [60,0,20,30], wire_blobs = [], wire_deadline = Deadline_Absent\<rparr>\<rparr>"

definition sync_seed_sync_packet where
  "sync_seed_sync_packet = \<lparr>packet_core = sync_seed_sync_core, packet_signature = replicate 64 177\<rparr>"

definition sync_seed_query_packet where
  "sync_seed_query_packet = \<lparr>packet_core = sync_seed_query_core, packet_signature = replicate 64 178\<rparr>"

definition sync_seed_integer_vectors :: "integer list list" where
  "sync_seed_integer_vectors =
    map (map integer_of_nat)
      [encode_wire_core sync_seed_sync_core, encode_wire_packet sync_seed_sync_packet,
       encode_wire_core sync_seed_query_core, encode_wire_packet sync_seed_query_packet,
       sync_seed_proof, sync_statement_bytes sync_seed_statement]"

lemma sync_seed_proof_has_exact_binary_structure:
  "sync_decode_proof sync_seed_proof = Some (sync_seed_statement,sync_seed_votes)"
  "length (sync_statement_bytes sync_seed_statement) = 160"
  "length sync_seed_proof = 312"
  by (simp_all add: sync_seed_proof_def sync_seed_statement_def sync_seed_votes_def
    sync_decode_proof_def code_reencoding_decode_def sync_parse_proof_def sync_proof_bytes_def
    sync_statement_bytes_def wire_octets_def small_number_eight_octets numeral_2_eq_2 Let_def)

lemma sync_seed_sync_and_query_have_the_exact_operand_observations:
  "sync_operand_observation sync_seed_sync_core =
    Some ([1,52,53,60,0,6,30,91,20,41,2],[replicate 32 165,replicate 32 0,sync_seed_proof])"
  "sync_operand_observation sync_seed_query_core = Some ([2,60,0,20,30],[])"
  by (simp_all add: sync_operand_observation_def sync_seed_sync_core_def sync_seed_query_core_def
    sync_seed_statement_def sync_read_operands_def sync_mode_at_def sync_read_query_def sync_operation_def Let_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_seed_proof_has_exact_binary_structure
    sync_seed_sync_and_query_have_the_exact_operand_observations})
  then () else error "Unexpected oracle in SyncCommitment structure seeds"
\<close>

export_code sync_seed_integer_vectors sync_packet_integer_observation sync_proof_integer_observation
  in SML module_name OIP_Sync_Commitment_Seeds file_prefix "oip_sync_structure_seeds"

end
