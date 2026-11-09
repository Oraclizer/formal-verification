theory Sync_V061_Observation_Export
  imports "OIP_Sync_V061_Position_Definitions.Sync_V061_Product"
    "OIP_Message_Code.Wire_Code_Oracle_Codegen" "HOL-Library.Code_Target_Nat"
begin

declare [[code drop: sync_parse_votes]]

lemma sync_parse_votes_integer_code [code]:
  "sync_parse_votes count raw =
    (if count = 0 then []
     else (sync_take_word raw, take 64 (drop 8 raw)) # sync_parse_votes (count - 1) (drop 72 raw))"
  by (cases count) simp_all

fun sync_mode_number :: "sync_mode \<Rightarrow> nat" where
  "sync_mode_number Sync_Initial = 1"
| "sync_mode_number Sync_Incremental = 2"
| "sync_mode_number Sync_Full = 3"

definition sync_operand_observation :: "wire_core \<Rightarrow> (nat list \<times> wire_bytes list) option" where
  "sync_operand_observation core =
    (case sync_read_operands core of Some request \<Rightarrow>
       let entry = sync_requested request in
       Some ([1, sync_message request, snd (sync_call request), sync_session request,
              cut_revision (sync_signed_cut request), sync_origin_epoch entry, snd (sync_key request),
              sync_event entry, fst (sync_key request), sync_position entry, sync_mode_number (sync_mode request)],
             [sync_commitment entry, (case sync_claimed_prior request of None \<Rightarrow> [] | Some prior \<Rightarrow> prior),
              sync_attestation request])
     | None \<Rightarrow> map_option (\<lambda>query.
         ([2, sync_query_session query, cut_revision (sync_query_cut query),
           fst (sync_query_key query), snd (sync_query_key query)], []))
         (sync_read_query core))"

definition sync_packet_observation :: "wire_bytes \<Rightarrow> (nat list \<times> wire_bytes list \<times> (nat list \<times> wire_bytes list) option) option" where
  "sync_packet_observation raw =
    map_option (\<lambda>packet.
      let core = packet_core packet in
      ([wire_version core, wire_deployment core, wire_source_domain core, wire_target_domain core,
        wire_principal core, wire_authority_epoch core, family_number (wire_message_family core),
        wire_opcode (wire_operation_body core)],
       [encode_wire_core core, envelope_signing_bytes core, wire_uuid core],
       sync_operand_observation core)) (sync_decode_packet raw)"

definition sync_proof_observation :: "wire_bytes \<Rightarrow> (nat list \<times> wire_bytes list) option" where
  "sync_proof_observation raw =
    map_option (\<lambda>(a,votes).
      let entry = sync_item a in
      ([sync_format a, sync_claim a, sync_deployment a, sync_origin a, sync_origin_epoch entry,
        sync_roster a, sync_asset a, sync_event entry, sync_position entry,
        (if sync_predecessor a = None then 0 else 1), length votes] @ map fst votes,
       [sync_statement_bytes a, sync_commitment entry,
        (case sync_predecessor a of None \<Rightarrow> [] | Some prior \<Rightarrow> prior)] @ map snd votes))
      (sync_decode_proof raw)"

definition sync_packet_integer_observation ::
  "integer list \<Rightarrow> (integer list \<times> integer list list \<times> (integer list \<times> integer list list) option) option" where
  "sync_packet_integer_observation raw =
    (if list_all (\<lambda>octet. 0 \<le> octet \<and> octet < 256) raw then
       map_option (\<lambda>(header,blobs,operand).
         (map integer_of_nat header, map (map integer_of_nat) blobs,
          map_option (\<lambda>(words,data). (map integer_of_nat words,map (map integer_of_nat) data)) operand))
         (sync_packet_observation (map nat_of_integer raw))
     else None)"

definition sync_proof_integer_observation :: "integer list \<Rightarrow> (integer list \<times> integer list list) option" where
  "sync_proof_integer_observation raw =
    (if list_all (\<lambda>octet. 0 \<le> octet \<and> octet < 256) raw then
       map_option (\<lambda>(words,blobs). (map integer_of_nat words,map (map integer_of_nat) blobs))
         (sync_proof_observation (map nat_of_integer raw))
     else None)"

lemma sync_observation_is_a_projection_of_the_decoded_packet:
  assumes "sync_packet_observation raw = Some (header,blobs,operand)"
  obtains packet where "sync_decode_packet raw = Some packet" "encode_wire_packet packet = raw"
    "blobs = [encode_wire_core (packet_core packet), envelope_signing_bytes (packet_core packet),
      wire_uuid (packet_core packet)]"
    "operand = sync_operand_observation (packet_core packet)"
proof -
  obtain packet where decoded: "sync_decode_packet raw = Some packet"
    and exact: "blobs = [encode_wire_core (packet_core packet), envelope_signing_bytes (packet_core packet),
      wire_uuid (packet_core packet)]"
    and typed: "operand = sync_operand_observation (packet_core packet)"
    using assms by (cases "sync_decode_packet raw") (auto simp: sync_packet_observation_def Let_def)
  show thesis by (rule that[OF decoded sync_decoded_packet_has_the_exact_bytes[OF decoded] exact typed])
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_parse_votes_integer_code sync_observation_is_a_projection_of_the_decoded_packet})
  then () else error "Unexpected oracle in SyncCommitment observation export"
\<close>

export_code sync_packet_integer_observation sync_proof_integer_observation
  in SML module_name OIP_Sync_Commitment_Oracle file_prefix "oip_sync_commitment"

end
