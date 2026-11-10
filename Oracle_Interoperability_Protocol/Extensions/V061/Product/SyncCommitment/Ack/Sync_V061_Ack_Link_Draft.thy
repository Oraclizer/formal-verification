theory Sync_V061_Ack_Link_Draft
  imports "OIP_Sync_V061_Position_Originals.Sync_V061_Originals"
    "OIP_Message_Response.Wire_Response_Fixed_Receiver"
begin

record sync_link_original =
  sync_link_enclosed :: wire_core
  sync_link_call_core :: wire_core
  sync_link_request :: sync_request

record sync_link_ack =
  sync_link_exact_original :: wire_bytes
  sync_link_original_view :: sync_link_original
  sync_link_id :: client_call_id
  sync_link_kind :: reference_response_kind
  sync_link_code :: nat
  sync_link_commit :: "nat option"

text \<open>This view is for direct SyncCommitment and ExactReceipt around
  SyncCommitment. A retained expected call at the signed boundary is direct.
  The legacy full decoder remains the owner of legacy call shapes.\<close>

definition sync_link_original_at :: "nat \<Rightarrow> wire_core \<Rightarrow> sync_link_original option" where
  "sync_link_original_at fuel enclosed =
    (if fuel < 2 then None
     else case sync_read_operands enclosed of
       Some request \<Rightarrow> Some \<lparr>sync_link_enclosed = enclosed, sync_link_call_core = enclosed,
         sync_link_request = request\<rparr>
     | None \<Rightarrow> map_option (\<lambda>receipt. \<lparr>sync_link_enclosed = enclosed,
          sync_link_call_core = sync_receipt_inner receipt, sync_link_request = sync_receipt_request receipt\<rparr>)
          (sync_parse_query_eight (fuel - 1) enclosed))"

definition sync_link_response_header where
  "sync_link_response_header outer enclosed caller \<longleftrightarrow>
    wire_version outer = wire_version enclosed \<and> wire_deployment outer = wire_deployment enclosed \<and>
    wire_principal enclosed = fst caller \<and> wire_source_domain outer = wire_target_domain enclosed \<and>
    wire_target_domain outer = wire_source_domain enclosed"

definition sync_link_response_status where
  "sync_link_response_status view =
    (let original = sync_link_call_core (sync_link_original_view view);
         kind = sync_link_kind view; code = sync_link_code view; committed = (sync_link_commit view \<noteq> None)
     in if \<not> sync_known_response_compatible original kind code committed
        then None
        else if sync_operation original = (Wire_State_Sync,7) \<and> sync_added_status code
        then Some (Code_Known_Response kind code)
        else code_decode_response_status kind code committed)"

definition sync_link_finish_parse where
  "sync_link_finish_parse raw_status outer raw original caller kind code commit =
    (let enclosed = sync_link_enclosed original; inner = sync_link_call_core original;
         committed = (commit \<noteq> None);
         view = \<lparr>sync_link_exact_original = raw, sync_link_original_view = original, sync_link_id = caller,
           sync_link_kind = kind, sync_link_code = code, sync_link_commit = commit\<rparr>
     in if (kind \<noteq> Recorded_Result \<and> committed) \<or>
           (raw_status \<and> sync_operation inner = (Wire_State_Sync,7) \<and> sync_added_status code \<and>
             (kind \<noteq> Recorded_Result \<or> committed \<noteq> (code = 29)))
        then Inl Invalid_Wire_Format
        else if \<not> sync_link_response_header outer enclosed caller then Inl Invalid_Wire_Source
        else if enclosed \<noteq> inner \<and> \<not> code_same_original enclosed inner then Inl Invalid_Wire_Source
        else if caller \<noteq> sync_call (sync_link_request original) then Inl Invalid_Wire_Format
        else if raw_status \<and> sync_link_response_status view = None then Inl Invalid_Wire_Format
        else Inr view)"

definition sync_link_parse_ack where
  "sync_link_parse_ack raw_status fuel outer =
    (let body = wire_operation_body outer in
     if sync_operation outer \<noteq> (Wire_Ack,2) \<or> wire_deadline body \<noteq> Deadline_Absent
     then Inl Invalid_Wire_Format
     else case wire_blobs body of [raw] \<Rightarrow>
       (case sync_decode_core raw of None \<Rightarrow> Inl Invalid_Wire_Format | Some enclosed \<Rightarrow>
        case sync_link_original_at fuel enclosed of None \<Rightarrow> Inl Invalid_Wire_Format | Some original \<Rightarrow>
          (case response_result_words (wire_words body) of None \<Rightarrow> Inl Invalid_Wire_Format
            | Some (caller,kind,code,commit) \<Rightarrow>
                sync_link_finish_parse raw_status outer raw original caller kind code commit))
     | _ \<Rightarrow> Inl Invalid_Wire_Format)"

definition sync_link_validate_signed where
  "sync_link_validate_signed fuel expected outer =
    (case sync_link_parse_ack False fuel outer of Inl reason \<Rightarrow> Inl reason | Inr view \<Rightarrow>
       case sync_read_operands expected of None \<Rightarrow> Inl Invalid_Wire_Format | Some request \<Rightarrow>
         if sync_link_exact_original view \<noteq> encode_wire_core expected \<or> sync_link_id view \<noteq> sync_call request
         then Inl Conflicting_Wire_Replay
         else case sync_link_response_status view of None \<Rightarrow> Inl Invalid_Wire_Format
          | Some status \<Rightarrow> Inr (view,status))"

definition sync_link_admit_signed where
  "sync_link_admit_signed curve_verify channel current expected bytes =
    (let scope = response_client_scope current in
     if response_channel_local channel \<noteq> boundary_target scope \<or>
        response_channel_remote channel \<noteq> boundary_source scope \<or>
        response_channel_deployment channel \<noteq> boundary_deployment scope \<or>
        boundary_now scope > response_channel_expires channel \<or>
        response_client_public_key current \<noteq> response_channel_remote_key channel
     then Inl Invalid_Wire_Source
     else case code_check_declared_version bytes (boundary_max_frame scope) of Some reason \<Rightarrow> Inl reason
      | None \<Rightarrow> (case sync_decode_packet bytes of None \<Rightarrow> Inl Invalid_Wire_Format | Some packet \<Rightarrow>
          case code_admit_packet
            (\<lambda>core preimage signature. curve_verify (response_client_public_key current) preimage signature)
            packet (scope\<lparr>boundary_profile := response_channel_profile channel\<rparr>) of Some reason \<Rightarrow> Inl reason
          | None \<Rightarrow> sync_link_validate_signed (response_client_max_nesting current) expected (packet_core packet)))"

lemma sync_link_original_at_uses_the_effective_sync_operation:
  assumes "sync_link_original_at fuel enclosed = Some original"
  shows "sync_operation (sync_link_call_core original) = (Wire_State_Sync,7)"
proof -
  have read_sync: "\<And>core request. sync_read_operands core = Some request \<Longrightarrow>
      sync_operation core = (Wire_State_Sync,7)"
    by (auto simp: sync_read_operands_def sync_operation_def Let_def split: if_splits)
  show ?thesis using assms
  proof (cases "sync_read_operands enclosed")
    case None
    with assms obtain receipt where "sync_parse_query_eight (fuel - 1) enclosed = Some receipt"
      "sync_link_call_core original = sync_receipt_inner receipt"
      by (auto simp: sync_link_original_at_def split: if_splits option.splits)
    then show ?thesis
      using sync_query_eight_keeps_one_canonical_inner_call(4) read_sync by metis
  next
    case (Some request)
    with assms show ?thesis
      by (auto simp: sync_link_original_at_def split: if_splits dest: read_sync)
  qed
qed

lemma sync_link_uses_the_fixed_status_for_the_decoded_sync_call:
  assumes "sync_link_original_at fuel enclosed = Some (sync_link_original_view view)"
    "sync_added_status (sync_link_code view)"
  shows "sync_link_response_status view =
    (if sync_link_kind view = Recorded_Result \<and>
       (sync_link_commit view \<noteq> None) = (sync_link_code view = 29)
     then Some (Code_Known_Response Recorded_Result (sync_link_code view)) else None)"
  using assms(2) sync_link_original_at_uses_the_effective_sync_operation[OF assms(1)]
  by (simp add: sync_link_response_status_def sync_known_response_compatible_def Let_def)

lemma sync_link_raw_status_uses_the_effective_call:
  assumes "sync_link_finish_parse True outer raw original caller kind code commit = Inr view"
  shows "sync_link_response_status view \<noteq> None"
    "sync_link_response_header outer (sync_link_enclosed original) caller"
    "sync_link_enclosed original \<noteq> sync_link_call_core original \<Longrightarrow>
      code_same_original (sync_link_enclosed original) (sync_link_call_core original)"
    "caller = sync_call (sync_link_request original)"
  using assms by (auto simp: sync_link_finish_parse_def Let_def split: if_splits)

lemma sync_link_signed_conflict_precedes_status:
  assumes "sync_link_parse_ack False fuel outer = Inr view"
    "sync_read_operands expected = Some request"
    "sync_link_exact_original view \<noteq> encode_wire_core expected \<or> sync_link_id view \<noteq> sync_call request"
  shows "sync_link_validate_signed fuel expected outer = Inl Conflicting_Wire_Replay"
  using assms by (simp add: sync_link_validate_signed_def)

lemma sync_link_signed_expected_decode_precedes_exact_bytes:
  assumes "sync_link_parse_ack False fuel outer = Inr view" "sync_read_operands expected = None"
  shows "sync_link_validate_signed fuel expected outer = Inl Invalid_Wire_Format"
  using assms by (simp add: sync_link_validate_signed_def)

lemma sync_link_signed_matching_original_reaches_status:
  assumes "sync_link_parse_ack False fuel outer = Inr view"
    "sync_read_operands expected = Some request"
    "sync_link_exact_original view = encode_wire_core expected" "sync_link_id view = sync_call request"
  shows "sync_link_validate_signed fuel expected outer =
    (case sync_link_response_status view of None \<Rightarrow> Inl Invalid_Wire_Format | Some status \<Rightarrow> Inr (view,status))"
  using assms by (simp add: sync_link_validate_signed_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_link_original_at_uses_the_effective_sync_operation
    sync_link_uses_the_fixed_status_for_the_decoded_sync_call sync_link_raw_status_uses_the_effective_call
    sync_link_signed_conflict_precedes_status sync_link_signed_expected_decode_precedes_exact_bytes
    sync_link_signed_matching_original_reaches_status})
  then () else error "Unexpected oracle in the Sync ACK comparison"
\<close>

end
