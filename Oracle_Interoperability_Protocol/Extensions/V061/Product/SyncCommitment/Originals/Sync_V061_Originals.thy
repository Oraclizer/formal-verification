theory Sync_V061_Originals
  imports "OIP_Sync_V061_Position_Proofs.Sync_V061_Product_Proofs"
    "OIP_Message_Code.Wire_Code_Response_Nesting"
begin

definition sync_added_status :: "nat \<Rightarrow> bool" where
  "sync_added_status number \<longleftrightarrow> number \<in> {29,39,40,41}"

definition sync_known_response_compatible where
  "sync_known_response_compatible original kind number committed \<longleftrightarrow>
    (if sync_operation original = (Wire_State_Sync,7) then
       (if sync_added_status number then kind = Recorded_Result \<and> committed = (number = 29)
        else if code_known_response_number number then number \<in> reference_result_codes kind committed \<and>
          (kind \<noteq> Recorded_Result \<or> number \<in> {1,2,3})
        else kind = Recorded_Result \<or> \<not> committed)
     else code_response_compatible (wire_message_family original)
       (wire_opcode (wire_operation_body original)) kind number committed)"

lemma sync_added_status_is_legacy_unknown:
  "sync_added_status number \<Longrightarrow> \<not> code_known_response_number number"
  by (auto simp: sync_added_status_def code_known_response_number_def reference_result_codes_def)

lemma sync_raw_legacy_status_classification_remains_available:
  "sync_added_status number \<Longrightarrow>
    code_decode_response_status kind number committed =
      (if kind = Recorded_Result \<or> \<not> committed
       then Some (Code_Unknown_Response kind number) else None)"
  by (simp add: an_unknown_number_is_accepted_only_as_its_declared_category
    sync_added_status_is_legacy_unknown)

lemma sync_added_known_status_requires_its_call_kind_and_commit_presence:
  assumes "sync_operation original = (Wire_State_Sync,7)" "sync_added_status number"
  shows "sync_known_response_compatible original kind number committed \<longleftrightarrow>
    kind = Recorded_Result \<and> committed = (number = 29)"
  using assms by (simp add: sync_known_response_compatible_def)

lemma sync_existing_correlation_keeps_its_compatibility:
  assumes "sync_operation original \<noteq> (Wire_State_Sync,7)"
  shows "sync_known_response_compatible original kind number committed =
    code_response_compatible (wire_message_family original) (wire_opcode (wire_operation_body original))
      kind number committed"
  using assms by (simp add: sync_known_response_compatible_def)

lemma sync_existing_known_correlation_keeps_its_compatibility:
  assumes "reference_response_compatible (wire_message_family original)
    (wire_opcode (wire_operation_body original)) kind number committed"
    "sync_operation original \<noteq> (Wire_State_Sync,7)"
  shows "sync_known_response_compatible original kind number committed"
  using assms the_extended_receiver_preserves_the_complete_old_compatibility_relation[OF assms(1)]
  by (simp add: sync_existing_correlation_keeps_its_compatibility)

lemma sync_scope_is_required_for_legacy_compatibility:
  assumes debit: "sync_operation original = (Wire_State_Sync,1)"
    and sync: "sync_operation synchronization = (Wire_State_Sync,7)"
  shows "sync_known_response_compatible original Delivery_Refusal 39 False"
    "\<not> sync_known_response_compatible synchronization Delivery_Refusal 39 False"
    "sync_known_response_compatible synchronization Recorded_Result 39 False"
  using debit sync by (simp_all add: sync_known_response_compatible_def sync_operation_def sync_added_status_def
    code_response_compatible_def code_response_call_shape_def
    code_known_response_number_def reference_result_codes_def)

record sync_receipt_original =
  sync_receipt_session :: product_session_id
  sync_receipt_exact_core :: wire_bytes
  sync_receipt_inner :: wire_core
  sync_receipt_request :: sync_request

definition sync_parse_query_eight :: "nat \<Rightarrow> wire_core \<Rightarrow> sync_receipt_original option" where
  "sync_parse_query_eight fuel outer =
    (let body = wire_operation_body outer in
     if fuel < 2 \<or> sync_operation outer \<noteq> (Wire_Query,8) \<or>
        wire_deadline body \<noteq> Deadline_Absent then None
     else case (wire_words body,wire_blobs body) of ([session],[raw]) \<Rightarrow>
       Option.bind (sync_decode_core raw) (\<lambda>original.
         map_option (\<lambda>request. \<lparr>sync_receipt_session = session, sync_receipt_exact_core = raw,
           sync_receipt_inner = original, sync_receipt_request = request\<rparr>) (sync_read_operands original))
     | _ \<Rightarrow> None)"

definition sync_query_eight_observe where
  "sync_query_eight_observe receipt_allowed fuel outer state =
    Option.bind (sync_parse_query_eight fuel outer) (\<lambda>receipt.
      if code_same_original outer (sync_receipt_inner receipt) \<and>
         sync_current_identity state outer (sync_receipt_session receipt) \<and>
         receipt_allowed state outer (sync_receipt_session receipt)
      then case sync_outcome_table state (sync_call (sync_receipt_request receipt)) of
        Some (original,outcome) \<Rightarrow> if original = sync_receipt_exact_core receipt then Some outcome else None
      | None \<Rightarrow> None
      else None)"

lemma sync_query_eight_keeps_one_canonical_inner_call:
  assumes "sync_parse_query_eight fuel outer = Some receipt"
  shows "2 \<le> fuel" "sync_operation outer = (Wire_Query,8)"
    "sync_decode_core (sync_receipt_exact_core receipt) = Some (sync_receipt_inner receipt)"
    "sync_read_operands (sync_receipt_inner receipt) = Some (sync_receipt_request receipt)"
  using assms by (auto simp: sync_parse_query_eight_def Let_def bind_eq_Some_conv
    split: list.splits prod.splits option.splits if_splits)

lemma sync_query_eight_releases_only_the_authorized_exact_outcome:
  assumes "sync_query_eight_observe receipt_allowed fuel outer state = Some outcome"
  obtains receipt where "sync_parse_query_eight fuel outer = Some receipt"
    "code_same_original outer (sync_receipt_inner receipt)"
    "sync_current_identity state outer (sync_receipt_session receipt)"
    "receipt_allowed state outer (sync_receipt_session receipt)"
    "sync_outcome_table state (sync_call (sync_receipt_request receipt)) =
      Some (sync_receipt_exact_core receipt,outcome)"
  using assms by (auto simp: sync_query_eight_observe_def bind_eq_Some_conv
    split: option.splits prod.splits if_splits)

record sync_ack_original =
  sync_ack_exact_core :: wire_bytes
  sync_ack_inner :: wire_core
  sync_ack_call :: client_call_id
  sync_ack_kind :: reference_response_kind
  sync_ack_number :: nat
  sync_ack_position :: "nat option"

definition sync_parse_ack_two :: "nat \<Rightarrow> wire_core \<Rightarrow> sync_ack_original option" where
  "sync_parse_ack_two fuel outer =
    (let body = wire_operation_body outer in
     if fuel < 2 \<or> sync_operation outer \<noteq> (Wire_Ack,2) \<or> wire_deadline body \<noteq> Deadline_Absent
     then None
     else case wire_blobs body of [raw] \<Rightarrow>
       Option.bind (sync_decode_core raw) (\<lambda>original.
         Option.bind (sync_read_operands original) (\<lambda>request.
          Option.bind (response_result_words (wire_words body)) (\<lambda>(call_id,kind,number,position).
           if call_id = sync_call request \<and> wire_version outer = wire_version original \<and>
              wire_deployment outer = wire_deployment original \<and>
              wire_source_domain outer = wire_target_domain original \<and>
              wire_target_domain outer = wire_source_domain original \<and>
              (kind = Recorded_Result \<or> position = None)
           then Some \<lparr>sync_ack_exact_core = raw, sync_ack_inner = original, sync_ack_call = call_id,
             sync_ack_kind = kind, sync_ack_number = number, sync_ack_position = position\<rparr>
           else None)))
     | _ \<Rightarrow> None)"

definition sync_correlate_ack_two where
  "sync_correlate_ack_two fuel expected expected_id outer =
    Option.bind (sync_parse_ack_two fuel outer) (\<lambda>ack.
      if sync_ack_exact_core ack = expected \<and> sync_ack_call ack = expected_id \<and>
         sync_known_response_compatible (sync_ack_inner ack) (sync_ack_kind ack) (sync_ack_number ack)
           (sync_ack_position ack \<noteq> None)
      then Some ack else None)"

lemma sync_ack_two_uses_the_exact_original_and_compatible_outcome:
  assumes "sync_correlate_ack_two fuel expected expected_id outer = Some ack"
  shows "sync_ack_exact_core ack = expected" "sync_ack_call ack = expected_id"
    "sync_decode_core expected = Some (sync_ack_inner ack)"
    "sync_known_response_compatible (sync_ack_inner ack) (sync_ack_kind ack) (sync_ack_number ack)
      (sync_ack_position ack \<noteq> None)"
proof -
  have parsed: "sync_parse_ack_two fuel outer = Some ack"
    and exact: "sync_ack_exact_core ack = expected"
    and caller: "sync_ack_call ack = expected_id"
    and compatible: "sync_known_response_compatible (sync_ack_inner ack) (sync_ack_kind ack) (sync_ack_number ack)
      (sync_ack_position ack \<noteq> None)"
    using assms by (auto simp: sync_correlate_ack_two_def bind_eq_Some_conv split: if_splits)
  show "sync_ack_exact_core ack = expected" by (rule exact)
  show "sync_ack_call ack = expected_id" by (rule caller)
  show "sync_known_response_compatible (sync_ack_inner ack) (sync_ack_kind ack) (sync_ack_number ack)
      (sync_ack_position ack \<noteq> None)" by (rule compatible)
  show "sync_decode_core expected = Some (sync_ack_inner ack)"
    using parsed exact by (auto simp: sync_parse_ack_two_def Let_def bind_eq_Some_conv
      split: list.splits prod.splits option.splits if_splits)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_added_status_is_legacy_unknown
    sync_raw_legacy_status_classification_remains_available
    sync_added_known_status_requires_its_call_kind_and_commit_presence
    sync_existing_correlation_keeps_its_compatibility sync_existing_known_correlation_keeps_its_compatibility
    sync_scope_is_required_for_legacy_compatibility
    sync_query_eight_keeps_one_canonical_inner_call sync_query_eight_releases_only_the_authorized_exact_outcome
    sync_ack_two_uses_the_exact_original_and_compatible_outcome})
  then () else error "Unexpected oracle in SyncCommitment original correlation"
\<close>

end
