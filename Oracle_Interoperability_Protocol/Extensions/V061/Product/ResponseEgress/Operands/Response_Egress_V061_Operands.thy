theory Response_Egress_V061_Operands
  imports "OIP_Message_Egress.Wire_Code_Response_Executable_Names"
    "OIP_Sync_V061_Position_Nested_IR.Sync_V061_Nested_IR"
    "OIP_Response_Code_Extension.Response_Code_Extension"
begin

datatype response_v061_nested =
    Response_V061_Legacy_Operand code_nested_operand
  | Response_V061_Sync_Operand sync_request
  | Response_V061_Receipt wire_core
  | Response_V061_Current

definition response_v061_is_call where
  "response_v061_is_call operand = (case operand of
     Response_V061_Sync_Operand request \<Rightarrow> True
   | Response_V061_Legacy_Operand decoded \<Rightarrow>
       (case response_fixed_caller_from_decoded decoded of Inl reason \<Rightarrow> False | Inr v061_caller \<Rightarrow> True)
   | _ \<Rightarrow> False)"

fun response_v061_caller where
  "response_v061_caller (Response_V061_Sync_Operand request) = Inr (sync_call request)"
| "response_v061_caller (Response_V061_Legacy_Operand decoded) = response_fixed_caller_from_decoded decoded"
| "response_v061_caller (Response_V061_Receipt original) = Inl Invalid_Wire_Format"
| "response_v061_caller Response_V061_Current = Inl Invalid_Wire_Format"

fun response_v061_is_sync_call :: "response_v061_nested \<Rightarrow> bool" where
  "response_v061_is_sync_call (Response_V061_Sync_Operand request) = True"
| "response_v061_is_sync_call (Response_V061_Receipt original) = (sync_operation original = (Wire_State_Sync,7))"
| "response_v061_is_sync_call _ = False"

definition response_v061_status where
  "response_v061_status original kind number position =
    (let committed = (position \<noteq> None);
         family = wire_message_family original;
         operation = wire_opcode (wire_operation_body original)
     in if sync_operation original = (Wire_State_Sync,7) then
       (case response_extended_status sync_response_allocations kind number committed of
          None \<Rightarrow> None
        | Some (Code_Unknown_Response category raw) \<Rightarrow> Some (Code_Unknown_Response category raw)
        | Some (Code_Known_Response category known) \<Rightarrow>
            if response_extended_compatible sync_response_allocations [sync_response_operation]
                family operation kind number committed
            then Some (Code_Known_Response category known) else None)
     else if code_known_response_number number \<and>
         \<not> reference_response_compatible family operation kind number committed
     then None else code_decode_response_status kind number committed)"

definition response_v061_check_enclosed where
  "response_v061_check_enclosed check_status original decoded v061_caller kind number position =
    (case decoded of
       Response_V061_Sync_Operand request \<Rightarrow>
         if v061_caller \<noteq> sync_call request \<or> (check_status \<and> response_v061_status original kind number position = None)
         then Some Invalid_Wire_Format else None
     | Response_V061_Legacy_Operand legacy \<Rightarrow> code_check_nested_response original legacy v061_caller position
     | _ \<Rightarrow> Some Invalid_Wire_Format)"

definition response_v061_finish_parse where
  "response_v061_finish_parse check_status descend outer exact nested decoded =
    (case response_result_words (wire_words (wire_operation_body outer)) of None \<Rightarrow> Inl Invalid_Wire_Format
     | Some (v061_caller,kind,number,position) \<Rightarrow>
       if (kind \<noteq> Recorded_Result \<and> position \<noteq> None) \<or>
          (check_status \<and> response_v061_is_sync_call decoded \<and> sync_added_status number \<and>
            (kind \<noteq> Recorded_Result \<or> (position \<noteq> None) \<noteq> (number = 29)))
       then Inl Invalid_Wire_Format
       else if \<not> sync_link_response_header outer nested v061_caller then Inl Invalid_Wire_Source
       else let v061_check = (\<lambda>original operand. response_v061_check_enclosed check_status original operand v061_caller kind number position);
                refusal = (case decoded of Response_V061_Receipt original \<Rightarrow>
                   if \<not> code_same_original nested original then Some Invalid_Wire_Source
                   else (case descend original of Inl reason \<Rightarrow> Some reason | Inr inner \<Rightarrow> v061_check original inner)
                 | _ \<Rightarrow> v061_check nested decoded)
            in case refusal of Some reason \<Rightarrow> Inl reason
             | None \<Rightarrow> Inr \<lparr>response_decoded_id = v061_caller,response_decoded_kind = kind,
                 response_decoded_number = number,response_decoded_position = position,
                 response_decoded_original_bytes = exact,response_decoded_original = nested\<rparr>)"

definition response_v061_parse_layer where
  "response_v061_parse_layer check_status descend outer =
    (let v061_body = wire_operation_body outer in
     if sync_operation outer \<noteq> (Wire_Ack,2) \<or> wire_deadline v061_body \<noteq> Deadline_Absent
     then Inl Invalid_Wire_Format
     else case wire_blobs v061_body of [exact] \<Rightarrow>
       (case sync_decode_core exact of None \<Rightarrow> Inl Invalid_Wire_Format | Some nested \<Rightarrow>
         case descend nested of Inl reason \<Rightarrow> Inl reason | Inr decoded \<Rightarrow>
           response_v061_finish_parse check_status descend outer exact nested decoded)
     | _ \<Rightarrow> Inl Invalid_Wire_Format)"

primrec response_v061_operand :: "nat \<Rightarrow> wire_core \<Rightarrow> wire_refusal + response_v061_nested" where
  "response_v061_operand 0 core = Inl Invalid_Wire_Format"
| "response_v061_operand (Suc fuel) core =
    (let v061_body = wire_operation_body core; operation = sync_operation core in
     if operation = (Wire_State_Sync,7) then
       (case sync_read_operands core of None \<Rightarrow> Inl Invalid_Wire_Format | Some request \<Rightarrow> Inr (Response_V061_Sync_Operand request))
     else if operation = (Wire_Query,9) then
       (case sync_read_query core of None \<Rightarrow> Inl Invalid_Wire_Format | Some request \<Rightarrow> Inr Response_V061_Current)
     else if operation = (Wire_Query,8) then
       (if wire_deadline v061_body \<noteq> Deadline_Absent \<or> fuel = 0 then Inl Invalid_Wire_Format
        else case (wire_words v061_body,wire_blobs v061_body) of ([v061_session],[exact]) \<Rightarrow>
          (case sync_decode_core exact of None \<Rightarrow> Inl Invalid_Wire_Format | Some nested \<Rightarrow>
            case response_v061_operand fuel nested of Inl reason \<Rightarrow> Inl reason | Inr decoded \<Rightarrow>
              if response_v061_is_call decoded then Inr (Response_V061_Receipt nested) else Inl Invalid_Wire_Format)
        | _ \<Rightarrow> Inl Invalid_Wire_Format)
     else if operation = (Wire_Ack,2) then
       (case response_v061_parse_layer True (response_v061_operand fuel) core of Inl reason \<Rightarrow> Inl reason
        | Inr view \<Rightarrow> Inr (Response_V061_Legacy_Operand Code_Nested_Response))
     else map_sum id Response_V061_Legacy_Operand (response_fixed_expected_decode core))"

definition response_v061_parse where
  "response_v061_parse check_status v061_depth core =
    (case v061_depth of 0 \<Rightarrow> Inl Invalid_Wire_Format
     | Suc fuel \<Rightarrow> response_v061_parse_layer check_status (response_v061_operand fuel) core)"

definition response_v061_original_caller where
  "response_v061_original_caller core =
    (case response_v061_operand 1 core of Inl reason \<Rightarrow> Inl reason | Inr decoded \<Rightarrow> response_v061_caller decoded)"

definition response_v061_result_of_view where
  "response_v061_result_of_view view =
    (response_decoded_id view,response_decoded_kind view,response_decoded_number view,response_decoded_position view)"

definition response_v061_validate where
  "response_v061_validate v061_depth expected packet =
    (case response_v061_parse False v061_depth (packet_core packet) of Inl reason \<Rightarrow> Inl reason
     | Inr view \<Rightarrow> (case response_v061_operand 1 expected of Inl reason \<Rightarrow> Inl reason | Inr decoded \<Rightarrow>
         if response_decoded_original_bytes view \<noteq> encode_wire_core expected then Inl Conflicting_Wire_Replay
         else (case response_v061_caller decoded of Inl reason \<Rightarrow> Inl reason | Inr original_id \<Rightarrow>
           if response_decoded_id view \<noteq> original_id then Inl Conflicting_Wire_Replay
           else case response_v061_status expected (response_decoded_kind view)
               (response_decoded_number view) (response_decoded_position view) of
             None \<Rightarrow> Inl Invalid_Wire_Format
           | Some status \<Rightarrow> Inr (response_v061_result_of_view view,Some status))))"

lemma response_v061_status_uses_the_checked_sync_allocation:
  assumes "sync_operation original = (Wire_State_Sync,7)" "sync_added_status number"
  shows "response_v061_status original kind number position =
    (if kind = Recorded_Result \<and> (position \<noteq> None) = (number = 29)
     then Some (Code_Known_Response Recorded_Result number) else None)"
  using assms by (simp add: response_v061_status_def Let_def sync_added_status_def sync_operation_def
    response_extended_status_def response_extended_compatible_def sync_response_lookup_is_exact
    sync_response_operation_def)

lemma response_v061_legacy_status_preserves_the_old_known_and_unknown_value:
  assumes "sync_operation original \<noteq> (Wire_State_Sync,7)"
  shows "response_v061_status original kind number position =
    (if code_known_response_number number \<and>
        \<not> reference_response_compatible (wire_message_family original) (wire_opcode (wire_operation_body original))
          kind number (position \<noteq> None)
     then None else code_decode_response_status kind number (position \<noteq> None))"
  using assms by (simp add: response_v061_status_def Let_def)

lemma response_v061_the_new_numbers_are_unknown_for_legacy_calls:
  assumes "sync_operation original \<noteq> (Wire_State_Sync,7)" "sync_added_status number"
  shows "response_v061_status original kind number position =
    (if kind = Recorded_Result \<or> position = None
     then Some (Code_Unknown_Response kind number) else None)"
proof -
  have unknown: "\<not> code_known_response_number number"
    by (rule sync_added_status_is_legacy_unknown[OF assms(2)])
  have legacy: "response_v061_status original kind number position =
      code_decode_response_status kind number (position \<noteq> None)"
    using unknown
    by (simp add: response_v061_legacy_status_preserves_the_old_known_and_unknown_value[OF assms(1)])
  have decoded: "code_decode_response_status kind number (position \<noteq> None) =
      (if kind = Recorded_Result \<or> position = None
       then Some (Code_Unknown_Response kind number) else None)"
    by (simp add: sync_raw_legacy_status_classification_remains_available[OF assms(2)])
  show ?thesis by (rule trans[OF legacy decoded])
qed

lemma response_v061_legacy_leaf_uses_the_old_operand_tree:
  assumes "sync_operation core \<notin> {(Wire_State_Sync,7),(Wire_Query,9),(Wire_Query,8),(Wire_Ack,2)}"
  shows "response_v061_operand fuel core =
    (case code_decode_operand_tree fuel core of Code_Tree_Refused reason \<Rightarrow> Inl reason
     | Code_Tree_Pending \<Rightarrow> Inl Invalid_Wire_Format
     | Code_Tree_Ready decoded \<Rightarrow> Inr (Response_V061_Legacy_Operand decoded))"
proof (cases fuel)
  case 0
  then show ?thesis by simp
next
  case (Suc depth)
  have stable: "code_decode_operand_tree (Suc depth) core = code_decode_operand_tree 1 core"
    using assms by (cases "wire_message_family core") (simp_all add: Let_def One_nat_def sync_operation_def)
  have legacy: "response_v061_operand (Suc depth) core =
      map_sum id Response_V061_Legacy_Operand (response_fixed_expected_decode core)"
    using assms by (simp add: Let_def)
  show ?thesis
    unfolding Suc legacy stable response_fixed_expected_decode_def
    by (cases "code_decode_operand_tree 1 core") simp_all
qed

lemma response_v061_parse_preserves_direct_legacy_original:
  assumes outer: "sync_operation core = (Wire_Ack,2)"
    and blob: "wire_blobs (wire_operation_body core) = [raw]"
    and original: "decode_wire_core raw = Some nested"
    and leaf: "sync_operation nested \<notin> {(Wire_State_Sync,7),(Wire_Query,9),(Wire_Query,8),(Wire_Ack,2)}"
  shows "response_v061_parse check_status (Suc fuel) core = response_fixed_parse_response fuel core"
proof -
  have decoded: "sync_decode_core raw = Some nested"
    by (rule sync_preserves_every_decoded_legacy_core[OF original])
  show ?thesis
    using outer by (cases "code_decode_operand_tree fuel nested")
      (auto simp: response_v061_parse_def response_v061_parse_layer_def response_fixed_parse_response_def
        response_v061_finish_parse_def response_v061_check_enclosed_def sync_link_response_header_def
        response_v061_legacy_leaf_uses_the_old_operand_tree[OF leaf] decoded original blob sync_operation_def
        Let_def split: option.splits prod.splits if_splits)
qed

lemma response_v061_sync_caller_comes_from_the_original:
  assumes "sync_operation core = (Wire_State_Sync,7)"
  shows "response_v061_original_caller core =
    (case sync_read_operands core of None \<Rightarrow> Inl Invalid_Wire_Format | Some request \<Rightarrow> Inr (sync_call request))"
  using assms by (simp add: response_v061_original_caller_def Let_def One_nat_def split: option.splits)

lemma response_v061_leaf_keeps_its_decoded_legacy_caller:
  assumes "sync_operation core \<notin> {(Wire_State_Sync,7),(Wire_Query,9),(Wire_Query,8),(Wire_Ack,2)}"
  shows "response_v061_original_caller core = code_response_caller core"
proof -
  have leaf: "response_v061_operand 1 core = map_sum id Response_V061_Legacy_Operand (response_fixed_expected_decode core)"
    using assms by (simp add: Let_def One_nat_def)
  show ?thesis unfolding response_v061_original_caller_def leaf
    using response_fixed_expected_then_caller_is_the_existing_source_projection[of core]
    by (cases "response_fixed_expected_decode core") auto
qed

lemma response_v061_exact_bytes_precede_status:
  assumes "response_v061_parse False v061_depth (packet_core packet) = Inr view"
    "response_v061_operand 1 expected = Inr decoded"
    "response_decoded_original_bytes view \<noteq> encode_wire_core expected"
  shows "response_v061_validate v061_depth expected packet = Inl Conflicting_Wire_Replay"
  using assms by (simp add: response_v061_validate_def)

lemma response_v061_validated_result_keeps_exact_bytes_and_status:
  assumes "response_v061_validate v061_depth expected packet = Inr (result,status)"
  obtains view decoded where
    "response_v061_parse False v061_depth (packet_core packet) = Inr view"
    "response_v061_operand 1 expected = Inr decoded"
    "response_decoded_original_bytes view = encode_wire_core expected"
    "response_v061_caller decoded = Inr (response_decoded_id view)"
    "result = response_v061_result_of_view view"
    "response_v061_status expected (response_decoded_kind view) (response_decoded_number view)
      (response_decoded_position view) = status"
  using assms by (auto simp: response_v061_validate_def split: sum.splits option.splits if_splits)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms response_v061_status_uses_the_checked_sync_allocation
      response_v061_legacy_status_preserves_the_old_known_and_unknown_value
      response_v061_the_new_numbers_are_unknown_for_legacy_calls
      response_v061_legacy_leaf_uses_the_old_operand_tree response_v061_parse_preserves_direct_legacy_original
      response_v061_sync_caller_comes_from_the_original response_v061_leaf_keeps_its_decoded_legacy_caller
      response_v061_exact_bytes_precede_status response_v061_validated_result_keeps_exact_bytes_and_status})
  then () else error "Unexpected oracle in the v0.6.1 response operand boundary"
\<close>

end
