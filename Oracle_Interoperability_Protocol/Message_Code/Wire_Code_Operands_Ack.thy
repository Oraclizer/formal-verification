theory Wire_Code_Operands_Ack
  imports Wire_Code_Operands_Regulated "OIP_Reference_Profile.Reference_Scheduled_ACK_Wire"
begin

definition code_decode_settlement_ack where
  "code_decode_settlement_ack core =
    (let body = wire_operation_body core in
     if wire_message_family core \<noteq> Wire_Ack \<or> wire_opcode body \<noteq> 1 \<or>
        wire_deadline body \<noteq> Deadline_Absent then None
     else case (wire_words body,wire_blobs body) of
       ([domain,event,position,target,asset,owner,destination,recipient,epoch,kind],[raw]) \<Rightarrow>
         if kind \<notin> {1,2} then None
         else map_option (\<lambda>amount.
           \<lparr>scheduled_ack_key = ((domain,event),position),scheduled_ack_target = target,
            scheduled_ack_asset = asset,scheduled_ack_owner = owner,scheduled_ack_destination = destination,
            scheduled_ack_recipient = recipient,scheduled_ack_amount = amount,scheduled_ack_epoch = epoch,
            scheduled_ack_kind = (if kind = 1 then Confirmed_Decision else Reversed_Decision)\<rparr>)
           (code_product_amount raw)
     | _ \<Rightarrow> None)"

theorem the_source_settlement_ack_parser_has_the_existing_exact_product_value:
  "code_decode_settlement_ack core = parse_native_scheduled_ack core"
  by (auto simp: code_decode_settlement_ack_def parse_native_scheduled_ack_def
    the_source_amount_check_is_exactly_the_model_value_and_u64_limit Let_def
    split: list.splits prod.splits if_splits)

theorem two_source_acknowledgements_for_one_slot_require_the_existing_product_serialization:
  assumes first: "code_decode_settlement_ack first_core = Some first_native"
    and second: "code_decode_settlement_ack second_core = Some second_native"
    and first_match: "scheduled_ack_matches_publication first_owner first_native first"
    and second_match: "scheduled_ack_matches_publication second_owner second_native second"
    and same: "scheduled_ack_key first_native = scheduled_ack_key second_native"
  shows "\<not> compatible_service_actions (Service_Maintenance (Exact_Acknowledge first))
    (Service_Maintenance (Exact_Acknowledge second)) world"
proof -
  have first_selected: "select_native_scheduled_ack first_owner first first_core = Some first_native"
    using first first_match
    by (simp add: the_source_settlement_ack_parser_has_the_existing_exact_product_value select_native_scheduled_ack_def)
  have second_selected: "select_native_scheduled_ack second_owner second second_core = Some second_native"
    using second second_match
    by (simp add: the_source_settlement_ack_parser_has_the_existing_exact_product_value select_native_scheduled_ack_def)
  show ?thesis
    by (rule two_decoded_acknowledgements_for_one_native_slot_require_product_serialization[OF first_selected second_selected same])
qed

end
