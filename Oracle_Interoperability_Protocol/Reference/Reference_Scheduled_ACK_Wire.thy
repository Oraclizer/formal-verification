theory Reference_Scheduled_ACK_Wire
  imports Reference_Wire_Schedule_Classifier "OIP_Product.Wire_Product_Execution"
begin

record native_scheduled_ack =
  scheduled_ack_key :: settlement_identity
  scheduled_ack_target :: nat
  scheduled_ack_asset :: nat
  scheduled_ack_owner :: nat
  scheduled_ack_destination :: nat
  scheduled_ack_recipient :: nat
  scheduled_ack_amount :: nat
  scheduled_ack_epoch :: nat
  scheduled_ack_kind :: terminal_kind

definition parse_native_scheduled_ack where
  "parse_native_scheduled_ack core =
    (let body = wire_operation_body core in
     if wire_message_family core \<noteq> Wire_Ack \<or> wire_opcode body \<noteq> 1 \<or>
        wire_deadline body \<noteq> Deadline_Absent then None
     else case (wire_words body, wire_blobs body) of
       ([domain,event,position,target,asset,owner,destination,recipient,epoch,kind], [raw]) \<Rightarrow>
         let amount = get_le_octets (rev raw) in
           if length raw \<noteq> 32 \<or> \<not> wire_octets raw \<or> amount \<ge> 2^64 \<or> kind \<notin> {1,2} then None
           else Some \<lparr>scheduled_ack_key = ((domain,event),position), scheduled_ack_target = target,
              scheduled_ack_asset = asset, scheduled_ack_owner = owner, scheduled_ack_destination = destination,
              scheduled_ack_recipient = recipient, scheduled_ack_amount = amount, scheduled_ack_epoch = epoch,
              scheduled_ack_kind = (if kind = 1 then Confirmed_Decision else Reversed_Decision)\<rparr>
       | _ \<Rightarrow> None)"

definition scheduled_ack_matches_publication where
  "scheduled_ack_matches_publication owner native ack \<longleftrightarrow>
    (let publication = ack_publication ack; decision = publication_decision publication;
         binding = origin_binding decision in
     scheduled_ack_key native = ack_settlement_key ack \<and> scheduled_ack_key native = settlement_key publication \<and>
     scheduled_ack_target native = ack_target ack \<and> scheduled_ack_asset native = binding_asset binding \<and>
     scheduled_ack_owner native = owner \<and> scheduled_ack_destination native = binding_destination binding \<and>
     scheduled_ack_recipient native = binding_recipient binding \<and> scheduled_ack_amount native = binding_amount binding \<and>
     scheduled_ack_epoch native = origin_epoch decision \<and> scheduled_ack_kind native = origin_kind decision)"

definition select_native_scheduled_ack where
  "select_native_scheduled_ack owner expected core =
     (case parse_native_scheduled_ack core of None \<Rightarrow> None | Some native \<Rightarrow>
       if scheduled_ack_matches_publication owner native expected then Some native else None)"

theorem two_decoded_acknowledgements_for_one_native_slot_require_product_serialization:
  assumes first: "select_native_scheduled_ack first_owner first first_core = Some first_native"
    and second: "select_native_scheduled_ack second_owner second second_core = Some second_native"
    and same: "scheduled_ack_key first_native = scheduled_ack_key second_native"
  shows "\<not> compatible_service_actions (Service_Maintenance (Exact_Acknowledge first))
      (Service_Maintenance (Exact_Acknowledge second)) world"
proof -
  have keys: "ack_settlement_key first = ack_settlement_key second"
    using first second same by (auto simp: select_native_scheduled_ack_def scheduled_ack_matches_publication_def Let_def
      split: option.splits if_splits)
  show ?thesis using keys
    by (simp add: compatible_service_actions_def service_access_footprint_def Let_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms two_decoded_acknowledgements_for_one_native_slot_require_product_serialization})
  then () else error "Unexpected oracle in scheduled ACK wire correspondence"
\<close>

end
