theory Protected_Spend_Export
  imports "OIP_Protected_Spend_G0.Protected_Spend_G0" "HOL-Library.Code_Target_Nat"
begin

definition pe_bit :: "bool \<Rightarrow> nat" where "pe_bit p5_value = (if p5_value then 1 else 0)"
definition pe_optional :: "nat option \<Rightarrow> nat list" where
  "pe_optional p5_value = (case p5_value of None \<Rightarrow> [0,0] | Some p5_word \<Rightarrow> [1,p5_word])"

fun pe_kind where
  "pe_kind PS_Ordinary = (0::nat)" | "pe_kind PS_Recover = 1" | "pe_kind PS_Seize = 2"
| "pe_kind PS_Confiscate = 3" | "pe_kind PS_Liquidate = 4"

fun pe_route where
  "pe_route PS_Normal = (0::nat)" | "pe_route PS_Administrative = 1"
| "pe_route PS_Adapter = 2" | "pe_route PS_Force_Inclusion = 3"

fun pe_mode where
  "pe_mode ACTIVE = (0::nat)" | "pe_mode RESTRICTED = 1" | "pe_mode FROZEN = 2"
| "pe_mode SEIZED = 3" | "pe_mode CONFISCATED = 4"

definition pe_binding where
  "pe_binding p5_binding = [fst (ps_origin p5_binding),snd (ps_origin p5_binding),ps_asset p5_binding,
    ps_owner p5_binding,ps_destination p5_binding,ps_receiver p5_binding,ps_root_amount p5_binding]"

definition pe_scope where
  "pe_scope p5_scope = pe_binding (ps_root p5_scope) @
    [ps_sender p5_scope,ps_recipient p5_scope,ps_amount p5_scope,pe_kind (ps_kind p5_scope)]"

definition pe_payload where
  "pe_payload p5_payload = [ps_message p5_payload,ps_caller p5_payload,ps_session p5_payload,
    cut_authority_epoch (ps_payload_cut p5_payload),cut_revision (ps_payload_cut p5_payload),
    ps_origin_epoch p5_payload,ps_reference p5_payload] @ pe_scope (ps_scope p5_payload)"

definition pe_enforcement where
  "pe_enforcement p5_optional = (case p5_optional of None \<Rightarrow> [0]
    | Some p5_order \<Rightarrow> [1] @ pe_scope (ps_order_scope p5_order) @
        [ps_officer p5_order,ps_jurisdiction p5_order,ps_legal_basis p5_order,length (ps_assets p5_order)] @ ps_assets p5_order @
        (case ps_prior_seizure p5_order of None \<Rightarrow> [0,0,0] | Some (p5_domain,p5_event) \<Rightarrow> [1,p5_domain,p5_event]) @
        pe_optional (ps_appeal_deadline p5_order))"

definition pe_call where
  "pe_call p5_call = [pe_route (ps_route p5_call),ps_actor p5_call,fst (ps_call_id p5_call),snd (ps_call_id p5_call),
    cut_authority_epoch (ps_expected p5_call),cut_revision (ps_expected p5_call)] @
    pe_payload (ps_payload p5_call) @ pe_enforcement (ps_enforcement p5_call)"

fun pe_spend_reply where
  "pe_spend_reply PS_Spend_Rejected = [1]"
| "pe_spend_reply PS_Spend_Busy = [2]"
| "pe_spend_reply PS_Spend_Unavailable = [3]"
| "pe_spend_reply (PS_Spend_Executed (p5_domain,p5_event) p5_position) = [0,p5_domain,p5_event,p5_position]"

fun pe_reply where
  "pe_reply (PG_Current None) = [0,0]"
| "pe_reply (PG_Current (Some (p5_cut,p5_mode))) =
    [0,1,cut_authority_epoch p5_cut,cut_revision p5_cut] @
       (case p5_mode of None \<Rightarrow> [0,0] | Some p5_actual \<Rightarrow> [1,pe_mode p5_actual])"
| "pe_reply (PG_Spend p5_reply) = [1] @ pe_spend_reply p5_reply"
| "pe_reply (PG_Primary p5_code p5_commit p5_waiting) = [2,p5_code] @ pe_optional p5_commit @ [pe_bit p5_waiting]"

definition pe_request where
  "pe_request p5_operation p5_machine =
    (let p5_input = pf_input p5_machine; p5_state = pf_state p5_machine in
      case p5_operation of PG_Frozen_Read \<Rightarrow>
        [0,pf_actor p5_input,1,ps_epoch p5_state,ps_revision p5_state,pf_destination p5_input,pf_asset p5_input]
      | PG_Protected_Debit \<Rightarrow> [3,pf_actor p5_input,1,pf_actor p5_input,3,ps_epoch p5_state,ps_revision p5_state] @
          pe_binding ((pf_root_binding p5_input)\<lparr>ps_root_amount := pf_amount p5_input\<rparr>) @ [0,ps_epoch p5_state]
      | _ \<Rightarrow> case pf_spend_call (if p5_operation = PG_Ordinary_Spend then PS_Ordinary else PS_Recover) p5_machine of
          None \<Rightarrow> [] | Some p5_call \<Rightarrow> [if p5_operation = PG_Ordinary_Spend then 1 else 2] @ pe_call p5_call)"

definition pe_snapshot_rows where
  "pe_snapshot_rows p5_role p5_index p5_snapshot =
    map (\<lambda>((p5_domain,p5_asset),p5_mode). [26,p5_role,p5_index,p5_domain,p5_asset,pe_mode p5_mode]) (pf_snapshot_modes p5_snapshot) @
    map (\<lambda>((p5_domain,p5_asset,p5_holder),p5_value). [27,p5_role,p5_index,p5_domain,p5_asset,p5_holder,p5_value]) (pf_snapshot_balances p5_snapshot) @
    map (\<lambda>(((p5_origin_domain,p5_event),(p5_domain,p5_asset,p5_holder)),p5_value).
      [28,p5_role,p5_index,p5_origin_domain,p5_event,p5_domain,p5_asset,p5_holder,p5_value]) (pf_snapshot_funding p5_snapshot)"

definition pe_state_rows where
  "pe_state_rows p5_role p5_machine =
    (let p5_state = pf_state p5_machine in
      [[10,p5_role,ps_epoch p5_state,ps_revision p5_state,ps_clock p5_state,pe_bit (ps_up p5_state),pe_bit (ps_available p5_state)]] @
      map (\<lambda>((p5_domain,p5_asset),p5_mode). [11,p5_role,p5_domain,p5_asset,pe_mode p5_mode]) (ps_modes p5_state) @
      map (\<lambda>((p5_domain,p5_asset,p5_holder),p5_value). [12,p5_role,p5_domain,p5_asset,p5_holder,p5_value]) (ps_balances p5_state) @
      map (\<lambda>(((p5_origin_domain,p5_event),(p5_domain,p5_asset,p5_holder)),p5_value).
        [13,p5_role,p5_origin_domain,p5_event,p5_domain,p5_asset,p5_holder,p5_value]) (ps_funding p5_state) @
      map (\<lambda>(p5_key,p5_slot). [14,p5_role,fst p5_key,snd p5_key] @ pe_binding (ps_slot_binding p5_slot) @
        [ps_slot_epoch p5_slot] @ (case ps_decision_kind p5_slot of None \<Rightarrow> [0,0]
          | Some p5_kind \<Rightarrow> [1,if p5_kind = Confirmed_Decision then 1 else 2]) @
        pe_optional (ps_decision_position p5_slot) @ pe_optional (ps_settled p5_slot) @ pe_optional (ps_published p5_slot)) (ps_roots p5_state) @
      map (\<lambda>(p5_key,p5_slot). [15,p5_role,fst p5_key,snd p5_key] @ pe_binding (ps_reserved p5_slot) @
        [ps_holder p5_slot,ps_generation p5_slot,ps_expires p5_slot,ps_phase p5_slot,ps_pending p5_slot]) (ps_reservations p5_state) @
      map (\<lambda>(p5_asset,p5_key). [16,p5_role,p5_asset,fst p5_key,snd p5_key]) (ps_active p5_state) @
      map (\<lambda>(p5_reference,(p5_binding,p5_kind)). [17,p5_role,p5_reference] @ pe_binding p5_binding @
        [if p5_kind = Confirmed_Decision then 1 else 2]) (ps_evidence p5_state) @
      map (\<lambda>(p5_key,p5_event). [18,p5_role,fst p5_key,snd p5_key] @ pe_binding (ps_legal_binding p5_event) @
        [ps_legal_epoch p5_event,ps_legal_officer p5_event,ps_legal_jurisdiction p5_event,ps_legal_basis_value p5_event,
         ps_emitted_position p5_event] @ pe_optional (ps_applied_position p5_event) @ pe_optional (ps_legal_published p5_event)) (ps_legal_events p5_state) @
      map (\<lambda>(p5_asset,p5_key). [19,p5_role,p5_asset,fst p5_key,snd p5_key]) (ps_active_freezes p5_state) @
      map (\<lambda>p5_grant. [20,p5_role,pe_route (ps_grant_route p5_grant),ps_grant_actor p5_grant,ps_grant_epoch p5_grant] @
        pe_scope (ps_grant_scope p5_grant) @ [ps_grant_jurisdiction p5_grant,ps_grant_basis p5_grant]) (ps_spend_grants p5_state) @
      map (\<lambda>(p5_id,(p5_payload,p5_order,p5_reply)). [21,p5_role,fst p5_id,snd p5_id] @
        pe_payload p5_payload @ pe_enforcement p5_order @ pe_spend_reply p5_reply) (ps_spend_receipts p5_state) @
      map (\<lambda>p5_id. [22,p5_role,fst p5_id,snd p5_id]) (ps_ordinary_ids p5_state) @
      map (\<lambda>p5_id. [23,p5_role,fst p5_id,snd p5_id]) (ps_legal_ids p5_state) @
      map (\<lambda>p5_id. [24,p5_role,fst p5_id,snd p5_id]) (ps_sync_ids p5_state) @
      map (\<lambda>(p5_id,p5_target,p5_position). [25,p5_role,fst p5_id,snd p5_id,p5_target,p5_position]) (ps_journal p5_state) @
      concat (map (\<lambda>(p5_index,p5_snapshot). pe_snapshot_rows p5_role p5_index p5_snapshot)
        (zip [0..<length (pf_history p5_machine)] (pf_history p5_machine))) @
      map (\<lambda>(p5_category,p5_sequence,p5_code,p5_commit,p5_waiting).
        [29,p5_role,p5_category,p5_sequence,p5_code] @ pe_optional p5_commit @ [pe_bit p5_waiting]) (pf_trace p5_machine))"

definition pe_decode where
  "pe_decode p5_words = (case p5_words of
      [p5_tag,p5_actor,p5_epoch,p5_asset,p5_source,p5_destination,p5_root_event,p5_freeze_event,
       p5_sender,p5_recipient,p5_initial,p5_root_amount,p5_amount,p5_jurisdiction,p5_basis,p5_authorized] \<Rightarrow>
        if p5_tag > 3 \<or> p5_authorized > 1 then None else Some
          ((if p5_tag = 0 then PG_Frozen_Read else if p5_tag = 1 then PG_Ordinary_Spend
            else if p5_tag = 2 then PG_Recovery_Spend else PG_Protected_Debit),
           \<lparr>pf_actor = p5_actor,pf_epoch = p5_epoch,pf_asset = p5_asset,pf_source = p5_source,pf_destination = p5_destination,
             pf_root_event = p5_root_event,pf_freeze_event = p5_freeze_event,pf_sender = p5_sender,pf_recipient = p5_recipient,
             pf_initial = p5_initial,pf_root_amount = p5_root_amount,pf_amount = p5_amount,
             pf_jurisdiction = p5_jurisdiction,pf_basis = p5_basis,pf_authorized = (p5_authorized = 1)\<rparr>)
    | _ \<Rightarrow> None)"

definition pe_abi where
  "pe_abi p5_mode p5_words =
    (if p5_mode > 1 \<or> \<not> list_all (\<lambda>p5_word. p5_word < 2^64) p5_words then [[0,1,p5_mode,1]]
     else case pe_decode p5_words of None \<Rightarrow> [[0,1,p5_mode,1]] | Some (p5_operation,p5_input) \<Rightarrow>
       case pg_run (p5_mode = 0) p5_operation p5_input of None \<Rightarrow> [[0,1,p5_mode,2]]
       | Some (p5_before,p5_after,p5_reply) \<Rightarrow>
         if \<not> pg_freeze_ready p5_before then [[0,1,p5_mode,3]]
         else [[0,1,p5_mode,0],[1] @ p5_words,[2,pe_bit (pg_freeze_ready p5_before),
                 pe_bit (pg_spend_ready PS_Ordinary p5_before),pe_bit (pg_spend_ready PS_Recover p5_before)],
               [3] @ pe_request p5_operation p5_before,[4] @ pe_reply p5_reply] @
               pe_state_rows 0 p5_before @ pe_state_rows 1 p5_after)"

definition pe_integer_abi :: "integer \<Rightarrow> integer list \<Rightarrow> integer list list" where
  "pe_integer_abi p5_mode p5_words = (if p5_mode < 0 \<or> list_ex (\<lambda>p5_word. p5_word < 0) p5_words
    then [[0,1,p5_mode,1]] else map (map integer_of_nat) (pe_abi (nat_of_integer p5_mode) (map nat_of_integer p5_words)))"

lemma pe_decode_failure_does_not_become_a_protocol_refusal:
  "pe_decode p5_words = None \<Longrightarrow> pe_abi p5_mode p5_words = [[0,1,p5_mode,1]]"
  by (simp add: pe_abi_def)

text \<open>
  All result, readiness, receipt and state rows are generated observations.
  Inputs contain operation and typed fixture parameters only. Metadata status
  1 is malformed/domain input, 2 operational prefix not established and 3 a
  failed reached-Freeze invariant. A metadata result contains no protocol
  verdict rows. Mode 1 changes only the ordinary protected-mode branch; every
  other operation is observed from the same independently recomputed seed.
  Output integer words are lossless; no expected answer or source result is
  accepted by this entry point.
\<close>

code_reserved (SML) before

export_code pe_integer_abi in SML module_name OIP_Protected_Spend file_prefix "oip_protected_spend"

end
