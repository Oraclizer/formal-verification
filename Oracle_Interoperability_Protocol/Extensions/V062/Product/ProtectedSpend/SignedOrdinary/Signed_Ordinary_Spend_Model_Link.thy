theory Signed_Ordinary_Spend_Model_Link
  imports "OIP_Signed_Legal_Model_Link.Signed_Legal_Model_Link"
begin

definition sos_wire_abi :: "integer list list \<Rightarrow> integer list option" where
  "sos_wire_abi osv_input =
    (case map (map nat_of_integer) osv_input of
      [osv_packet,osv_core_bytes,osv_preimage,osv_signature,osv_context,osv_words,osv_root_amount,osv_amount] \<Rightarrow>
        (if \<not> list_all (list_all sl_u64) osv_input then None
         else Option.bind (decode_wire_packet osv_packet) (\<lambda>osv_decoded.
           let osv_core = packet_core osv_decoded; osv_op = wire_operation_body osv_core in
           if wire_version osv_core = 6 \<and> wire_message_family osv_core = Wire_State_Sync \<and>
              wire_opcode osv_op = 6 \<and> wire_deadline osv_op = Deadline_Absent \<and>
              [wire_version osv_core,wire_deployment osv_core,wire_source_domain osv_core,wire_target_domain osv_core,
                wire_principal osv_core,wire_authority_epoch osv_core] @ wire_uuid osv_core = osv_context \<and>
              wire_words osv_op = osv_words \<and> wire_blobs osv_op = [osv_root_amount,osv_amount] \<and>
              encode_wire_core osv_core = osv_core_bytes \<and> envelope_signing_bytes osv_core = osv_preimage \<and>
              packet_signature osv_decoded = osv_signature
           then map_option (map integer_of_nat) (code_typed_spend_ir osv_core)
           else None))
     | _ \<Rightarrow> None)"

definition sos_scope where
  "sos_scope osv_row = (sl_scope osv_row)\<lparr>ps_kind :=
    (if osv_row ! 10 = 0 then PS_Ordinary else PS_Recover)\<rparr>"

definition sos_payload where
  "sos_payload osv_header osv_scope =
    \<lparr>ps_message = osv_header ! 0,ps_caller = osv_header ! 1,ps_session = osv_header ! 2,
      ps_payload_cut = sl_cut (osv_header ! 3) (osv_header ! 4),ps_origin_epoch = osv_header ! 5,
      ps_reference = osv_header ! 6,ps_scope = sos_scope osv_scope\<rparr>"

definition sos_call where
  "sos_call osv_header osv_scope =
    \<lparr>ps_route = PS_Normal,ps_actor = osv_header ! 1,ps_call_id = (osv_header ! 2,osv_header ! 3),
      ps_expected = sl_cut (osv_header ! 4) (osv_header ! 5),
      ps_payload = sos_payload (drop 6 osv_header) osv_scope,ps_enforcement = None\<rparr>"

definition sos_grant where
  "sos_grant osv_row =
    \<lparr>ps_grant_route = PS_Normal,ps_grant_actor = osv_row ! 1,ps_grant_epoch = osv_row ! 2,
      ps_grant_scope = sos_scope (drop 3 osv_row),
      ps_grant_jurisdiction = osv_row ! 14,ps_grant_basis = osv_row ! 15\<rparr>"

definition sos_reply where
  "sos_reply osv_row = (if osv_row ! 0 = 0
    then PS_Spend_Executed (osv_row ! 1,osv_row ! 2) (osv_row ! 3)
    else if osv_row ! 0 = 1 then PS_Spend_Rejected
    else if osv_row ! 0 = 2 then PS_Spend_Busy else PS_Spend_Unavailable)"

definition sos_receipt where
  "sos_receipt osv_row =
    ((osv_row ! 0,osv_row ! 1),
      (sos_payload (drop 2 osv_row) (drop 9 osv_row),None,sos_reply (drop 20 osv_row)))"

lemma sos_exact_retained_preserves_state:
  assumes "ps_access osv_verified osv_call osv_state" "ps_up osv_state"
    "map_of (ps_spend_receipts osv_state) (ps_call_id osv_call) =
      Some (ps_payload osv_call,ps_enforcement osv_call,osv_reply)"
  shows "ps_submit_spend True osv_verified osv_call osv_state = (osv_state,osv_reply)"
  using assms by (simp add: ps_submit_spend_def)

definition sos_diagnostics where
  "sos_diagnostics osv_call osv_state =
    (let osv_slot = map_of (ps_spend_receipts osv_state) (ps_call_id osv_call);
         osv_exact = (case osv_slot of None \<Rightarrow> False
           | Some (osv_payload,osv_order,osv_reply) \<Rightarrow>
               osv_payload = ps_payload osv_call \<and> osv_order = ps_enforcement osv_call)
     in [3,pe_bit (osv_slot \<noteq> None),pe_bit osv_exact,pe_bit (ps_granted osv_call 0 0 osv_state),
         pe_bit (ps_expected osv_call = ps_cut osv_state),
         pe_bit (ps_payload_cut (ps_payload osv_call) = ps_cut osv_state)])"

definition sos_spend_abi :: "integer list list list \<Rightarrow> integer list list option" where
  "sos_spend_abi osv_input =
    (case sl_nats osv_input of
      Some [[osv_header],[osv_scope],[osv_state],osv_sessions,osv_modes,osv_balances,osv_funding,osv_roots,osv_reservations,
            osv_active,osv_evidence,osv_events,osv_freezes,osv_grants,osv_legal,osv_ordinary,osv_sync,osv_journal,osv_retained] \<Rightarrow>
        if length osv_header = 14 \<and> osv_header ! 0 = 0 \<and> osv_header ! 13 \<le> 1 \<and>
           length osv_scope = 11 \<and> osv_scope ! 10 = 0 \<and> length osv_state = 5 \<and>
           sl_width 3 osv_sessions \<and> sl_width 3 osv_modes \<and> list_all (\<lambda>osv_row. osv_row ! 2 \<le> 4) osv_modes \<and>
           sl_width 4 osv_balances \<and> sl_width 6 osv_funding \<and> sl_width 18 osv_roots \<and>
           sl_width 14 osv_reservations \<and> sl_width 3 osv_active \<and> sl_width 9 osv_evidence \<and>
           sl_width 18 osv_events \<and> sl_width 3 osv_freezes \<and> sl_width 16 osv_grants \<and>
           list_all (\<lambda>osv_row. osv_row ! 0 = 0 \<and> osv_row ! 13 \<le> 1) osv_grants \<and>
           sl_width 2 osv_legal \<and> sl_width 2 osv_ordinary \<and> sl_width 2 osv_sync \<and> sl_width 4 osv_journal \<and>
           sl_width 24 osv_retained \<and> list_all (\<lambda>osv_row. osv_row ! 19 = 0 \<and> osv_row ! 20 \<le> 3) osv_retained
        then
          (let osv_initial = (sl_spend_state osv_state osv_sessions osv_modes osv_balances osv_funding
                    osv_roots osv_reservations osv_active osv_evidence osv_events osv_freezes []
                    osv_legal osv_ordinary osv_sync osv_journal)
                    \<lparr>ps_spend_grants := map sos_grant osv_grants,
                     ps_spend_receipts := map sos_receipt osv_retained\<rparr>;
               osv_call = sos_call osv_header osv_scope;
               osv_rows = sl_spend_result (osv_header ! 13 = 1) osv_call osv_initial
           in Some (map (map integer_of_nat) (osv_rows @ [sos_diagnostics osv_call osv_initial])))
        else None
     | _ \<Rightarrow> None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sos_exact_retained_preserves_state
      a_spend_summary_consumes_its_actual_decoded_values}) then ()
  else error "Unexpected oracle in the signed ordinary-spend link"
\<close>

export_code sos_wire_abi sos_spend_abi in SML
  module_name OIP_Signed_Ordinary_Spend_Link file_prefix "oip_signed_ordinary_spend_link"

end
