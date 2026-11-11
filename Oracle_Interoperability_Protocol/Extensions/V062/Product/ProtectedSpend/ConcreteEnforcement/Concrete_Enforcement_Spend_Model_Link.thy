theory Concrete_Enforcement_Spend_Model_Link
  imports "OIP_Signed_Ordinary_Spend_Model_Link.Signed_Ordinary_Spend_Model_Link"
begin

text \<open>
  The existing Recover ABI supplies an empty receipt list and only Recover grants.
  The concrete selected prefix has an earlier Ordinary receipt and both grant kinds.
  Reuse the checked state, call and result functions with those two fields restored.
\<close>

definition ces_spend_abi :: "integer list list list \<Rightarrow> integer list list option" where
  "ces_spend_abi ces_input =
    (case sl_nats ces_input of
      Some [[ces_call],[ces_scope],[ces_order_scope],[ces_order],[ces_header],
            ces_sessions,ces_modes,ces_balances,ces_funding,ces_roots,ces_reservations,
            ces_active,ces_evidence,ces_events,ces_freezes,ces_grants,ces_legal,
            ces_ordinary,ces_sync,ces_journal,ces_retained] \<Rightarrow>
        if length ces_call = 14 \<and> ces_call ! 0 = 0 \<and> ces_call ! 13 \<le> 1 \<and>
           length ces_scope = 11 \<and> ces_scope ! 10 = 1 \<and>
           length ces_order_scope = 11 \<and> ces_order_scope ! 10 = 1 \<and>
           8 \<le> length ces_order \<and> length ces_header = 5 \<and>
           sl_width 3 ces_sessions \<and> sl_width 3 ces_modes \<and>
           list_all (\<lambda>ces_row. ces_row ! 2 \<le> 4) ces_modes \<and>
           sl_width 4 ces_balances \<and> sl_width 6 ces_funding \<and>
           sl_width 18 ces_roots \<and> sl_width 14 ces_reservations \<and>
           sl_width 3 ces_active \<and> sl_width 9 ces_evidence \<and>
           sl_width 18 ces_events \<and> sl_width 3 ces_freezes \<and>
           sl_width 16 ces_grants \<and>
           list_all (\<lambda>ces_row. ces_row ! 0 = 0 \<and> ces_row ! 13 \<le> 1) ces_grants \<and>
           sl_width 2 ces_legal \<and> sl_width 2 ces_ordinary \<and>
           sl_width 2 ces_sync \<and> sl_width 4 ces_journal \<and>
           sl_width 24 ces_retained \<and>
           list_all (\<lambda>ces_row. ces_row ! 19 = 0 \<and> ces_row ! 20 \<le> 3) ces_retained
        then
          (let ces_initial =
             (sl_spend_state ces_header ces_sessions ces_modes ces_balances ces_funding
               ces_roots ces_reservations ces_active ces_evidence ces_events ces_freezes []
               ces_legal ces_ordinary ces_sync ces_journal)
                \<lparr>ps_spend_grants := map sos_grant ces_grants,
                 ps_spend_receipts := map sos_receipt ces_retained\<rparr>;
               ces_request = sl_spend_call ces_call ces_scope ces_order_scope ces_order
           in Some (map (map integer_of_nat)
                (sl_spend_result (ces_call ! 13 = 1) ces_request ces_initial)))
        else None
    | _ \<Rightarrow> None)"

export_code sl_wire_abi sos_wire_abi sos_spend_abi ces_spend_abi in SML
  module_name OIP_Concrete_Enforcement_Spend_Link file_prefix "oip_concrete_enforcement_spend_link"

end
