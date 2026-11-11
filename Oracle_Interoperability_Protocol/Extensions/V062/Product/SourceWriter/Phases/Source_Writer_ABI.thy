theory Source_Writer_ABI
  imports Source_Writer_Phases
begin

text \<open>Integer transport for the two input-only observations. A hash reply is
  an exact byte string to hash independently, never an observed write or a
  predicate over the native verdict. Success returns the six logical writes in
  actual reserve/prepare/publish order, the four consumed marks, and both sets
  of capacity sizes. No result byte string is an ABI argument.\<close>

fun sw_reply_rows :: "sw_writer_schedule \<Rightarrow> sw_writer_request \<Rightarrow> sw_writer_reply \<Rightarrow> nat list list" where
  "sw_reply_rows sw_revs sw_req SW_Outside_Chain = [[0]]"
| "sw_reply_rows sw_revs sw_req (SW_Need_Hash sw_raw) = [[1],sw_raw]"
| "sw_reply_rows sw_revs sw_req (SW_Capacity_Exceeded sw_init sw_append) = [[2],sw_init,sw_append]"
| "sw_reply_rows sw_revs sw_req (SW_Writer_Done sw_out) =
     [[3], [sw_w3 sw_revs,sw_j3 sw_revs,sw_w4 sw_revs,sw_w5 sw_revs,sw_j4 sw_revs,sw_w6 sw_revs],
      sw_initialize_sizes sw_out, sw_append_sizes sw_out,
      [fst (sw_empty_mark sw_out),fst (sw_genesis_mark sw_out),fst (sw_reservation_mark sw_out),fst (sw_prepared_mark sw_out)],
      snd (sw_empty_mark sw_out),snd (sw_genesis_mark sw_out),
      snd (sw_reservation_mark sw_out),snd (sw_prepared_mark sw_out),
      sw_issuer_preimage sw_req,sw_decision_json sw_req,
      sw_initializing_bytes sw_out,sw_genesis_bytes sw_out,sw_selected_genesis_bytes sw_out,
      sw_appending_bytes sw_out,sw_prepared_bytes sw_out,sw_selected_decision_bytes sw_out]"

definition sw_phase_integer ::
  "nat list list \<Rightarrow> (nat \<times> nat list) list \<Rightarrow> nat list list \<Rightarrow>
   (nat list \<times> nat list) list \<Rightarrow> nat list list list \<Rightarrow> nat list list" where
  "sw_phase_integer sw_rows sw_signers sw_good_keys sw_hash_rows sw_issuer_facts =
   (case sw_rows of
      [[sw_cd,sw_cf,sw_ca], [sw_rd,sw_rf,sw_ra],
       [sw_epoch,sw_domain,sw_event,sw_asset,sw_owner,sw_dest,sw_recipient,sw_amount,sw_kind,sw_ref],
       [sw_rule_domain,sw_quorum,sw_jcap,sw_wcap], sw_epochs, sw_issuer,
       sw_j_binding, sw_w_binding, sw_empty_j, sw_empty_w, sw_signature,
       [sw_ij,sw_iw,sw_gj,sw_initw,sw_gw,sw_aw,sw_pj,sw_pw]] \<Rightarrow>
        let sw_config = \<lparr>sw_cfg_profile = (sw_cd,sw_cf,sw_ca),
           sw_journal_binding_input = sw_j_binding, sw_witness_binding_input = sw_w_binding,
           sw_roster_domain = sw_rule_domain, sw_roster_epochs = sw_epochs,
           sw_roster_issuer = sw_issuer, sw_roster_quorum = sw_quorum, sw_roster_signers = sw_signers,
           sw_journal_cap = sw_jcap, sw_witness_cap = sw_wcap\<rparr>;
            sw_req = \<lparr>sw_req_profile = (sw_rd,sw_rf,sw_ra), sw_req_epoch = sw_epoch,
           sw_req_domain = sw_domain, sw_req_event = sw_event, sw_req_asset = sw_asset,
           sw_req_owner = sw_owner, sw_req_destination = sw_dest, sw_req_recipient = sw_recipient,
           sw_req_amount = sw_amount, sw_req_kind = sw_kind, sw_req_reference = sw_ref, sw_req_signature = sw_signature\<rparr>;
            sw_revs = \<lparr>sw_j2 = sw_ij, sw_w2 = sw_iw, sw_j3 = sw_gj, sw_w3 = sw_initw,
           sw_w4 = sw_gw, sw_w5 = sw_aw, sw_j4 = sw_pj, sw_w6 = sw_pw\<rparr>
        in sw_reply_rows sw_revs sw_req
           (sw_run (map_of sw_hash_rows) sw_config sw_req sw_revs sw_empty_j sw_empty_w sw_good_keys sw_issuer_facts)
      | _ \<Rightarrow> [[0]])"

export_code sw_phase_integer
  in SML module_name OIP_Source_Writer_Phase_ABI file_prefix "oip_source_writer_phase_abi"

end
