theory Signed_Publish_Primary_Model_Link
  imports "OIP_Signed_Legal_Model_Link.Signed_Legal_Model_Link"
    "OIP_Completion_Gates_Export.Completion_Gates_Export"
begin

lemma spp_fresh_ordinary_body_is_the_existing_publication_update:
  assumes spp_legal: "map_of (ps_legal_events spp_before) (ps_origin spp_binding) = None"
    and spp_root: "map_of (ps_roots spp_before) (ps_origin spp_binding) = Some spp_slot"
    and spp_matches: "ps_slot_binding spp_slot = spp_binding" "ps_slot_epoch spp_slot = pf_epoch spp_input"
    and spp_settled: "ps_settled spp_slot \<noteq> None"
    and spp_fresh: "ps_published spp_slot = None"
  shows "pf_ordinary_body PF_Publish spp_binding spp_input spp_before =
    (pf_store_root (spp_slot\<lparr>ps_published := Some (ps_revision spp_before)\<rparr>) spp_before,22,True)"
  using assms by (simp add: pf_ordinary_body_def Let_def)

lemma spp_publication_update_preserves_financial_rows:
  "ps_balances (pf_store_root spp_slot spp_before) = ps_balances spp_before"
  "ps_funding (pf_store_root spp_slot spp_before) = ps_funding spp_before"
  "ps_reservations (pf_store_root spp_slot spp_before) = ps_reservations spp_before"
  "ps_active (pf_store_root spp_slot spp_before) = ps_active spp_before"
  "ps_evidence (pf_store_root spp_slot spp_before) = ps_evidence spp_before"
  by (simp_all add: pf_store_root_def)

definition spp_fixture_input :: "nat \<Rightarrow> nat \<Rightarrow> ps_binding \<Rightarrow> pf_input" where
  "spp_fixture_input spp_actor spp_origin_epoch spp_binding =
    \<lparr>pf_actor = spp_actor, pf_epoch = spp_origin_epoch, pf_asset = ps_asset spp_binding,
      pf_source = fst (ps_origin spp_binding), pf_destination = ps_destination spp_binding,
      pf_root_event = snd (ps_origin spp_binding), pf_freeze_event = 0, pf_sender = ps_receiver spp_binding,
      pf_recipient = ps_receiver spp_binding, pf_initial = 0, pf_root_amount = ps_root_amount spp_binding,
      pf_amount = 0, pf_jurisdiction = 0, pf_basis = 0, pf_authorized = False\<rparr>"

definition spp_released_credit :: "ps_binding \<Rightarrow> ps_state \<Rightarrow> nat \<Rightarrow>
  wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> nat list" where
  "spp_released_credit spp_binding spp_state spp_credit_position spp_requested spp_retained =
    (let spp_origin = ps_origin spp_binding;
         spp_selected = map_option (\<lambda>spp_slot.
           ((case (ps_decision_kind spp_slot,ps_decision_position spp_slot) of
              (Some spp_kind,Some spp_pos) \<Rightarrow> Some (spp_kind,spp_pos)
            | _ \<Rightarrow> None),ps_settled spp_slot,ps_published spp_slot))
           (map_of (ps_roots spp_state) spp_origin)
     in cg_reply_words (cg_observe True spp_origin (map_of (ps_active spp_state) (ps_asset spp_binding))
          spp_selected spp_requested (Some (spp_retained,(1,Some spp_credit_position)))))"

definition spp_state_view :: "nat \<Rightarrow> ps_state \<Rightarrow> nat list list" where
  "spp_state_view spp_role spp_state =
    sl_spend_projection spp_role spp_state @
    map (\<lambda>(spp_asset,(spp_domain,spp_event)). [16,spp_role,spp_asset,spp_domain,spp_event]) (ps_active spp_state) @
    map (\<lambda>(spp_ref,spp_binding,spp_kind). [17,spp_role,spp_ref] @ pe_binding spp_binding @
      [if spp_kind = Confirmed_Decision then 1 else 2]) (ps_evidence spp_state) @
    map (\<lambda>(spp_actor,spp_sequence). [22,spp_role,spp_actor,spp_sequence]) (ps_ordinary_ids spp_state)"

definition spp_run :: "bool \<Rightarrow> nat list \<Rightarrow> ps_binding \<Rightarrow> nat \<Rightarrow>
  wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> ps_state \<Rightarrow> nat list list option" where
  "spp_run spp_origin_allowed spp_request spp_binding spp_credit_position spp_requested spp_retained spp_before =
    (case spp_request of [spp_actor,spp_sequence,spp_session,spp_target,spp_origin_epoch,
       spp_cut_epoch,spp_cut_revision,spp_verified,spp_no_credential] \<Rightarrow>
      (let spp_origin = ps_origin spp_binding;
           spp_session_value = Some (spp_actor,ps_epoch spp_before);
           spp_state_ready = (case map_of (ps_reservations spp_before) spp_origin of
               Some spp_reservation \<Rightarrow> ps_phase spp_reservation = 5 \<and> ps_reserved spp_reservation = spp_binding
             | None \<Rightarrow> False)
       in if \<not> spp_origin_allowed \<or> spp_verified \<noteq> 1 \<or> spp_no_credential \<noteq> 1 \<or>
             spp_target \<noteq> fst spp_origin \<or> \<not> spp_state_ready \<or>
             map_of (ps_sessions spp_before) spp_session \<noteq> spp_session_value \<or>
             map_of (ps_sessions spp_before) 1 \<noteq> spp_session_value \<or>
             map_of (ps_legal_events spp_before) spp_origin \<noteq> None
          then None
          else let spp_machine = \<lparr>pf_input = spp_fixture_input spp_actor spp_origin_epoch spp_binding,
                     pf_state = spp_before,pf_history = [],pf_trace = []\<rparr>;
                   (spp_next,spp_committed) = pf_ordinary True spp_sequence spp_binding PF_Publish
                     (sl_cut spp_cut_epoch spp_cut_revision) spp_machine;
                   spp_after = pf_state spp_next
               in (case pf_trace spp_next of [(spp_category,spp_id,spp_code,spp_commit,spp_wait)] \<Rightarrow>
                   Some ([[0,spp_category,spp_id,spp_code] @ pe_optional spp_commit @
                       [pe_bit spp_committed,pe_bit spp_wait],
                       [1,0] @ spp_released_credit spp_binding spp_before spp_credit_position spp_requested spp_retained,
                       [1,1] @ spp_released_credit spp_binding spp_after spp_credit_position spp_requested spp_retained] @
                       spp_state_view 0 spp_before @ spp_state_view 1 spp_after)
                 | _ \<Rightarrow> None))
    | _ \<Rightarrow> None)"

definition spp_abi :: "bool \<Rightarrow> integer list list \<Rightarrow> integer list list list \<Rightarrow> integer list list option" where
  "spp_abi spp_origin_allowed spp_request_rows spp_state_rows =
    (case (sl_nats [spp_request_rows],sl_nats spp_state_rows) of
       (Some [[spp_request,spp_binding,[spp_credit_position],spp_requested,spp_retained]],
        Some [[spp_header],spp_sessions,spp_modes,spp_balances,spp_funding,spp_roots,spp_reservations,
          spp_active,spp_evidence,spp_ordinary,spp_journal]) \<Rightarrow>
       if length spp_binding = 7 \<and> length spp_header = 5 \<and>
          sl_width 3 spp_sessions \<and> sl_width 3 spp_modes \<and> sl_width 4 spp_balances \<and>
          sl_width 6 spp_funding \<and> sl_width 18 spp_roots \<and> sl_width 14 spp_reservations \<and>
          sl_width 3 spp_active \<and> sl_width 9 spp_evidence \<and> sl_width 2 spp_ordinary \<and>
          sl_width 4 spp_journal
       then let spp_before = sl_spend_state spp_header spp_sessions spp_modes spp_balances spp_funding
              spp_roots spp_reservations spp_active spp_evidence [] [] [] [] spp_ordinary [] spp_journal
            in map_option (map (map integer_of_nat))
                 (spp_run spp_origin_allowed spp_request (sl_binding spp_binding) spp_credit_position
                    spp_requested spp_retained spp_before)
       else None
     | _ \<Rightarrow> None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms spp_fresh_ordinary_body_is_the_existing_publication_update
      spp_publication_update_preserves_financial_rows cg_ready_refines_the_public_outcome_gate})
  then () else error "Unexpected oracle in signed primary publication link"
\<close>

export_code spp_abi in SML module_name OIP_Signed_Publish_Primary
  file_prefix "oip_signed_publish_primary"

end
