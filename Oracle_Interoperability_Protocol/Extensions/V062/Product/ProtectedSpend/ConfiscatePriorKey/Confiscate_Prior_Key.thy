theory Confiscate_Prior_Key
  imports "OIP_Signed_Legal_Model_Link.Signed_Legal_Model_Link"
begin

definition cpk_scope where
  "cpk_scope cpk_native cpk_fields =
    \<lparr>ps_root = \<lparr>ps_origin = native_origin cpk_native,ps_asset = native_asset cpk_native,
      ps_owner = native_funding_owner cpk_native,ps_destination = native_destination cpk_native,
      ps_receiver = native_recipient cpk_native,ps_root_amount = native_amount cpk_native\<rparr>,
      ps_sender = spend_sender cpk_fields,ps_recipient = spend_recipient cpk_fields,
      ps_amount = spend_amount cpk_fields,ps_kind = PS_Confiscate\<rparr>"

definition cpk_call where
  "cpk_call cpk_native cpk_fields cpk_enforcement cpk_assets =
    (let cpk_scope_value = cpk_scope cpk_native cpk_fields; cpk_id = native_id cpk_native;
         cpk_cut = native_cut cpk_native; cpk_actor = fst cpk_id
     in \<lparr>ps_route = PS_Normal,ps_actor = cpk_actor,ps_call_id = cpk_id,ps_expected = cpk_cut,
          ps_payload = \<lparr>ps_message = native_reference cpk_native,ps_caller = cpk_actor,
            ps_session = native_session cpk_native,ps_payload_cut = cpk_cut,
            ps_origin_epoch = native_origin_epoch cpk_native,ps_reference = spend_reference cpk_fields,
            ps_scope = cpk_scope_value\<rparr>,
          ps_enforcement = Some \<lparr>ps_order_scope = cpk_scope_value,ps_officer = enforcement_officer cpk_enforcement,
            ps_jurisdiction = enforcement_jurisdiction cpk_enforcement,ps_legal_basis = enforcement_basis cpk_enforcement,
            ps_assets = cpk_assets,ps_prior_seizure = enforcement_prior_seizure cpk_enforcement,
            ps_appeal_deadline = enforcement_appeal_deadline cpk_enforcement\<rparr>\<rparr>)"

definition cpk_active_entry where
  "cpk_active_entry cpk_row =
    (cpk_row ! 0,\<lparr>ps_seizure_key = (cpk_row ! 1,cpk_row ! 2),
      ps_seizure_freeze = (cpk_row ! 3,cpk_row ! 4),
      ps_seizure_deadline = sl_optional (cpk_row ! 5) (cpk_row ! 6)\<rparr>)"

definition cpk_grant where
  "cpk_grant cpk_row =
    \<lparr>ps_grant_route = PS_Normal,ps_grant_actor = cpk_row ! 1,ps_grant_epoch = cpk_row ! 2,
      ps_grant_scope = (sl_scope (drop 3 cpk_row))\<lparr>ps_kind := PS_Confiscate\<rparr>,
      ps_grant_jurisdiction = cpk_row ! 14,ps_grant_basis = cpk_row ! 15\<rparr>"

definition cpk_funding_words where
  "cpk_funding_words cpk_scope_value cpk_state =
    (let cpk_root = ps_root cpk_scope_value; cpk_origin = ps_origin cpk_root;
         cpk_sender = ps_holder_account cpk_root (ps_sender cpk_scope_value);
         cpk_recipient = ps_holder_account cpk_root (ps_recipient cpk_scope_value)
     in [ps_epoch cpk_state,ps_revision cpk_state,
        ps_get (ps_balances cpk_state) cpk_sender,ps_get (ps_balances cpk_state) cpk_recipient,
        ps_get (ps_funding cpk_state) (cpk_origin,cpk_sender),ps_get (ps_funding cpk_state) (cpk_origin,cpk_recipient)])"

lemma cpk_readiness_consumes_the_active_seizure_key_and_clock:
  assumes "map_of (ps_active_freezes cpk_state) (ps_asset (ps_root (ps_order_scope cpk_order))) = Some cpk_freeze"
    "map_of (ps_active_seizures cpk_state) (ps_asset (ps_root (ps_order_scope cpk_order))) = Some cpk_seizure"
  shows "ps_confiscation_ready cpk_order cpk_mode cpk_state \<longleftrightarrow>
    ps_seizure_freeze cpk_seizure = cpk_freeze \<and> ps_prior_seizure cpk_order = Some (ps_seizure_key cpk_seizure) \<and>
    cpk_mode \<in> {SEIZED,CONFISCATED} \<and>
    (case ps_appeal_deadline cpk_order of None \<Rightarrow> False | Some cpk_deadline \<Rightarrow>
      ps_seizure_deadline cpk_seizure = Some cpk_deadline \<and> cpk_deadline \<le> ps_clock cpk_state)"
  using assms by (simp add: ps_confiscation_ready_def Let_def)

lemma cpk_wrong_prior_refuses_at_the_same_cut:
  assumes cpk_cut: "ps_expected cpk_request = ps_cut cpk_state" "ps_payload_cut (ps_payload cpk_request) = ps_cut cpk_state"
    and cpk_mode: "map_of (ps_modes cpk_state)
      (ps_destination (ps_root (ps_scope (ps_payload cpk_request))),ps_asset (ps_root (ps_scope (ps_payload cpk_request)))) = Some cpk_mode_value"
    and cpk_order: "ps_kind (ps_scope (ps_payload cpk_request)) = PS_Confiscate" "ps_enforcement cpk_request = Some cpk_order_value"
    and cpk_selected: "map_of (ps_active_freezes cpk_state) (ps_asset (ps_root (ps_order_scope cpk_order_value))) = Some cpk_freeze"
      "map_of (ps_active_seizures cpk_state) (ps_asset (ps_root (ps_order_scope cpk_order_value))) = Some cpk_seizure"
    and cpk_wrong: "ps_prior_seizure cpk_order_value \<noteq> Some (ps_seizure_key cpk_seizure)"
  shows "ps_apply_spend True cpk_request cpk_state = (cpk_state,PS_Spend_Rejected)"
proof -
  have "\<not> ps_confiscation_ready cpk_order_value cpk_mode_value cpk_state"
    using cpk_wrong by (simp add: cpk_readiness_consumes_the_active_seizure_key_and_clock[OF cpk_selected])
  with cpk_cut cpk_mode cpk_order show ?thesis
    by (simp add: ps_apply_spend_def ps_enforcement_coordinates_def Let_def)
qed

lemma cpk_ready_exact_request_reuses_checked_funding:
  assumes "ps_expected cpk_request = ps_cut cpk_state" "ps_payload_cut (ps_payload cpk_request) = ps_cut cpk_state"
    "map_of (ps_modes cpk_state)
      (ps_destination (ps_root (ps_scope (ps_payload cpk_request))),ps_asset (ps_root (ps_scope (ps_payload cpk_request)))) = Some cpk_mode"
    "ps_enforcement_coordinates True cpk_request cpk_mode cpk_state = Some (cpk_jurisdiction,cpk_basis)"
    "ps_granted cpk_request cpk_jurisdiction cpk_basis cpk_state" "ps_exact_root (ps_payload cpk_request) cpk_state"
    "ps_spend_funding (ps_scope (ps_payload cpk_request)) cpk_state = Some (cpk_next,cpk_position)"
  shows "ps_apply_spend True cpk_request cpk_state =
    (cpk_next,PS_Spend_Executed (ps_origin (ps_root (ps_scope (ps_payload cpk_request)))) cpk_position)"
  using assms by (simp add: ps_apply_spend_def Let_def)

definition cpk_projection where
  "cpk_projection cpk_verified cpk_request cpk_order cpk_state =
    (let cpk_payload = ps_payload cpk_request; cpk_scope_value = ps_scope cpk_payload; cpk_root = ps_root cpk_scope_value;
         cpk_access = ps_access cpk_verified cpk_request cpk_state;
         cpk_mode = map_of (ps_modes cpk_state) (ps_destination cpk_root,ps_asset cpk_root);
         cpk_ready = (case cpk_mode of None \<Rightarrow> False | Some cpk_live \<Rightarrow>
           ps_confiscation_ready cpk_order cpk_live cpk_state);
         cpk_coords = Option.bind cpk_mode (\<lambda>cpk_live. ps_enforcement_coordinates True cpk_request cpk_live cpk_state);
         cpk_granted = ps_granted cpk_request (ps_jurisdiction cpk_order) (ps_legal_basis cpk_order) cpk_state;
         (cpk_next,cpk_reply) = (if cpk_access then ps_apply_spend True cpk_request cpk_state else (cpk_state,PS_Spend_Rejected))
     in [pe_call cpk_request,
         map pe_bit [cpk_access,ps_expected cpk_request = ps_cut cpk_state,cpk_ready,cpk_coords \<noteq> None,
           cpk_granted,ps_exact_root cpk_payload cpk_state],
         pe_spend_reply cpk_reply,cpk_funding_words cpk_scope_value cpk_state,cpk_funding_words cpk_scope_value cpk_next])"

definition cpk_run where
  "cpk_run cpk_inputs =
    (case cpk_inputs of
      [[[cpk_epoch,cpk_revision,cpk_clock,cpk_now,cpk_expires,cpk_deployment,cpk_source,cpk_target,cpk_key_number,cpk_route,
         cpk_max_frame,cpk_packet_ok,cpk_approval_ok,cpk_token_ok]],
       [cpk_raw],[cpk_core_bytes],[cpk_preimage],[cpk_signature],[cpk_approval],[cpk_expected],[cpk_assets],
       cpk_sessions,cpk_modes,cpk_balances,cpk_funding,cpk_roots,cpk_freezes,cpk_seizures,cpk_grants] \<Rightarrow>
       Option.bind (decode_wire_packet cpk_raw) (\<lambda>cpk_packet.
         let cpk_core = packet_core cpk_packet; cpk_body = wire_operation_body cpk_core in
         if wire_version cpk_core \<noteq> 6 \<or> wire_purpose cpk_core \<noteq> 1 \<or> wire_message_family cpk_core \<noteq> Wire_Regulatory \<or>
            wire_opcode cpk_body \<noteq> 3 \<or> wire_deployment cpk_core \<noteq> cpk_deployment \<or>
            wire_source_domain cpk_core \<noteq> cpk_source \<or> wire_target_domain cpk_core \<noteq> cpk_target \<or>
            wire_key_number cpk_core \<noteq> cpk_key_number \<or> wire_authority_epoch cpk_core \<noteq> cpk_epoch \<or>
            wire_route_scope cpk_core \<noteq> cpk_route \<or> wire_signature_scheme cpk_core \<noteq> 1 \<or>
            cpk_now > cpk_expires \<or> length cpk_raw > cpk_max_frame \<or> encode_wire_core cpk_core \<noteq> cpk_core_bytes \<or>
            envelope_signing_bytes cpk_core \<noteq> cpk_preimage \<or> packet_signature cpk_packet \<noteq> cpk_signature
         then None else
          (case code_decode_spend cpk_core of Code_Spend_Ready cpk_native cpk_fields \<Rightarrow>
            Option.bind (spend_enforcement cpk_fields) (\<lambda>cpk_ef.
              let cpk_request = cpk_call cpk_native cpk_fields cpk_ef cpk_assets in
              if spend_kind_number cpk_fields \<noteq> 3 \<or> spend_proof cpk_fields \<noteq> Some cpk_approval \<or>
                 set cpk_assets \<noteq> enforcement_assets cpk_ef \<or> pe_call cpk_request \<noteq> cpk_expected \<or>
                 \<not> sl_width 3 cpk_sessions \<or> \<not> sl_width 3 cpk_modes \<or> \<not> list_all (\<lambda>cpk_row. cpk_row ! 2 \<le> 4) cpk_modes \<or>
                 \<not> sl_width 4 cpk_balances \<or> \<not> sl_width 6 cpk_funding \<or> \<not> sl_width 18 cpk_roots \<or>
                 \<not> sl_width 3 cpk_freezes \<or> \<not> sl_width 7 cpk_seizures \<or> \<not> sl_width 16 cpk_grants
              then None else
                (let cpk_state =
                  (sl_spend_state [cpk_epoch,cpk_revision,cpk_clock,1,1] cpk_sessions cpk_modes cpk_balances cpk_funding
                    cpk_roots [] [] [] [] cpk_freezes [] [] [] [] [])
                    \<lparr>ps_active_seizures := map cpk_active_entry cpk_seizures,
                      ps_spend_grants := map cpk_grant cpk_grants\<rparr>;
                   cpk_verified = (cpk_packet_ok = 1 \<and> cpk_approval_ok = 1 \<and> cpk_token_ok = 1)
                 in map_option (\<lambda>cpk_order. cpk_projection cpk_verified cpk_request cpk_order cpk_state)
                    (ps_enforcement cpk_request)))
          | _ \<Rightarrow> None))
     | _ \<Rightarrow> None)"

definition cpk_submit_integer :: "integer list list list \<Rightarrow> integer list list option" where
  "cpk_submit_integer cpk_inputs =
    Option.bind (sl_nats cpk_inputs) (\<lambda>cpk_nats.
      map_option (map (map integer_of_nat)) (cpk_run cpk_nats))"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms cpk_readiness_consumes_the_active_seizure_key_and_clock
    cpk_wrong_prior_refuses_at_the_same_cut cpk_ready_exact_request_reuses_checked_funding
    a_source_spend_has_the_exact_destination_and_two_u64_amounts ps_funding_body_preserves_regulation_and_exact_root_records})
  then () else error "Unexpected oracle in ConfiscateSpend prior-key checks"
\<close>

export_code cpk_submit_integer in SML module_name Confiscate_Prior_Key_ABI file_prefix "confiscate_prior_key_abi"

end
