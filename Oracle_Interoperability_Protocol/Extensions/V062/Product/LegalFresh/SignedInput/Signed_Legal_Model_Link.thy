theory Signed_Legal_Model_Link
  imports "OIP_Protected_Spend_Export.Protected_Spend_Export"
    "OIP_Message_Code.Wire_Code_Typed_Call_Values"
begin

definition sl_u64 :: "integer \<Rightarrow> bool" where
  "sl_u64 sll_x \<longleftrightarrow> 0 \<le> sll_x \<and> sll_x < 18446744073709551616"

definition sl_nats :: "integer list list list \<Rightarrow> nat list list list option" where
  "sl_nats sll_x = (if list_all (list_all (list_all sl_u64)) sll_x
    then Some (map (map (map nat_of_integer)) sll_x) else None)"

definition sl_wire_abi :: "integer \<Rightarrow> integer list list \<Rightarrow> integer list option" where
  "sl_wire_abi sll_opcode sll_input =
    (case map (map nat_of_integer) sll_input of
      sll_bytes # sll_core_bytes # sll_preimage # sll_signature # sll_context # sll_words # sll_blobs \<Rightarrow>
        (if \<not> sl_u64 sll_opcode \<or> \<not> list_all (list_all sl_u64) sll_input then None
         else Option.bind (decode_wire_packet sll_bytes) (\<lambda>sll_packet.
           let sll_core = packet_core sll_packet; sll_body = wire_operation_body sll_core in
           if wire_version sll_core = 6 \<and> wire_message_family sll_core = Wire_Regulatory \<and>
              wire_opcode sll_body = nat_of_integer sll_opcode \<and> wire_deadline sll_body = Deadline_Absent \<and>
              [wire_version sll_core,wire_deployment sll_core,wire_source_domain sll_core,wire_target_domain sll_core,
                wire_principal sll_core,wire_authority_epoch sll_core] @ wire_uuid sll_core = sll_context \<and>
              wire_words sll_body = sll_words \<and> wire_blobs sll_body = sll_blobs \<and>
              encode_wire_core sll_core = sll_core_bytes \<and> envelope_signing_bytes sll_core = sll_preimage \<and>
              packet_signature sll_packet = sll_signature
           then map_option (map integer_of_nat)
             (if sll_opcode = 3 then code_typed_spend_ir sll_core else code_typed_legal_ir sll_core)
           else None))
    | _ \<Rightarrow> None)"

definition sl_freeze_admission where
  "sl_freeze_admission sll_verified sll_granted sll_officer sll_basis sll_scoped sll_stage sll_epoch_current sll_no_issued sll_exact sll_mode =
    (if \<not> sll_verified \<or> \<not> sll_officer \<or> sll_basis = (0::nat) \<or> \<not> sll_scoped \<or> \<not> sll_granted
      then Legal_Refuse Invalid_Legal_Authority
     else if (case sll_stage of Legal_Source_Emission \<Rightarrow> \<not> sll_epoch_current \<or> (\<not> sll_no_issued \<and> \<not> sll_exact)
                         | Legal_Receiving_Commit \<Rightarrow> \<not> sll_exact)
      then Legal_Refuse Conflicting_Legal_Order
     else if sll_mode = Some ACTIVE then Legal_Admit else Legal_Refuse Invalid_Legal_State)"

lemma sl_freeze_admission_is_the_canonical_projection:
  assumes "legal_action sll_order = FREEZE"
  shows "sl_freeze_admission (sll_order_verified sll_stage sll_entry sll_who sll_order)
    (sll_grant sll_stage sll_entry sll_who (Legal_Admission.legal_jurisdiction sll_order) (legal_asset sll_order)
      (legal_action sll_order) (cut_authority_epoch (legal_current_cut sll_s)))
    (Legal_Admission.legal_officer sll_order = sll_who) (Legal_Admission.legal_basis sll_order)
    (legal_asset sll_order \<in> Legal_Admission.legal_scope sll_order) sll_stage
    (Legal_Admission.legal_issuance_epoch sll_order = cut_authority_epoch (legal_current_cut sll_s))
    (issued_legal_orders sll_s (legal_origin sll_order) = None)
    (issued_legal_orders sll_s (legal_origin sll_order) = Some sll_order)
    (legal_current_state sll_s (fst (legal_origin sll_order)) (legal_asset sll_order)) =
    legal_admission_at_cut sll_grant sll_order_verified sll_stage sll_entry sll_who sll_order sll_s"
  using assms
  by (cases sll_stage; cases "issued_legal_orders sll_s (legal_origin sll_order)")
    (simp_all add: sl_freeze_admission_def legal_admission_at_cut_def legal_state_gate_def Let_def)

fun sl_admission_word where
  "sl_admission_word Legal_Admit = (0::nat)"
| "sl_admission_word (Legal_Refuse Invalid_Legal_Authority) = 1"
| "sl_admission_word (Legal_Refuse Conflicting_Legal_Order) = 2"
| "sl_admission_word (Legal_Refuse Invalid_Legal_State) = 3"
| "sl_admission_word (Legal_Refuse _) = 4"

definition sl_mode :: "nat \<Rightarrow> reg_state" where
  "sl_mode sll_n = [ACTIVE,RESTRICTED,FROZEN,SEIZED,CONFISCATED] ! sll_n"

definition sl_modes where
  "sl_modes sll_rows = map (\<lambda>sll_r. ((sll_r ! 0,sll_r ! 1),sl_mode (sll_r ! 2))) sll_rows"

definition sl_legal_rows where
  "sl_legal_rows sll_header sll_order sll_payload_binding sll_issued sll_grants sll_modes sll_sessions sll_enrollments sll_occupied sll_origins =
    (case sll_header of
       [sll_stage_word,sll_route,sll_actor,sll_namespace,sll_sequence,sll_expected_epoch,sll_expected_revision,sll_message,sll_caller,sll_session,
        sll_payload_epoch,sll_payload_revision,sll_origin_epoch,sll_payload_action,sll_up,sll_available,sll_verified,sll_epoch,sll_revision,sll_clock] \<Rightarrow>
       (case sll_order of sll_source # sll_event # sll_asset # sll_owner # sll_target # sll_recipient # sll_amount # sll_action # sll_officer #
           jurisdiction # sll_basis # sll_issuance # sll_prior_flag # sll_prior_source # sll_prior_event # sll_appeal_flag #
           sll_appeal # sll_destination_flag # sll_destination # sll_scope \<Rightarrow>
         if (sll_stage_word = 1 \<or> sll_stage_word = 2) \<and> sll_action = 1 then
           let sll_stage = (if sll_stage_word = 1 then Legal_Source_Emission else Legal_Receiving_Commit);
               sll_mode_rows = sl_modes sll_modes;
               sll_source_mode = map_of sll_mode_rows (sll_source,sll_asset);
               sll_receiver_mode = map_of sll_mode_rows (sll_target,sll_asset);
               sll_granted = [sll_stage_word,sll_route,sll_actor,jurisdiction,sll_basis,sll_asset,sll_action,sll_epoch] \<in> set sll_grants;
               sll_no_issued = sll_issued = [];
               sll_exact = \<not> sll_no_issued \<and> drop 5 sll_issued = sll_order;
               sll_admitted = sl_freeze_admission (sll_verified = 1) sll_granted (sll_officer = sll_actor) sll_basis
                 (sll_asset \<in> set sll_scope) sll_stage (sll_issuance = sll_epoch) sll_no_issued sll_exact sll_source_mode;
               sll_paired = sll_source_mode \<noteq> None \<and> sll_source_mode = sll_receiver_mode;
               sll_enrolled = [sll_asset,sll_source,sll_target] \<in> set sll_enrollments;
               sll_bound = sll_payload_binding = take 7 sll_order \<and> sll_payload_action = sll_action \<and> sll_origin_epoch = sll_issuance
                 \<and> (sll_destination_flag = 0 \<or> sll_destination = sll_recipient);
               sll_cut = (sll_expected_epoch,sll_expected_revision) = (sll_epoch,sll_revision)
                 \<and> (sll_payload_epoch,sll_payload_revision) = (sll_epoch,sll_revision);
               sll_access = sll_namespace = sll_actor \<and> sll_caller = sll_actor \<and> [sll_session,sll_actor,sll_epoch] \<in> set sll_sessions;
               sll_fresh = [sll_namespace,sll_sequence] \<notin> set sll_occupied \<and> [sll_source,sll_event] \<notin> set sll_origins;
               sll_effect = (if sll_stage = Legal_Receiving_Commit \<and> sll_admitted = Legal_Admit \<and> sll_paired
                 then Option.bind sll_source_mode (\<lambda>sll_mode. reg_transition sll_mode FREEZE) else None)
           in Some ([[0,sll_stage_word,sll_route,sll_actor,sll_namespace,sll_sequence,sll_message,sll_epoch,sll_revision,sll_clock],
             [1,sl_admission_word sll_admitted,pe_bit sll_granted,pe_bit sll_no_issued,pe_bit sll_exact,pe_bit sll_paired],
             [2,sll_up,sll_available,sll_verified,pe_bit sll_access,pe_bit sll_enrolled,pe_bit sll_bound,pe_bit sll_cut,pe_bit sll_fresh],
             [3] @ pe_optional (map_option pe_mode sll_source_mode) @ pe_optional (map_option pe_mode sll_receiver_mode),
             [4] @ pe_optional (map_option pe_mode sll_effect), [5] @ sll_order, [6] @ sll_issued])
         else None
       | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)"

definition sl_legal_abi :: "integer list list list \<Rightarrow> integer list list option" where
  "sl_legal_abi sll_input =
    (case sl_nats sll_input of Some [[sll_header],[sll_order],[sll_payload],[sll_issued],sll_grants,sll_modes,sll_sessions,sll_enrollments,sll_occupied,sll_origins] \<Rightarrow>
       if list_all (\<lambda>sll_r. length sll_r = 3 \<and> sll_r ! 2 \<le> 4) sll_modes then
         map_option (map (map integer_of_nat))
           (sl_legal_rows sll_header sll_order sll_payload sll_issued sll_grants sll_modes sll_sessions sll_enrollments sll_occupied sll_origins)
       else None
     | _ \<Rightarrow> None)"

definition sl_binding where
  "sl_binding sll_r = \<lparr>ps_origin = (sll_r ! 0,sll_r ! 1),ps_asset = sll_r ! 2,ps_owner = sll_r ! 3,
    ps_destination = sll_r ! 4,ps_receiver = sll_r ! 5,ps_root_amount = sll_r ! 6\<rparr>"

definition sl_scope where
  "sl_scope sll_r = \<lparr>ps_root = sl_binding sll_r,ps_sender = sll_r ! 7,ps_recipient = sll_r ! 8,
    ps_amount = sll_r ! 9,ps_kind = PS_Recover\<rparr>"

definition sl_cut where
  "sl_cut sll_epoch sll_revision = \<lparr>cut_authority_epoch = sll_epoch,cut_revision = sll_revision\<rparr>"

definition sl_optional where
  "sl_optional sll_flag sll_word = (if sll_flag = (0::nat) then None else Some sll_word)"

definition sl_terminal where
  "sl_terminal sll_flag = (if sll_flag = (1::nat) then Confirmed_Decision else Reversed_Decision)"

definition sl_spend_call where
  "sl_spend_call sll_header sll_scope sll_order_scope sll_order =
    \<lparr>ps_route = PS_Normal,ps_actor = sll_header ! 1,ps_call_id = (sll_header ! 2,sll_header ! 3),
      ps_expected = sl_cut (sll_header ! 4) (sll_header ! 5),
      ps_payload = \<lparr>ps_message = sll_header ! 6,ps_caller = sll_header ! 7,ps_session = sll_header ! 8,
        ps_payload_cut = sl_cut (sll_header ! 9) (sll_header ! 10),ps_origin_epoch = sll_header ! 11,
        ps_reference = sll_header ! 12,ps_scope = sl_scope sll_scope\<rparr>,
      ps_enforcement = Some \<lparr>ps_order_scope = sl_scope sll_order_scope,ps_officer = sll_order ! 0,
        ps_jurisdiction = sll_order ! 1,ps_legal_basis = sll_order ! 2,ps_assets = drop 8 sll_order,
        ps_prior_seizure = sl_optional (sll_order ! 3) (sll_order ! 4,sll_order ! 5),
        ps_appeal_deadline = sl_optional (sll_order ! 6) (sll_order ! 7)\<rparr>\<rparr>"

definition sl_root_entry where
  "sl_root_entry sll_r =
    ((sll_r ! 0,sll_r ! 1),\<lparr>ps_slot_binding = sl_binding (drop 2 sll_r),ps_slot_epoch = sll_r ! 9,
      ps_decision_kind = map_option sl_terminal (sl_optional (sll_r ! 10) (sll_r ! 11)),
      ps_decision_position = sl_optional (sll_r ! 12) (sll_r ! 13),
      ps_settled = sl_optional (sll_r ! 14) (sll_r ! 15),ps_published = sl_optional (sll_r ! 16) (sll_r ! 17)\<rparr>)"

definition sl_reservation_entry where
  "sl_reservation_entry sll_r =
    ((sll_r ! 0,sll_r ! 1),\<lparr>ps_reserved = sl_binding (drop 2 sll_r),ps_holder = sll_r ! 9,ps_generation = sll_r ! 10,
       ps_expires = sll_r ! 11,ps_phase = sll_r ! 12,ps_pending = sll_r ! 13\<rparr>)"

definition sl_event_entry where
  "sl_event_entry sll_r =
    ((sll_r ! 0,sll_r ! 1),\<lparr>ps_legal_binding = sl_binding (drop 2 sll_r),ps_legal_epoch = sll_r ! 9,
       ps_legal_officer = sll_r ! 10,ps_legal_jurisdiction = sll_r ! 11,ps_legal_basis_value = sll_r ! 12,
       ps_emitted_position = sll_r ! 13,ps_applied_position = sl_optional (sll_r ! 14) (sll_r ! 15),
       ps_legal_published = sl_optional (sll_r ! 16) (sll_r ! 17)\<rparr>)"

definition sl_spend_state where
  "sl_spend_state sll_header sll_sessions sll_modes sll_balances sll_funding sll_roots sll_reservations sll_active sll_evidence sll_events sll_freezes
      sll_grants sll_legal sll_ordinary sll_syncs sll_journal =
    \<lparr>ps_epoch = sll_header ! 0,ps_revision = sll_header ! 1,ps_clock = sll_header ! 2,
      ps_up = (sll_header ! 3 = 1),ps_available = (sll_header ! 4 = 1),
      ps_sessions = map (\<lambda>sll_r. (sll_r ! 0,sll_r ! 1,sll_r ! 2)) sll_sessions,ps_modes = sl_modes sll_modes,
      ps_balances = map (\<lambda>sll_r. ((sll_r ! 0,sll_r ! 1,sll_r ! 2),sll_r ! 3)) sll_balances,
      ps_funding = map (\<lambda>sll_r. (((sll_r ! 0,sll_r ! 1),(sll_r ! 2,sll_r ! 3,sll_r ! 4)),sll_r ! 5)) sll_funding,
      ps_roots = map sl_root_entry sll_roots,ps_reservations = map sl_reservation_entry sll_reservations,
      ps_active = map (\<lambda>sll_r. (sll_r ! 0,sll_r ! 1,sll_r ! 2)) sll_active,
      ps_evidence = map (\<lambda>sll_r. (sll_r ! 0,sl_binding (drop 2 sll_r),sl_terminal (sll_r ! 1))) sll_evidence,
      ps_legal_events = map sl_event_entry sll_events,ps_active_freezes = map (\<lambda>sll_r. (sll_r ! 0,sll_r ! 1,sll_r ! 2)) sll_freezes,
      ps_active_seizures = [],
      ps_spend_grants = map (\<lambda>sll_r. \<lparr>ps_grant_route = PS_Normal,ps_grant_actor = sll_r ! 1,ps_grant_epoch = sll_r ! 2,
        ps_grant_scope = sl_scope (drop 3 sll_r),ps_grant_jurisdiction = sll_r ! 14,ps_grant_basis = sll_r ! 15\<rparr>) sll_grants,
      ps_spend_receipts = [],ps_legal_ids = map (\<lambda>sll_r. (sll_r ! 0,sll_r ! 1)) sll_legal,
      ps_ordinary_ids = map (\<lambda>sll_r. (sll_r ! 0,sll_r ! 1)) sll_ordinary,ps_sync_ids = map (\<lambda>sll_r. (sll_r ! 0,sll_r ! 1)) sll_syncs,
      ps_journal = map (\<lambda>sll_r. ((sll_r ! 0,sll_r ! 1),sll_r ! 2,sll_r ! 3)) sll_journal\<rparr>"

definition sl_spend_projection where
  "sl_spend_projection sll_role sll_state =
    [[10,sll_role,ps_epoch sll_state,ps_revision sll_state,ps_clock sll_state,pe_bit (ps_up sll_state),pe_bit (ps_available sll_state)]] @
    map (\<lambda>((sll_endpoint,sll_asset),sll_mode). [11,sll_role,sll_endpoint,sll_asset,pe_mode sll_mode]) (ps_modes sll_state) @
    map (\<lambda>((sll_endpoint,sll_asset,sll_holder),sll_value). [12,sll_role,sll_endpoint,sll_asset,sll_holder,sll_value]) (ps_balances sll_state) @
    map (\<lambda>(((sll_source,sll_event),(sll_endpoint,sll_asset,sll_holder)),sll_value).
      [13,sll_role,sll_source,sll_event,sll_endpoint,sll_asset,sll_holder,sll_value]) (ps_funding sll_state) @
    map (\<lambda>((sll_source,sll_event),sll_slot). [14,sll_role,sll_source,sll_event] @ pe_binding (ps_slot_binding sll_slot) @
      [ps_slot_epoch sll_slot] @ pe_optional (map_option (\<lambda>sll_k. if sll_k = Confirmed_Decision then 1 else 2)
        (ps_decision_kind sll_slot)) @ pe_optional (ps_decision_position sll_slot) @
      pe_optional (ps_settled sll_slot) @ pe_optional (ps_published sll_slot)) (ps_roots sll_state) @
    map (\<lambda>((sll_source,sll_event),sll_slot). [15,sll_role,sll_source,sll_event] @ pe_binding (ps_reserved sll_slot) @
      [ps_holder sll_slot,ps_generation sll_slot,ps_expires sll_slot,ps_phase sll_slot,ps_pending sll_slot]) (ps_reservations sll_state) @
    map (\<lambda>((sll_namespace,sll_sequence),(sll_payload,sll_enforcement,sll_reply)). [21,sll_role,sll_namespace,sll_sequence] @
      pe_payload sll_payload @ pe_enforcement sll_enforcement @ pe_spend_reply sll_reply) (ps_spend_receipts sll_state) @
    map (\<lambda>((sll_namespace,sll_sequence),sll_target,sll_position). [25,sll_role,sll_namespace,sll_sequence,sll_target,sll_position]) (ps_journal sll_state)"

definition sl_spend_result where
  "sl_spend_result sll_verified sll_call sll_state =
    (let (sll_next,sll_reply) = ps_submit_spend True sll_verified sll_call sll_state in
       [[0] @ pe_spend_reply sll_reply, [1] @ pe_call sll_call,
        [2,pe_bit (ps_access sll_verified sll_call sll_state),pe_bit (ps_exact_root (ps_payload sll_call) sll_state)]] @
       sl_spend_projection 0 sll_state @ sl_spend_projection 1 sll_next)"

definition sl_width where
  "sl_width sll_size sll_rows \<longleftrightarrow> list_all (\<lambda>sll_r. length sll_r = sll_size) sll_rows"

definition sl_spend_abi :: "integer list list list \<Rightarrow> integer list list option" where
  "sl_spend_abi sll_input =
    (case sl_nats sll_input of
      Some [[sll_call],[sll_scope],[sll_order_scope],[sll_order],[sll_header],sll_sessions,sll_modes,sll_balances,sll_funding,sll_roots,sll_reservations,
            sll_active,sll_evidence,sll_events,sll_freezes,sll_grants,sll_legal,sll_ordinary,sll_syncs,sll_journal] \<Rightarrow>
        if length sll_call = 14 \<and> sll_call ! 0 = 0 \<and> length sll_header = 5 \<and>
           length sll_scope = 11 \<and> sll_scope ! 10 = 1 \<and> length sll_order_scope = 11 \<and> sll_order_scope ! 10 = 1 \<and>
           8 \<le> length sll_order \<and> sl_width 3 sll_sessions \<and> sl_width 3 sll_modes \<and> list_all (\<lambda>sll_r. sll_r ! 2 \<le> 4) sll_modes \<and>
           sl_width 4 sll_balances \<and> sl_width 6 sll_funding \<and> sl_width 18 sll_roots \<and> sl_width 14 sll_reservations \<and>
           sl_width 3 sll_active \<and> sl_width 9 sll_evidence \<and> sl_width 18 sll_events \<and> sl_width 3 sll_freezes \<and>
           sl_width 16 sll_grants \<and> list_all (\<lambda>sll_r. sll_r ! 0 = 0 \<and> sll_r ! 13 = 1) sll_grants \<and>
           sl_width 2 sll_legal \<and> sl_width 2 sll_ordinary \<and> sl_width 2 sll_syncs \<and> sl_width 4 sll_journal
        then Some (map (map integer_of_nat) (sl_spend_result (sll_call ! 13 = 1)
          (sl_spend_call sll_call sll_scope sll_order_scope sll_order)
          (sl_spend_state sll_header sll_sessions sll_modes sll_balances sll_funding sll_roots sll_reservations sll_active sll_evidence sll_events sll_freezes
            sll_grants sll_legal sll_ordinary sll_syncs sll_journal)))
        else None
    | _ \<Rightarrow> None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sl_freeze_admission_is_the_canonical_projection
      ps_lawful_recovery_consumes_the_same_current_root_and_funding
      ps_funding_body_preserves_regulation_and_exact_root_records})
  then () else error "Unexpected oracle in signed legal input link"
\<close>

export_code sl_wire_abi sl_legal_abi sl_spend_abi in SML
  module_name OIP_Signed_Legal_Link file_prefix "oip_signed_legal_link"

end
