theory Control_Recovery_Export
  imports "OIP_V062_Handover_Recovery_Finite_Model.Control_Recovery_Finite"
    "HOL-Library.Code_Target_Nat"
begin

definition hce_gate_without_controller :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "hce_gate_without_controller m_who m_session \<longleftrightarrow>
    (\<exists>m_identity m_proof. hc_typed_authenticate (endorsement_token (hc_endorsement m_who m_session)) = Some m_identity \<and>
      m_proof = endorsement_session (hc_endorsement m_who m_session) \<and>
      active_identity identity_case_directory m_identity m_proof hc_post_source \<and>
      hc_typed_policy m_identity (0::nat) (envelope_asset (payload_envelope hc_refund_payload)) Recover_Claim (proof_epoch m_proof) \<and>
      hc_typed_endorse m_identity m_proof (0::nat) (0,17) ((7,10)::client_call_id) hc_refund_payload)"

lemma hce_finite_removal_deletes_only_current_controller:
  "hcf_active m_who m_session = hce_gate_without_controller m_who m_session"
  by (simp add: hcf_active_is_the_actual_identity_gate hce_gate_without_controller_def
      hc_endorsement_def hc_typed_authenticate_def hc_typed_policy_def hc_typed_endorse_def)

lemma hce_former_removal_reaches_the_refund_but_does_not_refund:
  "\<not> hc_endorsement_allowed 7 2"
  "hce_gate_without_controller 7 2"
  "hcf_refund_reply = Some Finality_Rejected"
  using hc_successor_passes_but_the_live_former_worker_does_not_endorse(2)
    hc_post_owner_and_live_sessions(3)
  by (simp_all add: hce_finite_removal_deletes_only_current_controller[symmetric]
      hcf_active_is_the_actual_identity_gate hcf_refund_observation_is_the_actual_refused_consumer
      hc_actual_refund_consumer_rejects_the_missing_record_without_financial_effect)

lemma hce_selected_financial_state_is_always_the_checked_frame:
  "hc_selected_financial_state m_who m_session = authoritative_reservation_state hf_source"
  by (simp add: hc_selected_financial_state_def
      hc_actual_refund_consumer_rejects_the_missing_record_without_financial_effect
      hc_post_financial_state_is_the_same_checked_pending_state)

definition hce_removed_financial_state :: "nat \<Rightarrow> nat \<Rightarrow> reservation_state" where
  "hce_removed_financial_state m_who m_session =
    (if hce_gate_without_controller m_who m_session then machine_state (core_parent (fst hc_refund_core_result))
     else authoritative_reservation_state hc_post_source)"

lemma hce_removed_financial_state_is_also_the_checked_frame:
  "hce_removed_financial_state m_who m_session = authoritative_reservation_state hf_source"
  by (simp add: hce_removed_financial_state_def
      hc_actual_refund_consumer_rejects_the_missing_record_without_financial_effect
      hc_post_financial_state_is_the_same_checked_pending_state)

lemma hce_finite_financial_projection_is_the_selected_actual_state:
  "rust_handover_ledger hcf_post_image =
    hfp_project_ledger (7, hc_selected_financial_state m_who m_session)"
  by (simp add: hcf_post_image_def hfp_run_is_related_to_the_checked_typed_execution
      hfp_project_image_def hg_normal_native_owner_sessions_epoch_and_immutable_ledger(8)
      hce_selected_financial_state_is_always_the_checked_frame)

definition hce_flag :: "bool \<Rightarrow> nat" where
  "hce_flag m_flag = (if m_flag then 1 else 0)"

fun hce_reply_tag :: "finality_reply option \<Rightarrow> nat" where
  "hce_reply_tag None = 0"
| "hce_reply_tag (Some Finality_Rejected) = 1"
| "hce_reply_tag (Some m_other) = 2"

fun hce_phase_tag :: "reservation_phase \<Rightarrow> nat" where
  "hce_phase_tag Reservation_Held = 1"
| "hce_phase_tag Source_Submitted = 2"
| "hce_phase_tag Source_Pending = 3"
| "hce_phase_tag Source_Confirmed = 4"
| "hce_phase_tag Source_Returned = 5"
| "hce_phase_tag Source_Cancelled = 6"

definition hce_financial_row :: "hfp_ledger \<Rightarrow> nat list" where
  "hce_financial_row m_store = [fp_pending m_store,fp_source_units m_store,fp_destination_units m_store]"

definition hce_binding_row :: "hfp_ledger \<Rightarrow> nat list" where
  "hce_binding_row m_store =
    (let m_binding = fp_binding m_store in
      [fst (binding_key m_binding),snd (binding_key m_binding),binding_asset m_binding,fp_original_owner m_store,
       binding_destination m_binding,binding_recipient m_binding,binding_amount m_binding,
       hce_phase_tag (fp_phase m_store),fp_worker m_store,fp_generation m_store,fp_deadline m_store] @ fp_footprint m_store)"

definition hce_observe :: "bool \<Rightarrow> nat \<Rightarrow> nat list list" where
  "hce_observe m_remove_controller m_session =
    (let m_who = (if m_session = 3 then 8 else 7);
         m_active = hcf_active m_who m_session;
         m_admitted = (if m_remove_controller then m_active else hcf_endorsement_allowed m_who m_session);
         m_reply = (if m_admitted then hcf_refund_reply else None);
         m_store = rust_handover_ledger hcf_post_image;
         m_exact = (hcf_record_reference hcf_terminal_rows 0 (request_binding hc_refund_request) Reversed_Decision =
           Some (request_certificate hc_refund_request))
     in [[1,1,2,m_who,m_session,10,hce_flag m_active,
          hce_flag (hcf_controller \<noteq> None),(case hcf_controller of None \<Rightarrow> 0 | Some m_owner \<Rightarrow> m_owner),
          hce_flag m_admitted,hce_flag m_admitted,hce_reply_tag m_reply],
         [7,2,10,hce_flag (hcf_active 7 2)],
         [hce_flag (map_of hcf_terminal_rows (0,17) \<noteq> None),hce_flag m_exact,0],
         hce_binding_row m_store,hce_financial_row m_store,hce_financial_row m_store])"

definition hce_u64 :: "integer \<Rightarrow> bool" where
  "hce_u64 m_word \<longleftrightarrow> 0 \<le> m_word \<and> m_word < 18446744073709551616"

fun hce_observe_integer :: "bool \<Rightarrow> integer list \<Rightarrow> integer list list" where
  "hce_observe_integer m_remove [m_source,m_receiver,m_asset,m_event,m_former,m_successor,m_worker,m_session,m_epoch,m_amount] =
    (if list_all hce_u64 [m_source,m_receiver,m_asset,m_event,m_former,m_successor,m_worker,m_session,m_epoch,m_amount] \<and>
      [m_source,m_receiver,m_asset,m_event,m_former,m_successor,m_worker,m_epoch,m_amount] = [0,2,17,17,7,8,7,10,5] \<and>
      (m_session = 2 \<or> m_session = 3)
     then map (map integer_of_nat) (hce_observe m_remove (nat_of_integer m_session)) else [[0]])"
| "hce_observe_integer m_remove m_other_input = [[0]]"

thm_oracles hce_finite_removal_deletes_only_current_controller
  hce_former_removal_reaches_the_refund_but_does_not_refund
  hce_selected_financial_state_is_always_the_checked_frame
  hce_removed_financial_state_is_also_the_checked_frame
  hce_finite_financial_projection_is_the_selected_actual_state

ML \<open>
  if null (Thm_Deps.all_oracles @{thms hce_finite_removal_deletes_only_current_controller
      hce_former_removal_reaches_the_refund_but_does_not_refund
      hce_selected_financial_state_is_always_the_checked_frame
      hce_removed_financial_state_is_also_the_checked_frame
      hce_finite_financial_projection_is_the_selected_actual_state})
  then writeln "HANDOVER_RECOVERY_EXPORT_ORACLES_EMPTY"
  else error "Unexpected oracle in recovery export"
\<close>

export_code hce_observe_integer
  in SML module_name OIP_Handover_Recovery_ABI file_prefix "oip_handover_recovery_abi"

end
