theory Reference_Settlement_Effects_Code
  imports "Preemptive_Lock_Correctness.Reservation_Lifecycle"
begin

datatype native_terminal_path = Native_Confirm | Native_Reverse

record native_settlement_observation =
  native_origin_pending :: bool
  native_funded_destination :: nat
  native_root_lot :: nat
  native_available_source :: nat
  native_origin_owns_footprint :: bool

definition native_settle_observation where
  "native_settle_observation kind exact_terminal capacity binding before =
    (if \<not> native_origin_pending before \<or> \<not> exact_terminal \<or> \<not> capacity then (before, False)
     else case kind of
       Native_Confirm \<Rightarrow>
         (before\<lparr>native_origin_pending := False,
           native_funded_destination := native_funded_destination before + binding_amount binding,
           native_root_lot := binding_amount binding\<rparr>, True)
       | Native_Reverse \<Rightarrow>
         (before\<lparr>native_origin_pending := False,
           native_available_source := native_available_source before + binding_amount binding,
           native_origin_owns_footprint := False\<rparr>, True))"

context source_attestation
begin

definition native_settlement_state_related where
  "native_settlement_state_related binding native model \<longleftrightarrow>
    native_origin_pending native = (binding \<in> unresolved_source_obligations model) \<and>
    native_funded_destination native = destination_units model (destination_account_of binding) \<and>
    native_root_lot native = funded_units model (binding_key binding, destination_account_of binding) \<and>
    native_available_source native = source_units model (source_account_of binding) \<and>
    native_origin_owns_footprint native = (asset_owner model (binding_asset binding) = Some (binding_key binding))"

theorem first_native_credit_and_refund_match_the_actual_public_financial_events:
  assumes related: "native_settlement_state_related binding native model"
    and pending: "native_origin_pending native"
    and fresh_credit: "native_root_lot native = 0"
    and exact_record: "reservation_at model (binding_key binding) = Some reservation"
  shows "native_settlement_state_related binding
      (fst (native_settle_observation Native_Confirm True True binding native))
      (apply_reservation_event (Credit_Event binding) model)"
    "native_settlement_state_related binding
      (fst (native_settle_observation Native_Reverse True True binding native))
      (apply_reservation_event (Return_Event binding) model)"
proof -
  show "native_settlement_state_related binding
      (fst (native_settle_observation Native_Confirm True True binding native))
      (apply_reservation_event (Credit_Event binding) model)"
    using related pending fresh_credit
    by (simp add: native_settlement_state_related_def native_settle_observation_def
      unresolved_source_obligations_def record_credit_def)
  show "native_settlement_state_related binding
      (fst (native_settle_observation Native_Reverse True True binding native))
      (apply_reservation_event (Return_Event binding) model)"
    using related pending exact_record
    by (simp add: native_settlement_state_related_def native_settle_observation_def
      unresolved_source_obligations_def phase_at_def finish_reservation_def set_phase_def)
qed

end

lemma different_terminal_evidence_or_insufficient_capacity_has_no_native_effect:
  assumes "\<not> exact_terminal \<or> \<not> capacity"
  shows "native_settle_observation kind exact_terminal capacity binding native = (native, False)"
  using assms by (simp add: native_settle_observation_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.first_native_credit_and_refund_match_the_actual_public_financial_events
      different_terminal_evidence_or_insufficient_capacity_has_no_native_effect})
  then () else error "Unexpected oracle in native settlement effect correspondence"
\<close>

end
