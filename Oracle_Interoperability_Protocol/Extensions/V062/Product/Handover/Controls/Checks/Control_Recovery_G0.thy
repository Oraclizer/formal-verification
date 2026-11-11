theory Control_Recovery_G0
  imports "OIP_V062_Handover_Recovery_Control_Base.Control_Recovery_Base"
begin

lemma hc_recovery_g0:
  "hc_endorsement_allowed 8 3 \<and> \<not> hc_endorsement_allowed 7 2 \<and>
    hc_selected_reply 8 3 = Some Finality_Rejected \<and> hc_selected_reply 7 2 = None \<and>
    hc_selected_financial_state 8 3 = hc_selected_financial_state 7 2"
  using hc_successor_passes_but_the_live_former_worker_does_not_endorse
    hc_gate_and_refund_effect_are_distinct_observations by simp

thm_oracles hc_recovery_g0

ML \<open>
  if null (Thm_Deps.all_oracles @{thms hc_recovery_g0})
  then writeln "HANDOVER_RECOVERY_G0_ORACLES_EMPTY"
  else error "Unexpected oracle in recovery G0"
\<close>

end
