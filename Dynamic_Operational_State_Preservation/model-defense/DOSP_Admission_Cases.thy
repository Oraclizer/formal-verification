theory DOSP_Admission_Cases
  imports DOSP_Joint_Metering_Cases
begin

interpretation reversed_dosp: integrated_dosp_authority example_roster example_faulty example_bound
  example_threshold sample_verifies sample_signed sample_truth sample_source coupling_policy "{(12,4)}" "(22,7,3)"
  by unfold_locales

abbreviation reversed_authority where
  "reversed_authority \<equiv>
    (let a = with_finality_core (finality_sample_certified 22) joined_initial
     in with_operational_state ((current_operational a)\<lparr>registered_asset := 22\<rparr>) a)"

definition reversed_cycle :: cycle_request where
  "reversed_cycle = \<lparr>cycle_attempt_id = (22,0), cycle_session_id = (22,7,3), cycle_binding_id = prod_encode (0,22),
    cycle_ticket = \<lparr>ticket_asset = 22, ticket_initiator = 0, ticket_metadata = coupling_ticket\<rparr>,
    cycle_source = 0, cycle_target = 2, cycle_value = binding_amount (sample_binding 22)\<rparr>"

abbreviation reversed_product where
  "reversed_product recovery \<equiv> \<lparr>source_lifecycle = episode_initial\<lparr>lifecycle_session := (22,7,3),
      lifecycle_cutover := degree_state (current_operational reversed_authority),
      lifecycle_registry := authority_registry reversed_authority,
      lifecycle_phase := Bound_Cycle reversed_cycle, lifecycle_tariff := 3,
      cycle_custody := Native_Debit_Pending (0,22)\<rparr>,
    source_consensus = reversed_authority, source_recovery = recovery, observed_divergence_work = {}\<rparr>"

theorem the_actual_native_refund_releases_a_bound_debit_without_a_local_write:
  "\<exists>q. reversed_dosp.release_live_reversed_debit (reversed_product recovery) 0 (sample_request 22) 0 [] True q \<and>
    cycle_custody (source_lifecycle q) = Local_Cells_Only \<and> lifecycle_phase (source_lifecycle q) = Idle_Cycle \<and>
    lifecycle_invoice (source_lifecycle q) = lifecycle_invoice (source_lifecycle (reversed_product recovery)) \<and>
    lifecycle_cutover (source_lifecycle q) = lifecycle_cutover (source_lifecycle (reversed_product recovery))"
proof -
  let ?p = "reversed_product recovery"
  let ?c = "finality_sample_certified 22"
  let ?raw = "sample.execute_finality_client (Client_Protocol 0 0 (Return_Intent (sample_request 22) 0 [])) ?c"
  let ?q = "?p\<lparr>source_lifecycle := (source_lifecycle ?p)\<lparr>cycle_custody := Local_Cells_Only, lifecycle_phase := Idle_Cycle\<rparr>,
    source_consensus := with_finality_core (fst ?raw) reversed_authority\<rparr>"
  have stored: "core_records ?c (0,22) = Some
    \<lparr>terminal_binding = sample_binding 22, terminal_kind = Reversed_Decision, terminal_evidence = [sample_certificate 22]\<rparr>"
    using terminal_certificate_publishes_the_actual_parent_evidence[of 22] actual_source_supports_terminal_record_creation[of 22]
    by auto
  have reference: "exact_record_reference ?c 0 (request_binding (sample_request 22)) Reversed_Decision (request_certificate (sample_request 22))"
    by (simp add: exact_record_reference_def record_reference_def sample_request_def sample_binding_def example_binding_def stored)
  have core: "credit_core (current_operational reversed_authority) = ?c"
    by (simp add: with_operational_state_def with_finality_core_def Let_def)
  have asset: "registered_asset (current_operational reversed_authority) = 22"
    by (simp add: with_operational_state_def Let_def)
  have key: "binding_key (request_binding (sample_request 22)) = (0,22)"
    "binding_asset (request_binding (sample_request 22)) = 22"
    by (simp_all add: sample_request_def sample_binding_def example_binding_def)
  have prepared: "names_prepared_binding (source_lifecycle ?p) (request_binding (sample_request 22))"
    by (auto simp: names_prepared_binding_def reversed_cycle_def request_flow_def sample_request_def sample_binding_def example_binding_def)
  have refunded:
    "snd (sample.execute_finality_client (Client_Protocol (fst (binding_key (request_binding (sample_request 22)))) 0
        (Return_Intent (sample_request 22) 0 [])) (credit_core (current_operational reversed_authority))) =
      Protocol_Response Reservation_Released"
    by (simp only: key(1) fst_conv core normal_reverse_returns_the_recorded_source)
  have allowed: "reversed_dosp.release_live_reversed_debit ?p 0 (sample_request 22) 0 [] True ?q"
    unfolding reversed_dosp.release_live_reversed_debit_def
    using refunded prepared core reference key asset
    by (simp add: Let_def)
  show ?thesis using allowed by (intro exI[of _ ?q]) simp
qed

end
