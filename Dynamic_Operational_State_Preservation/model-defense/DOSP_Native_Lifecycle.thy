theory DOSP_Native_Lifecycle
  imports DOSP_Billing_Public
begin

definition cycle_names_native_binding where
  "cycle_names_native_binding cycle r \<longleftrightarrow>
    (let b = request_binding r in
      fst (cycle_session_id cycle) = binding_asset b \<and>
      cycle_binding_id cycle = prod_encode (binding_key b) \<and>
      request_flow cycle = transfer_commit b)"

definition native_source_pending where
  "native_source_pending native r \<longleftrightarrow>
    (let b = request_binding r in
      \<exists>res. reservation_at (machine_state (core_parent (credit_core native))) (binding_key b) = Some res \<and>
        reservation_binding res = b \<and> reservation_phase res = Source_Pending)"

definition bind_native_custody where
  "bind_native_custody s native r =
    (if native_source_pending native r then s\<lparr>cycle_custody := Native_Debit_Pending (binding_key (request_binding r))\<rparr>
     else s)"

lemma actual_native_pending_cannot_be_discharged_by_local_restoration:
  assumes "native_source_pending native r"
  shows "lifecycle_step policy grants versions confirmed verified locks (bind_native_custody s native r)
    (Restore_Cycle restoration) Restoration_Refused (bind_native_custody s native r)"
proof -
  have pending: "cycle_custody (bind_native_custody s native r) = Native_Debit_Pending (binding_key (request_binding r))"
    using assms by (simp add: bind_native_custody_def)
  show ?thesis by (rule bare_retry_and_restore_cannot_clear_a_pending_native_debit(1)[OF pending])
qed

definition guarded_native_promotion where
  "guarded_native_promotion policy grants versions s native epoch version reply t native_after \<longleftrightarrow>
    (if fst (lifecycle_session s) = registered_asset native \<and>
        degree_state native = lifecycle_cutover s \<and> lifecycle_promotable (promotion_locks_clear policy native) s
        \<and> versions version \<noteq> None
     then promote_settled_asset policy grants epoch version native = (native_after,reply) \<and>
          t = (if reply = transition_result.Accepted Promotion_Finalized then finish_promotion s (degree_state native_after) version else s)
     else reply = transition_result.Rejected Ineligible_Promotion \<and> t = s \<and> native_after = native)"

lemma guarded_promotion_blocks_a_bound_phase_before_the_native_step:
  assumes "lifecycle_phase s = Bound_Cycle request"
  shows "guarded_native_promotion policy grants versions s native epoch version reply t native_after \<longleftrightarrow>
    reply = transition_result.Rejected Ineligible_Promotion \<and> t = s \<and> native_after = native"
  using assms by (simp add: guarded_native_promotion_def lifecycle_promotable_def)

lemma guarded_promotion_cannot_change_another_registry_asset:
  assumes "fst (lifecycle_session s) \<noteq> registered_asset native"
  shows "guarded_native_promotion policy grants versions s native epoch version reply t native_after \<longleftrightarrow>
    reply = transition_result.Rejected Ineligible_Promotion \<and> t = s \<and> native_after = native"
  using assms by (simp add: guarded_native_promotion_def)

lemma guarded_promotion_consumes_native_lock_and_registry_checks:
  assumes step: "guarded_native_promotion policy grants versions s native epoch version
    (transition_result.Accepted Promotion_Finalized) t native_after"
  shows "lifecycle_step policy grants versions confirmed evidence (promotion_locks_clear policy native) s
    (Promote_Cycle epoch version) Lifecycle_Promoted t \<and>
    degree_state native_after = lifecycle_cutover t \<and> source_authority native_after = source_authority native"
proof -
  from step have match: "degree_state native = lifecycle_cutover s"
    and ready: "lifecycle_promotable (promotion_locks_clear policy native) s"
    and tariff: "versions version \<noteq> None"
    and promotion: "promote_settled_asset policy grants epoch version native =
      (native_after,transition_result.Accepted Promotion_Finalized)"
    and updated: "t = finish_promotion s (degree_state native_after) version"
    by (auto simp: guarded_native_promotion_def split: if_splits)
  have local: "lifecycle_step policy grants versions confirmed evidence (promotion_locks_clear policy native) s
    (Promote_Cycle epoch version) Lifecycle_Promoted t"
  proof -
    have cutover: "cutover_step policy grants (lifecycle_cutover s) (Confirm_Promotion epoch version)
        (transition_result.Accepted Promotion_Finalized) (degree_state native_after)"
      using settled_asset_promotion_projects_to_cutover[OF promotion] match by simp
    show ?thesis unfolding updated
      by (rule lifecycle_step.Promote) (rule ready, rule tariff, rule cutover)
  qed
  show ?thesis using local updated settled_asset_promotion_projects_to_cutover[OF promotion]
    by (simp add: finish_promotion_def)
qed

context source_attestation
begin

definition restore_with_native_terminal where
  "restore_with_native_terminal policy grants versions confirmed evidence s native restoration epoch index r duration t native_after
    \<longleftrightarrow>
    degree_state native = lifecycle_cutover s \<and>
    (\<exists>cycle released. cycle_names_native_binding cycle r \<and>
      resolve_cutover_lock Release_Reversal epoch index r duration native = (released, Reservation_Released) \<and>
      cycle_custody s = Native_Debit_Pending (binding_key (request_binding r)) \<and>
      (if lifecycle_phase s = Bound_Cycle cycle \<or> lifecycle_phase s = Verified_Cycle cycle then
        t = s\<lparr>cycle_custody := Local_Cells_Only, lifecycle_phase := Idle_Cycle\<rparr>
       else (\<exists>before. lifecycle_phase s = Partial_Cycle cycle before \<and>
         lifecycle_step policy grants versions confirmed evidence (promotion_locks_clear policy native)
           (s\<lparr>cycle_custody := Local_Cells_Only\<rparr>) (Restore_Cycle restoration) Cycle_Restored t)) \<and>
      native_after = released\<lparr>degree_state := lifecycle_cutover t\<rparr>)"

lemma native_partially_applied_binding_cannot_restore_without_reversal:
  assumes stale: "epoch \<noteq> core_epoch (credit_core native) \<or>
    \<not> exact_record_reference (credit_core native) index (request_binding r) Reversed_Decision (request_certificate r)"
  shows "\<not> restore_with_native_terminal policy grants versions confirmed evidence
    s native restoration epoch index r duration t native_after"
  using stale by (auto simp: restore_with_native_terminal_def resolve_cutover_lock_def Let_def split: if_splits)

lemma restoring_the_matching_cycle_preserves_the_native_terminal_history:
  assumes step: "restore_with_native_terminal policy grants versions confirmed evidence
    s native restoration epoch index r duration t native_after"
  shows "core_records (credit_core native_after) = core_records (credit_core native) \<and>
    core_published (credit_core native_after) = core_published (credit_core native) \<and>
    lifecycle_invoice t = lifecycle_invoice s \<and> lifecycle_phase t = Idle_Cycle"
proof -
  from step obtain released where actual:
    "resolve_cutover_lock Release_Reversal epoch index r duration native = (released, Reservation_Released)"
    and composed: "native_after = released\<lparr>degree_state := lifecycle_cutover t\<rparr>"
    and witness:
      "t = s\<lparr>cycle_custody := Local_Cells_Only, lifecycle_phase := Idle_Cycle\<rparr> \<or>
        lifecycle_step policy grants versions confirmed evidence (promotion_locks_clear policy native)
          (s\<lparr>cycle_custody := Local_Cells_Only\<rparr>) (Restore_Cycle restoration) Cycle_Restored t"
    by (auto simp: restore_with_native_terminal_def split: if_splits)
  have local_history: "lifecycle_step policy grants versions confirmed evidence (promotion_locks_clear policy native)
      (s\<lparr>cycle_custody := Local_Cells_Only\<rparr>) (Restore_Cycle restoration) Cycle_Restored t
      \<Longrightarrow> lifecycle_invoice t = lifecycle_invoice s \<and> lifecycle_phase t = Idle_Cycle"
    by (erule lifecycle_step.cases) auto
  have history: "lifecycle_invoice t = lifecycle_invoice s \<and> lifecycle_phase t = Idle_Cycle"
    using witness local_history by auto
  show ?thesis using lock_resolution_keeps_the_cutover_and_durable_publication[OF actual] history composed by simp
qed

lemma verified_reversal_before_commit_releases_the_debit_without_local_writes:
  assumes coherent: "degree_state native = lifecycle_cutover s"
    and prepared: "lifecycle_phase s = Bound_Cycle cycle \<or> lifecycle_phase s = Verified_Cycle cycle"
    and binding: "cycle_names_native_binding cycle r"
    and custody: "cycle_custody s = Native_Debit_Pending (binding_key (request_binding r))"
    and terminal: "resolve_cutover_lock Release_Reversal epoch index r duration native = (released, Reservation_Released)"
  shows "restore_with_native_terminal policy grants versions confirmed evidence s native restoration epoch index r duration
    (s\<lparr>cycle_custody := Local_Cells_Only, lifecycle_phase := Idle_Cycle\<rparr>)
    (released\<lparr>degree_state := lifecycle_cutover s\<rparr>)"
  using assms unfolding restore_with_native_terminal_def by (intro conjI exI[of _ cycle] exI[of _ released]) simp_all

theorem the_native_credit_consumes_the_same_binding_and_public_meter_row:
  assumes native_step: "meter_source_credit policy (ticket_metadata (cycle_ticket request)) epoch index sequence route r native =
    (native_after, Credit_Metered native_row)"
    and binding: "cycle_names_native_binding request r"
    and phase: "lifecycle_phase s = Verified_Cycle request"
    and projection: "lifecycle_cutover s = degree_state native"
    and current: "binding_is_current policy s request"
    and footprint: "checked_final_leaves evidence s request (transition_result.Accepted Binding_Committed) = Some leaves"
    and tariff: "versions (lifecycle_tariff s) = Some schedule"
  shows "\<exists>row t. lifecycle_step policy grants versions confirmed evidence locks s
      (Commit_Cycle True) (Cycle_Result (transition_result.Accepted Binding_Committed)) t \<and>
      lifecycle_cutover t = degree_state native_after \<and>
      row \<in> set (lifecycle_invoice t) \<and>
      accounted_binding row = binding_id native_row \<and>
      public_degree (usage_row_for_epoch row) = billing_level native_row \<and>
      public_domain_count (usage_row_for_epoch row) = domains_written native_row \<and>
      public_meter_version (usage_row_for_epoch row) = billing_version native_row \<and>
      public_session (usage_row_for_epoch row) = cycle_session_id request \<and>
      public_billing_day (usage_row_for_epoch row) = billing_day (lifecycle_clock s) \<and>
      charge_from_public_row precision versions (usage_row_for_epoch row) = Some (charge_of precision row)"
proof -
  let ?request_action = "request_flow request"
  let ?row = "\<lparr>accounted_attempt = cycle_attempt_id request, accounted_binding = cycle_binding_id request,
    accounted_session = cycle_session_id request, accounted_ticket = cycle_ticket request,
    accounted_clock = lifecycle_clock s, accounted_footprint = participants ?request_action,
    accounted_payload = leaves, accounted_abort = None, accounted_tariff = lifecycle_tariff s,
    accounted_schedule = schedule\<rparr>"
  let ?target = "s\<lparr>lifecycle_cutover := degree_state native_after,
    lifecycle_invoice := append_accounted_cycle (lifecycle_invoice s) ?row, lifecycle_phase := Idle_Cycle\<rparr>"
  have agreed: "cycle_binding_id request = prod_encode (binding_key (request_binding r))"
    "cycle_source request = fst (binding_key (request_binding r))"
    "cycle_target request = binding_destination (request_binding r)"
    "cycle_value request = binding_amount (request_binding r)"
    using binding by (auto simp: cycle_names_native_binding_def request_flow_def Let_def)
  note native = metered_credit_projects_to_one_cutover_commit[OF native_step, where grants=grants]
  have actual: "cutover_step policy grants (lifecycle_cutover s) (request_commit request True)
    (transition_result.Accepted Binding_Committed) (degree_state native_after)"
    using native by (simp only: projection request_commit_def agreed)
  have auth: "ticket_authorizes (lifecycle_registry s) policy (fst (cycle_session_id request)) (cycle_ticket request) ?request_action"
    using current unfolding binding_is_current_def by blast
  have meter: "metered_attempt policy grants versions evidence s request True (transition_result.Accepted Binding_Committed)
    (degree_state native_after) = Some ?row"
    using footprint actual auth tariff
    by (simp add: metered_attempt_def observed_commit_charge_def request_flow_def request_commit_def Let_def)
  have step: "lifecycle_step policy grants versions confirmed evidence locks s
    (Commit_Cycle True) (Cycle_Result (transition_result.Accepted Binding_Committed)) ?target"
    using lifecycle_step.Commit[OF phase current meter, where restoration_confirmed=confirmed and locks_clear=locks] by simp
  have old_rows: "cycle_attempt_id request \<notin> image accounted_attempt (set (lifecycle_invoice s))"
    using current by (simp add: binding_is_current_def)
  have no_prior_bill: "\<not> (\<exists>row \<in> set (lifecycle_invoice s). accounted_abort row = None \<and>
      accounted_session row = cycle_session_id request \<and> accounted_binding row = cycle_binding_id request)"
    using current unfolding binding_is_current_def by blast
  have usage: "native_row = billing_record (cycle_binding_id request) (ticket_metadata (cycle_ticket request)) ?request_action"
    using native current binding by (auto simp: cycle_names_native_binding_def binding_is_current_def projection Let_def)
  have current_tariff: "lifecycle_tariff s = meter_version (ticket_metadata (cycle_ticket request))"
    using current unfolding binding_is_current_def by blast
  have price: "charge_from_public_row precision versions (usage_row_for_epoch ?row) = Some (charge_of precision ?row)"
    by (rule public_row_reconstructs_the_exact_private_charge) (simp add: tariff)
  have extends: "append_accounted_cycle (lifecycle_invoice s) ?row = lifecycle_invoice s @ [?row]"
    unfolding append_accounted_cycle_def
    by (simp only: accounted_cycle.select_convs old_rows no_prior_bill if_False simp_thms)
  have row_in: "?row \<in> set (lifecycle_invoice ?target)" by (simp add: extends)
  show ?thesis using step usage current_tariff price row_in
    by (intro exI[of _ ?row] exI[of _ ?target])
       (simp add: usage_row_for_epoch_def billing_record_def settlement_epoch_def Let_def)
qed

end

end
