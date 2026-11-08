theory Frozen_Spend
  imports Governed_Orders
begin

definition protected_freeze_mode where
  "protected_freeze_mode mode \<longleftrightarrow> mode \<in> {FROZEN, SEIZED, CONFISCATED}"

lemma protected_mode_closes_ordinary_spending:
  "protected_freeze_mode mode \<Longrightarrow> \<not> ordinary_transfer_allowed baseline restriction mode"
  by (cases mode) (simp_all add: protected_freeze_mode_def ordinary_transfer_allowed_def)

definition lawful_enforcement_preconditions where
  "lawful_enforcement_preconditions s endpoint index r root sender recipient amount kind \<longleftrightarrow>
    (let context = current_lock_view s endpoint; rs = machine_state (core_parent s);
         operation = Enforcement_Transfer_Effect kind
     in record_reference s index root Confirmed_Decision \<noteq> None \<and> binding_key root \<in> core_published s \<and>
        root \<in> set (credit_history (received_messages rs)) \<and>
        request_binding r = descendant_binding root recipient amount operation \<and>
        enforcement_transfer_action kind \<and>
        get_reg_state (lock_metadata context) (binding_destination root) (binding_asset (request_binding r)) \<noteq> None \<and>
        current_use_allowed (lock_authority context) r \<and> context_endpoint (lock_authority context) = binding_destination root \<and>
        (request_caller r, binding_key root, sender, recipient, amount, operation) \<in> lock_spend_permissions context \<and>
        0 < amount \<and> amount \<le> destination_units rs (holder_account root sender) \<and>
        amount \<le> funded_units rs (binding_key root, holder_account root sender))"

context source_attestation
begin

theorem protected_ordinary_spending_cannot_change_authoritative_balances:
  assumes op: "binding_operation (request_binding r) = Ordinary_Transfer_Effect"
    and mode: "get_reg_state (lock_metadata (current_lock_view s endpoint))
      (binding_destination root) (binding_asset (request_binding r)) = Some policy"
    and protected: "protected_freeze_mode policy"
  shows "let result = invoke_protocol endpoint (core_epoch s) index (Descendant_Intent r root sender recipient amount) s
    in snd result \<in> {Finality_Rejected, Protocol_Response Request_Rejected} \<and>
       machine_state (core_parent (fst result)) = machine_state (core_parent s) \<and>
       core_records (fst result) = core_records s \<and> core_regulatory (fst result) = core_regulatory s"
proof -
  have denied: "\<not> metadata_permission (current_lock_view s endpoint) r (binding_destination root)"
    using op mode protected_mode_closes_ordinary_spending[OF protected]
    by (simp add: metadata_permission_def)
  show ?thesis using denied
    by (simp add: invoke_protocol_def execute_descendant_def reject_protocol_intent_def
      lift_protocol_result_def record_observation_def Let_def split: if_splits)
qed

theorem lawful_enforcement_consumes_the_exact_confirmed_root:
  assumes ready: "lawful_enforcement_preconditions s endpoint index r root sender recipient amount kind"
  shows "let result = invoke_protocol endpoint (core_epoch s) index (Descendant_Intent r root sender recipient amount) s
    in snd result = Protocol_Response Descendant_Executed \<and>
       (\<exists>event. lawful_descendants (machine_state (core_parent (fst result))) =
          lawful_descendants (machine_state (core_parent s)) @ [event] \<and>
          lineage_root event = root \<and> lineage_from event = sender \<and> lineage_to event = recipient \<and>
          lineage_amount event = amount \<and> lineage_caller event = request_caller r)"
proof -
  let ?context = "current_lock_view s endpoint"
  let ?operation = "Enforcement_Transfer_Effect kind"
  let ?event = "\<lparr>lineage_root = root, lineage_from = sender, lineage_to = recipient, lineage_amount = amount,
    lineage_operation = ?operation, lineage_caller = request_caller r, lineage_authority_epoch = request_authority_epoch r,
    lineage_version = request_version r\<rparr>"
  have bound: "request_binding r = descendant_binding root recipient amount ?operation"
    using ready unfolding lawful_enforcement_preconditions_def Let_def by blast
  have op: "binding_operation (request_binding r) = ?operation"
    unfolding bound by (simp add: descendant_binding_def)
  obtain mode where current: "get_reg_state (lock_metadata ?context) (binding_destination root)
      (binding_asset (request_binding r)) = Some mode"
    using ready unfolding lawful_enforcement_preconditions_def Let_def by auto
  have permit: "current_use_allowed (lock_authority ?context) r" and action: "enforcement_transfer_action kind"
    using ready unfolding lawful_enforcement_preconditions_def Let_def by simp_all
  have allowed: "metadata_permission ?context r (binding_destination root)"
    using current op permit action by (simp add: metadata_permission_def transfer_allowed_def)
  have execution: "execute_descendant ?context r root sender recipient amount (core_parent s) =
    record_observation r Descendant_Executed (commit_reservation_event (Descendant_Event ?event) (core_parent s))"
    using ready allowed op unfolding lawful_enforcement_preconditions_def
    by (simp add: execute_descendant_def Let_def descendant_binding_def)
  have reference: "terminal_intent_guard s index (Descendant_Intent r root sender recipient amount)"
    using ready by (simp add: lawful_enforcement_preconditions_def Let_def)
  let ?result = "invoke_protocol endpoint (core_epoch s) index (Descendant_Intent r root sender recipient amount) s"
  show ?thesis unfolding Let_def
  proof (rule conjI)
    show "snd ?result = Protocol_Response Descendant_Executed"
      using reference by (simp add: invoke_protocol_def execution lift_protocol_result_def record_observation_def Let_def)
    show "\<exists>event. lawful_descendants (machine_state (core_parent (fst ?result))) =
        lawful_descendants (machine_state (core_parent s)) @ [event] \<and>
        lineage_root event = root \<and> lineage_from event = sender \<and> lineage_to event = recipient \<and>
        lineage_amount event = amount \<and> lineage_caller event = request_caller r"
      using reference by (intro exI[of _ ?event])
        (simp add: invoke_protocol_def execution lift_protocol_result_def record_observation_def commit_reservation_event_def Let_def)
  qed
qed

end

end
