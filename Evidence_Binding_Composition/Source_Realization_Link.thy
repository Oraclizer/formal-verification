(* SPDX-License-Identifier: BSD-3-Clause *)
theory Source_Realization_Link
  imports Funding_Realization Integration_Transport
    "Evidence_Atomic_Binding.Finality_Terminal_Scenarios"
    "Evidence_Atomic_Binding.Sourced_Response_Link"
begin

section \<open>Installing Current Inputs and Calling the Existing Source Dispatcher\<close>

definition source_realization_request :: "source_certificate \<Rightarrow> descendant_effect \<Rightarrow> execution_request" where
  "source_realization_request certificate effect=funding_probe_request certificate
    (lineage_root effect)(lineage_to effect)(lineage_amount effect)"

definition source_realization_context :: "descendant_effect \<Rightarrow> lock_context" where
  "source_realization_context effect=funding_probe_context (lineage_root effect)
    (lineage_from effect)(lineage_to effect)(lineage_amount effect)"

definition source_realization_intent :: "source_certificate \<Rightarrow> descendant_effect \<Rightarrow> protocol_intent" where
  "source_realization_intent certificate effect=Descendant_Intent
    (source_realization_request certificate effect)(lineage_root effect)
    (lineage_from effect)(lineage_to effect)(lineage_amount effect)"

definition source_realization_word :: "source_certificate \<Rightarrow> nat \<Rightarrow> descendant_effect
  \<Rightarrow> source_coupling_action list" where
  "source_realization_word certificate index effect=[
    Coupling_Environment (binding_destination(lineage_root effect))(source_realization_context effect),
    Coupling_Client True(Client_Protocol (binding_destination(lineage_root effect))index
      (source_realization_intent certificate effect))]"

fun source_realization_words :: "(transfer_binding \<Rightarrow> source_certificate) \<Rightarrow>
  (transfer_binding \<Rightarrow> nat) \<Rightarrow> descendant_effect list \<Rightarrow> source_coupling_action list" where
  "source_realization_words certificates indices []=[]"
| "source_realization_words certificates indices (effect#effects)=
    source_realization_word(certificates(lineage_root effect))(indices(lineage_root effect))effect @
      source_realization_words certificates indices effects"

lemma active_snapshot_preserves_the_actual_probe:
  assumes active: "get_reg_state regulatory (binding_destination root)(binding_asset root)=Some ACTIVE"
  shows "execute_descendant
      ((funding_probe_context root sender recipient amount)\<lparr>lock_metadata:=regulatory\<rparr>)
      (funding_probe_request certificate root recipient amount)root sender recipient amount parent=
    execute_descendant(funding_probe_context root sender recipient amount)
      (funding_probe_request certificate root recipient amount)root sender recipient amount parent"
proof -
  have actual_metadata: "metadata_permission
      ((funding_probe_context root sender recipient amount)\<lparr>lock_metadata:=regulatory\<rparr>)
      (funding_probe_request certificate root recipient amount)(binding_destination root)"
    using active by (simp add: metadata_permission_def funding_probe_context_def funding_probe_request_def
      descendant_binding_def current_use_allowed_def ordinary_transfer_allowed_def)
  have probe_metadata: "metadata_permission(funding_probe_context root sender recipient amount)
      (funding_probe_request certificate root recipient amount)(binding_destination root)"
    by (rule funding_probe_uses_actual_current_authorization(2))
  show ?thesis
    by (simp add: execute_descendant_def Let_def actual_metadata probe_metadata)
qed

context source_attestation
begin

definition source_realization_installed :: "descendant_effect \<Rightarrow> source_coupling_state \<Rightarrow>
  source_coupling_state" where
  "source_realization_installed effect s=fst(source_coupling_step
    (Coupling_Environment (binding_destination(lineage_root effect))(source_realization_context effect))s)"

lemma source_realization_install_shape:
  "source_realization_installed effect s=s\<lparr>coupled_core:=
    (coupled_core s)\<lparr>core_contexts:=(core_contexts(coupled_core s))
      (binding_destination(lineage_root effect):=source_realization_context effect),
      core_epoch:=Suc(core_epoch(coupled_core s))\<rparr>\<rparr>"
  by (simp add: source_realization_installed_def execute_finality_environment_def finality_step_def
      source_realization_context_def funding_probe_context_def Let_def)

theorem source_realization_one_step_is_the_actual_parent_result:
  fixes effect :: descendant_effect and s :: source_coupling_state
    and certificate :: source_certificate
  assumes reference: "record_reference(coupled_core s)index(lineage_root effect)Confirmed_Decision\<noteq>None"
    and published: "binding_key(lineage_root effect)\<in>core_published(coupled_core s)"
    and active: "get_reg_state(receiver_snapshot(core_regulatory(coupled_core s)))
      (binding_destination(lineage_root effect))(binding_asset(lineage_root effect))=Some ACTIVE"
  defines "parent_result \<equiv> execute_descendant(source_realization_context effect)
    (source_realization_request certificate effect)(lineage_root effect)
    (lineage_from effect)(lineage_to effect)(lineage_amount effect)(core_parent(coupled_core s))"
    and "installed \<equiv> source_realization_installed effect s"
    and "after \<equiv> run_source_coupling(source_realization_word certificate index effect)s"
  shows "snd(source_coupling_step(Coupling_Client True(Client_Protocol
      (binding_destination(lineage_root effect))index(source_realization_intent certificate effect)))installed)=
      Coupling_Client_Reply(Protocol_Response(snd parent_result)) \<and>
    core_parent(coupled_core after)=fst parent_result \<and>
    coupled_source after=coupled_source s \<and> coupled_receipts after=coupled_receipts s \<and>
    coupled_sent after=coupled_sent s \<and> coupled_blocked after=coupled_blocked s \<and>
    core_records(coupled_core after)=core_records(coupled_core s) \<and>
    core_published(coupled_core after)=core_published(coupled_core s) \<and>
    core_regulatory(coupled_core after)=core_regulatory(coupled_core s) \<and>
    core_epoch(coupled_core after)=Suc(Suc(core_epoch(coupled_core s)))"
proof -
  have view: "current_lock_view(coupled_core installed)(binding_destination(lineage_root effect))=
    (source_realization_context effect)\<lparr>lock_metadata:=receiver_snapshot(core_regulatory(coupled_core s))\<rparr>"
    by (simp add: installed_def source_realization_install_shape current_lock_view_def)
  have guard: "terminal_intent_guard(coupled_core installed)index(source_realization_intent certificate effect)"
    using reference published
    by (simp add: installed_def source_realization_install_shape source_realization_intent_def record_reference_def)
  have parent: "execute_descendant(current_lock_view(coupled_core installed)
      (binding_destination(lineage_root effect)))(source_realization_request certificate effect)
      (lineage_root effect)(lineage_from effect)(lineage_to effect)(lineage_amount effect)
      (core_parent(coupled_core installed))=parent_result"
    using active_snapshot_preserves_the_actual_probe[OF active,
      where sender="lineage_from effect" and recipient="lineage_to effect"
        and amount="lineage_amount effect" and certificate=certificate
        and parent="core_parent(coupled_core s)"]
    by (simp only: view; simp add: installed_def source_realization_install_shape parent_result_def
      source_realization_context_def source_realization_request_def)
  have client: "execute_finality_client(Client_Protocol(binding_destination(lineage_root effect))index
      (source_realization_intent certificate effect))(coupled_core installed)=
    ((coupled_core installed)\<lparr>core_parent:=fst parent_result,
      core_epoch:=Suc(core_epoch(coupled_core installed))\<rparr>,Protocol_Response(snd parent_result))"
    using guard parent
    by (simp add: execute_finality_client_def finality_step_def invoke_protocol_def
      source_realization_intent_def lift_protocol_result_def Let_def)
  have stepped: "source_coupling_step(Coupling_Client True(Client_Protocol
      (binding_destination(lineage_root effect))index(source_realization_intent certificate effect)))installed=
    (installed\<lparr>coupled_core:=fst(execute_finality_client(Client_Protocol
      (binding_destination(lineage_root effect))index(source_realization_intent certificate effect))
      (coupled_core installed))\<rparr>,Coupling_Client_Reply(Protocol_Response(snd parent_result)))"
    by (simp add: coupling_client_step_def source_realization_intent_def
        client[unfolded source_realization_intent_def] Let_def)
  have after: "after=fst(source_coupling_step(Coupling_Client True(Client_Protocol
      (binding_destination(lineage_root effect))index(source_realization_intent certificate effect)))installed)"
    by (simp add: after_def source_realization_word_def installed_def source_realization_installed_def)
  show ?thesis by (simp only: after stepped client;
    simp add: installed_def source_realization_install_shape)
qed

theorem source_realization_finite_word_projection:
  assumes references: "\<forall>effect\<in>set effects.
      record_reference(coupled_core s)(indices(lineage_root effect))(lineage_root effect)Confirmed_Decision\<noteq>None"
    and published: "\<forall>effect\<in>set effects. binding_key(lineage_root effect)\<in>core_published(coupled_core s)"
    and active: "\<forall>effect\<in>set effects.
      get_reg_state(receiver_snapshot(core_regulatory(coupled_core s)))
        (binding_destination(lineage_root effect))(binding_asset(lineage_root effect))=Some ACTIVE"
  shows "core_parent(coupled_core(run_source_coupling(source_realization_words certificates indices effects)s))=
      run_realization certificates effects(core_parent(coupled_core s)) \<and>
    coupled_source(run_source_coupling(source_realization_words certificates indices effects)s)=coupled_source s \<and>
    core_records(coupled_core(run_source_coupling(source_realization_words certificates indices effects)s))=
      core_records(coupled_core s) \<and>
    core_published(coupled_core(run_source_coupling(source_realization_words certificates indices effects)s))=
      core_published(coupled_core s) \<and>
    core_regulatory(coupled_core(run_source_coupling(source_realization_words certificates indices effects)s))=
      core_regulatory(coupled_core s)"
  using assms
proof (induction effects arbitrary:s)
  case Nil
  then show ?case by simp
next
  case (Cons effect effects)
  let ?next="run_source_coupling(source_realization_word(certificates(lineage_root effect))
    (indices(lineage_root effect))effect)s"
  have reference: "record_reference(coupled_core s)(indices(lineage_root effect))
    (lineage_root effect)Confirmed_Decision\<noteq>None" using Cons.prems(1) by simp
  have publication: "binding_key(lineage_root effect)\<in>core_published(coupled_core s)"
    using Cons.prems(2) by simp
  have metadata: "get_reg_state(receiver_snapshot(core_regulatory(coupled_core s)))
    (binding_destination(lineage_root effect))(binding_asset(lineage_root effect))=Some ACTIVE"
    using Cons.prems(3) by simp
  note step=source_realization_one_step_is_the_actual_parent_result[OF reference publication metadata,
    where certificate="certificates(lineage_root effect)"]
  have tail_references: "\<forall>e\<in>set effects.
    record_reference(coupled_core ?next)(indices(lineage_root e))(lineage_root e)Confirmed_Decision\<noteq>None"
    using Cons.prems(1) step by (auto simp: record_reference_def)
  have tail_published: "\<forall>e\<in>set effects. binding_key(lineage_root e)\<in>core_published(coupled_core ?next)"
    using Cons.prems(2) step by auto
  have tail_active: "\<forall>e\<in>set effects.
    get_reg_state(receiver_snapshot(core_regulatory(coupled_core ?next)))
      (binding_destination(lineage_root e))(binding_asset(lineage_root e))=Some ACTIVE"
    using Cons.prems(3) step by auto
  note tail=Cons.IH[OF tail_references tail_published tail_active]
  show ?case using step tail
    by (simp add: progress_source_run_append source_realization_context_def source_realization_request_def
      realization_result_def)
qed

definition source_realization_reply :: "(transfer_binding \<Rightarrow> source_certificate) \<Rightarrow>
  (transfer_binding \<Rightarrow> nat) \<Rightarrow> descendant_effect \<Rightarrow> source_coupling_state \<Rightarrow>
  source_coupling_reply" where
  "source_realization_reply certificates indices effect s=snd(source_coupling_step
    (Coupling_Client True(Client_Protocol(binding_destination(lineage_root effect))
      (indices(lineage_root effect))(source_realization_intent(certificates(lineage_root effect))effect)))
    (source_realization_installed effect s))"

theorem source_realization_actual_reply_at_every_prefix:
  assumes references: "\<forall>effect\<in>set effects.
      record_reference(coupled_core s)(indices(lineage_root effect))(lineage_root effect)Confirmed_Decision\<noteq>None"
    and published: "\<forall>effect\<in>set effects. binding_key(lineage_root effect)\<in>core_published(coupled_core s)"
    and active: "\<forall>effect\<in>set effects.
      get_reg_state(receiver_snapshot(core_regulatory(coupled_core s)))
        (binding_destination(lineage_root effect))(binding_asset(lineage_root effect))=Some ACTIVE"
    and index: "i<length effects"
  shows "source_realization_reply certificates indices(effects!i)
      (run_source_coupling(source_realization_words certificates indices(take i effects))s)=
    Coupling_Client_Reply(Protocol_Response(snd(realization_result certificates(effects!i)
      (run_realization certificates(take i effects)(core_parent(coupled_core s))))))"
proof -
  let ?prefix="run_source_coupling(source_realization_words certificates indices(take i effects))s"
  have prefix_references: "\<forall>e\<in>set(take i effects).
    record_reference(coupled_core s)(indices(lineage_root e))(lineage_root e)Confirmed_Decision\<noteq>None"
    using references by (meson set_take_subset subsetD)
  have prefix_published: "\<forall>e\<in>set(take i effects). binding_key(lineage_root e)\<in>core_published(coupled_core s)"
    using published by (meson set_take_subset subsetD)
  have prefix_active: "\<forall>e\<in>set(take i effects).
    get_reg_state(receiver_snapshot(core_regulatory(coupled_core s)))
      (binding_destination(lineage_root e))(binding_asset(lineage_root e))=Some ACTIVE"
    using active by (meson set_take_subset subsetD)
  note prefix=source_realization_finite_word_projection[OF prefix_references prefix_published prefix_active,
    where certificates=certificates]
  have member: "effects!i\<in>set effects" using index by simp
  have reference: "record_reference(coupled_core ?prefix)(indices(lineage_root(effects!i)))
      (lineage_root(effects!i))Confirmed_Decision\<noteq>None"
    using references member prefix by (auto simp: record_reference_def)
  have publication: "binding_key(lineage_root(effects!i))\<in>core_published(coupled_core ?prefix)"
    using published member prefix by blast
  have metadata: "get_reg_state(receiver_snapshot(core_regulatory(coupled_core ?prefix)))
    (binding_destination(lineage_root(effects!i)))(binding_asset(lineage_root(effects!i)))=Some ACTIVE"
  proof -
    have frame: "core_regulatory(coupled_core ?prefix)=core_regulatory(coupled_core s)"
      using prefix by blast
    have before: "get_reg_state(receiver_snapshot(core_regulatory(coupled_core s)))
      (binding_destination(lineage_root(effects!i)))(binding_asset(lineage_root(effects!i)))=Some ACTIVE"
      by (rule bspec[OF active member])
    show ?thesis by (simp only: frame before)
  qed
  note step=source_realization_one_step_is_the_actual_parent_result[OF reference publication metadata,
    where certificate="certificates(lineage_root(effects!i))"]
  show ?thesis using step prefix
    by (simp add: source_realization_reply_def realization_result_def
      source_realization_context_def source_realization_request_def)
qed

theorem source_realization_constructive_plan_uses_the_actual_dispatcher:
  fixes s :: source_coupling_state
    and certificates :: "transfer_binding \<Rightarrow> source_certificate"
    and effects :: "descendant_effect list"
  assumes financial: "financial_history_agreement balances(core_parent(coupled_core s))"
    and credited: "\<forall>root\<in>set roots. root\<in>set(credit_history(received_messages(machine_state(core_parent(coupled_core s)))))"
    and keys: "distinct(map binding_key roots)" and holders: "distinct holders"
    and masses: "\<forall>root\<in>set roots. sum_list(map(target root)holders)=
      sum_list(map(realization_units(core_parent(coupled_core s))root)holders)"
    and references: "\<forall>root\<in>set roots.
      record_reference(coupled_core s)(indices root)root Confirmed_Decision\<noteq>None"
    and published: "\<forall>root\<in>set roots. binding_key root\<in>core_published(coupled_core s)"
    and active: "\<forall>root\<in>set roots. get_reg_state(receiver_snapshot(core_regulatory(coupled_core s)))
      (binding_destination root)(binding_asset root)=Some ACTIVE"
  defines "effects \<equiv> realization_plan roots holders(core_parent(coupled_core s))target"
    and "after \<equiv> run_source_coupling(source_realization_words certificates indices effects)s"
  shows "(\<forall>root\<in>set roots. \<forall>holder\<in>set holders.
      realization_units(core_parent(coupled_core after))root holder=target root holder) \<and>
    coupled_source after=coupled_source s \<and>
    (\<forall>i<length effects. source_realization_reply certificates indices(effects!i)
      (run_source_coupling(source_realization_words certificates indices(take i effects))s)=
      Coupling_Client_Reply(Protocol_Response Descendant_Executed))"
proof -
  have initial: "\<forall>root\<in>set roots. \<forall>holder\<in>set holders.
    realization_units(core_parent(coupled_core s))root holder=
    realization_units(core_parent(coupled_core s))root holder" by simp
  have construction: "realization_succeeds certificates effects(core_parent(coupled_core s)) \<and>
    (\<forall>root\<in>set roots. \<forall>holder\<in>set holders.
      realization_units(run_realization certificates effects(core_parent(coupled_core s)))root holder=target root holder)"
    unfolding effects_def realization_plan_def
    by (rule realization_plan_from_is_constructive[OF financial credited keys holders initial masses])
  have support: "\<And>e. e\<in>set effects \<Longrightarrow> lineage_root e\<in>set roots"
    unfolding effects_def realization_plan_def using realization_plan_support by blast
  have refs: "\<forall>e\<in>set effects.
    record_reference(coupled_core s)(indices(lineage_root e))(lineage_root e)Confirmed_Decision\<noteq>None"
    using references support by blast
  have pubs: "\<forall>e\<in>set effects. binding_key(lineage_root e)\<in>core_published(coupled_core s)"
    using published support by blast
  have metadata: "\<forall>e\<in>set effects. get_reg_state(receiver_snapshot(core_regulatory(coupled_core s)))
    (binding_destination(lineage_root e))(binding_asset(lineage_root e))=Some ACTIVE"
    using active support by blast
  note projection=source_realization_finite_word_projection[OF refs pubs metadata,where certificates=certificates]
  have replies: "\<forall>i<length effects. source_realization_reply certificates indices(effects!i)
      (run_source_coupling(source_realization_words certificates indices(take i effects))s)=
      Coupling_Client_Reply(Protocol_Response Descendant_Executed)"
  proof (intro allI impI)
    fix i assume i: "i<length effects"
    have success: "snd(realization_result certificates(effects!i)
      (run_realization certificates(take i effects)(core_parent(coupled_core s))))=Descendant_Executed"
      by (rule realization_success_at_every_prefix) (use construction i in auto)
    show "source_realization_reply certificates indices(effects!i)
      (run_source_coupling(source_realization_words certificates indices(take i effects))s)=
      Coupling_Client_Reply(Protocol_Response Descendant_Executed)"
      by (simp only: source_realization_actual_reply_at_every_prefix[OF refs pubs metadata i] success)
  qed
  show ?thesis using projection construction replies by (simp add: after_def)
qed

theorem finite_source_realization_preserves_the_exact_financial_projection:
  fixes certificates :: "transfer_binding \<Rightarrow> source_certificate"
    and effects :: "descendant_effect list"
  assumes contract: "reservation_contract balances(core_parent(coupled_core s))"
    and credited: "\<forall>root\<in>set roots. root\<in>set(credit_history(received_messages(machine_state(core_parent(coupled_core s)))))"
    and keys: "distinct(map binding_key roots)" and holders: "distinct holders"
    and rows: "\<forall>root\<in>set roots. sum_list(map(target root)holders)=
      sum_list(map(realization_units(core_parent(coupled_core s))root)holders)"
    and columns: "\<forall>account. realization_account_total roots holders target account=
      realization_account_total roots holders(realization_units(core_parent(coupled_core s)))account"
    and references: "\<forall>root\<in>set roots.
      record_reference(coupled_core s)(indices root)root Confirmed_Decision\<noteq>None"
    and published: "\<forall>root\<in>set roots. binding_key root\<in>core_published(coupled_core s)"
    and active: "\<forall>root\<in>set roots. get_reg_state(receiver_snapshot(core_regulatory(coupled_core s)))
      (binding_destination root)(binding_asset root)=Some ACTIVE"
  defines "effects \<equiv> realization_plan roots holders(core_parent(coupled_core s))target"
    and "after \<equiv> run_source_coupling(source_realization_words certificates indices effects)s"
  shows "core_parent(coupled_core after)=run_reservations balances(realization_actions certificates effects)
      (core_parent(coupled_core s)) \<and>
    erase_lineage_state(core_parent(coupled_core after))=erase_lineage_state(core_parent(coupled_core s)) \<and>
    destination_units(machine_state(core_parent(coupled_core after)))=
      destination_units(machine_state(core_parent(coupled_core s))) \<and>
    machine_journal(core_parent(coupled_core after))=
      machine_journal(core_parent(coupled_core s))@map Descendant_Event effects \<and>
    coupled_source after=coupled_source s \<and>
    reservation_contract balances(core_parent(coupled_core after))"
proof -
  note funding=finite_funding_realization[OF contract credited keys holders rows columns,
    where certificates=certificates]
  have support: "\<And>e. e\<in>set effects \<Longrightarrow> lineage_root e\<in>set roots"
    unfolding effects_def realization_plan_def using realization_plan_support by blast
  have refs: "\<forall>e\<in>set effects.
    record_reference(coupled_core s)(indices(lineage_root e))(lineage_root e)Confirmed_Decision\<noteq>None"
    using references support by blast
  have pubs: "\<forall>e\<in>set effects. binding_key(lineage_root e)\<in>core_published(coupled_core s)"
    using published support by blast
  have metadata: "\<forall>e\<in>set effects. get_reg_state(receiver_snapshot(core_regulatory(coupled_core s)))
    (binding_destination(lineage_root e))(binding_asset(lineage_root e))=Some ACTIVE"
    using active support by blast
  note projection=source_realization_finite_word_projection[OF refs pubs metadata,where certificates=certificates]
  show ?thesis using funding projection
    by (simp add: after_def effects_def realization_run_is_parent_execution[symmetric])
qed

end

section \<open>Receipts Produced by the Actual Two-Root Source History\<close>

definition realization_source_commands :: "controlled_source_command list" where
  "realization_source_commands=[
    Controlled_Boundary(Boundary_Apply(sample_binding 17)),Controlled_Finalize(sample_binding 17),
    Controlled_Boundary(Boundary_Apply(sample_binding 23)),Controlled_Finalize(sample_binding 23)]"

definition realization_receipts :: "source_certificate list" where
  "realization_receipts=generated_source_receipts sample_balances realization_source_commands
    [linked_certificate 17,linked_certificate 23]"

interpretation realized: source_attestation example_roster example_faulty example_bound example_threshold
  "source_receipt_verifies realization_receipts" "source_receipt_signed realization_receipts"
  "controlled_produced_fact sample_balances realization_source_commands"
  "controlled_stable_source sample_balances realization_source_commands"
  unfolding realization_receipts_def by (rule source_receipts_interpret_source_attestation)

lemma realization_receipts_are_generated:
  "realization_receipts=[linked_certificate 17,linked_certificate 23]"
  by (simp add: realization_receipts_def generated_source_receipts_def realization_source_commands_def
    issue_source_receipt_def source_receipt_slot_available_def linked_certificate_def sample_statement_def
    initial_controlled_source_def initial_source_boundary_def controlled_boundary_def controlled_finalize_def
    controlled_record_finalized_def controlled_source_fact_def boundary_apply_def boundary_record_effect_def
    boundary_has_effect_def boundary_valid_binding_def sample_binding_def example_binding_def
    sample_balances_def source_account_of_def Let_def)

lemma realization_checked_certificate:
  "event\<in>{17,23} \<Longrightarrow> realized.certificate_ok(linked_certificate event)"
  unfolding realized.certificate_ok_def
  by (auto simp: source_receipt_verifies_def realization_receipts_are_generated linked_certificate_def
    example_roster_def example_threshold_def)

definition realization_credit_request :: "nat \<Rightarrow> execution_request" where
  "realization_credit_request event=(sample_request event)\<lparr>request_certificate:=linked_certificate event\<rparr>"

lemma realization_credit_admission:
  assumes member: "event\<in>{17,23}"
  shows "realized.credit_admissible example_context(realization_credit_request event)"
proof -
  have checked: "realized.certificate_ok(linked_certificate event)"
    by (rule realization_checked_certificate[OF member])
  show ?thesis using checked member
    by (auto simp: realized.credit_admissible_def realized.authenticated_request_def realization_credit_request_def
      sample_request_def linked_certificate_def sample_statement_def sample_binding_def example_binding_def
      current_use_allowed_def example_context_def)
qed

lemma realization_certificate_projections:
  "certificate_statement(linked_certificate event)=sample_statement event"
  "certificate_epoch(linked_certificate event)=8"
  "certificate_signature(linked_certificate event)=event"
  by (simp_all add: linked_certificate_def)

definition realization_source_prefix :: "nat \<Rightarrow> source_coupling_action list" where
  "realization_source_prefix event=coupling_prepare event@[
    Coupling_Source True True(Controlled_Boundary(Boundary_Apply(sample_binding event))),
    Coupling_Client True(Client_Protocol 0 0(Source_Intent(sample_request event)0[])),
    Coupling_Source True True(Controlled_Finalize(sample_binding event))]"

definition realization_credit_word :: "nat \<Rightarrow> source_coupling_action list" where
  "realization_credit_word event=realization_source_prefix event @
    terminal_finish_actions 2(linked_certificate event)(Deliver_Intent Bypass_Route(realization_credit_request event)) @
    [Coupling_Client True(Client_Protocol 0 0(Reconcile_Intent(realization_credit_request event)0[]))]"

definition realization_parent_credit_word :: "nat \<Rightarrow> reservation_action list" where
  "realization_parent_credit_word event=sample_prefix event@[
    Publish_Action(linked_certificate event),
    Deliver_Action Bypass_Route example_context(realization_credit_request event),
    Reconcile_Action(sample_source_context ACTIVE)(realization_credit_request event)0(\<lambda>_.0)]"

definition realization_parent_first :: reservation_machine where
  "realization_parent_first=realized.run_reservations sample_balances(realization_parent_credit_word 17)sample_initial"

definition realization_parent_second :: reservation_machine where
  "realization_parent_second=realized.run_reservations sample_balances(realization_parent_credit_word 23)realization_parent_first"

definition realization_source_first :: source_coupling_state where
  "realization_source_first=realized.run_source_coupling(realization_credit_word 17)conservation_initial"

definition realization_source_second :: source_coupling_state where
  "realization_source_second=realized.run_source_coupling(realization_credit_word 23)realization_source_first"

lemmas realization_source_execution =
  realized.run_source_coupling.simps realized.source_coupling_step.simps
  realized.coupling_client_step_def realized.coupling_client_result.simps
  realized.execute_finality_client_def realized.finality_step_def realized.core_result.simps
  realized.invoke_protocol_def realized.intent_result.simps realized.record_terminal_def
  realized.publish_source_certificate_def realized.deliver_reserved_credit_def realized.published_receive_expansion
  realized.publish_primary_def realized.reconcile_recorded_credit_def
  coupling_source_result_def coupling_issue_result_def coupling_live_receipt_def coupling_monetary_def
  coupling_effect_witness_def boundary_evidence_exact boundary_has_effect_def
  controlled_boundary_def controlled_finalize_def controlled_record_finalized_def controlled_source_fact_def
  initial_controlled_source_def initial_source_boundary_def boundary_apply_def boundary_record_effect_def
  boundary_valid_binding_def initial_source_coupling_def initial_finality_core_def current_lock_view_def
  acquire_reservation_def dispatch_source_def execute_source_effect_def
  lift_protocol_result_def record_observation_def commit_reservation_event_def vector_lookup_def
  issue_source_receipt_def source_receipt_slot_available_def source_origin_present_def
  exact_record_reference_def record_reference_def terminal_effect_completed_def
  record_credit_def credit_marker_def empty_message_state_def realization_certificate_projections

lemma realization_parent_first_state:
  "machine_state realization_parent_first=(initial_reservation_state sample_balances)\<lparr>
    reservation_at:=(\<lambda>_.None)((0,17):=Some(sample_confirmed_record 17)),
    source_units:=sample_balances((0,17):=5),source_effects:=[sample_binding 17],
    issued_certificates:=[linked_certificate 17],
    received_messages:=record_credit(sample_binding 17)empty_message_state,
    destination_units:=(\<lambda>_.0)((2,17,3):=5),funded_units:=(\<lambda>_.0)(((0,17),(2,17,3)):=5)\<rparr>"
  by (simp add: realization_parent_first_def realization_parent_credit_word_def realization_credit_request_def
    sample_confirmed_record_def sample_data_defs realized.run_reservations.simps realized.reservation_step.simps
    realized.protocol_definitions realized.published_receive_expansion
    realized.credit_admissible_def realized.authenticated_request_def
    realization_checked_certificate realization_certificate_projections sample_statement_def
    record_observation_def commit_reservation_event_def record_credit_def credit_marker_def
    empty_message_state_def Let_def fun_eq_iff)

lemma realization_first_source_shape:
  "realization_source_first=(initial_source_coupling sample_balances(sample_metadata ACTIVE)conservation_contexts)\<lparr>
    coupled_source:=run_controlled_source
      [Controlled_Boundary(Boundary_Apply(sample_binding 17)),Controlled_Finalize(sample_binding 17)]
      (initial_controlled_source sample_balances),
    coupled_core:=(initial_finality_core sample_balances(sample_metadata ACTIVE)conservation_contexts)\<lparr>
      core_parent:=realization_parent_first,
      core_records:=(\<lambda>_.None)((0,17):=Some(progress_terminal_record(linked_certificate 17)Confirmed_Decision)),
      core_published:={(0,17)},core_epoch:=8\<rparr>,
    coupled_receipts:=[linked_certificate 17],coupled_sent:={(0,17)}\<rparr>"
  by (simp add: realization_source_first_def realization_credit_word_def realization_source_prefix_def
    terminal_finish_actions_def terminal_effect_actions_def terminal_evidence_actions_def coupling_prepare_def
    conservation_initial_def conservation_contexts_def realization_parent_first_def realization_parent_credit_word_def
    realization_credit_request_def realization_source_execution
    realized.run_reservations.simps realized.reservation_step.simps realized.protocol_definitions
    realized.credit_admissible_def realized.authenticated_request_def
    realization_checked_certificate sample_data_defs realization_certificate_projections sample_statement_def
    progress_terminal_record_def Let_def)

lemma realization_parent_second_state:
  "machine_state realization_parent_second=(machine_state realization_parent_first)\<lparr>
    reservation_at:=(reservation_at(machine_state realization_parent_first))((0,23):=Some(sample_confirmed_record 23)),
    source_units:=(source_units(machine_state realization_parent_first))((0,17):=0),
    source_effects:=[sample_binding 17,sample_binding 23],
    issued_certificates:=[linked_certificate 17,linked_certificate 23],
    received_messages:=record_credit(sample_binding 23)(received_messages(machine_state realization_parent_first)),
    destination_units:=(destination_units(machine_state realization_parent_first))((2,17,3):=10),
    funded_units:=(funded_units(machine_state realization_parent_first))(((0,23),(2,17,3)):=5)\<rparr>"
  by (simp add: realization_parent_second_def realization_parent_credit_word_def realization_credit_request_def
    realization_parent_first_state sample_confirmed_record_def sample_data_defs
    realized.run_reservations.simps realized.reservation_step.simps realized.protocol_definitions
    realized.published_receive_expansion realized.credit_admissible_def realized.authenticated_request_def
    realization_checked_certificate realization_certificate_projections sample_statement_def
    record_observation_def commit_reservation_event_def record_credit_def credit_marker_def
    empty_message_state_def Let_def fun_eq_iff)

lemma realization_second_source_shape:
  "realization_source_second=realization_source_first\<lparr>
    coupled_source:=run_controlled_source realization_source_commands(initial_controlled_source sample_balances),
    coupled_core:=(coupled_core realization_source_first)\<lparr>core_parent:=realization_parent_second,
      core_records:=(core_records(coupled_core realization_source_first))
        ((0,23):=Some(progress_terminal_record(linked_certificate 23)Confirmed_Decision)),
      core_published:={(0,17),(0,23)},core_epoch:=16\<rparr>,
    coupled_receipts:=[linked_certificate 17,linked_certificate 23],coupled_sent:={(0,17),(0,23)}\<rparr>"
proof -
  define parent_prefix where
    "parent_prefix=realized.run_reservations sample_balances(sample_prefix 23)realization_parent_first"
  define submitted where
    "submitted=realized.run_source_coupling(realization_source_prefix 23)realization_source_first"
  define prepared where
    "prepared=realized.run_source_coupling(terminal_evidence_actions 2(linked_certificate 23))submitted"
  have first_fields:
    "core_parent(coupled_core realization_source_first)=realization_parent_first"
    "core_records(coupled_core realization_source_first)=
      (\<lambda>_.None)((0,17):=Some(progress_terminal_record(linked_certificate 17)Confirmed_Decision))"
    "core_published(coupled_core realization_source_first)={(0,17)}"
    "core_contexts(coupled_core realization_source_first)=conservation_contexts"
    "core_regulatory(coupled_core realization_source_first)=
      \<lparr>receiver_snapshot=sample_metadata ACTIVE,receiver_applied={}\<rparr>"
    "core_epoch(coupled_core realization_source_first)=8"
    "coupled_source realization_source_first=run_controlled_source
      [Controlled_Boundary(Boundary_Apply(sample_binding 17)),Controlled_Finalize(sample_binding 17)]
      (initial_controlled_source sample_balances)"
    "coupled_receipts realization_source_first=[linked_certificate 17]"
    "coupled_sent realization_source_first={(0,17)}"
    "coupled_blocked realization_source_first={}"
    by (simp_all add: realization_first_source_shape initial_source_coupling_def initial_finality_core_def)
  have sent_pair: "insert(0,23){(0,17)}={(0,17),(0,23)}" by auto
  have parent_prefix_state:
    "machine_state parent_prefix=(machine_state realization_parent_first)\<lparr>
      asset_owner:=(asset_owner(machine_state realization_parent_first))(17:=Some(0,23)),
      reservation_at:=(reservation_at(machine_state realization_parent_first))
        ((0,23):=Some((sample_confirmed_record 23)\<lparr>reservation_phase:=Source_Pending\<rparr>)),
      source_units:=(source_units(machine_state realization_parent_first))((0,17):=0),
      source_effects:=[sample_binding 17,sample_binding 23]\<rparr>"
    by (simp add: parent_prefix_def realization_parent_first_state sample_confirmed_record_def
      sample_data_defs realized.run_reservations.simps realized.reservation_step.simps
      realized.protocol_definitions record_observation_def commit_reservation_event_def
      record_credit_def credit_marker_def empty_message_state_def Let_def fun_eq_iff)
  have submitted_shape:
    "submitted=realization_source_first\<lparr>
      coupled_source:=run_controlled_source realization_source_commands(initial_controlled_source sample_balances),
      coupled_core:=(coupled_core realization_source_first)\<lparr>core_parent:=parent_prefix,core_epoch:=11\<rparr>,
      coupled_sent:={(0,17),(0,23)}\<rparr>"
    by (intro source_coupling_state.equality finality_core.equality;
      simp_all add: submitted_def realization_source_prefix_def coupling_prepare_def
        first_fields parent_prefix_def realization_source_commands_def realization_parent_first_state
        conservation_contexts_def realization_source_execution
        realized.run_reservations.simps realized.reservation_step.simps realized.protocol_definitions
        sample_data_defs realization_certificate_projections sample_statement_def
        sample_confirmed_record_def sent_pair Let_def)
  have submitted_fields:
    "core_parent(coupled_core submitted)=parent_prefix"
    "core_records(coupled_core submitted)=
      (\<lambda>_.None)((0,17):=Some(progress_terminal_record(linked_certificate 17)Confirmed_Decision))"
    "core_published(coupled_core submitted)={(0,17)}"
    "core_contexts(coupled_core submitted)=conservation_contexts"
    "core_regulatory(coupled_core submitted)=
      \<lparr>receiver_snapshot=sample_metadata ACTIVE,receiver_applied={}\<rparr>"
    "core_epoch(coupled_core submitted)=11"
    "coupled_source submitted=run_controlled_source realization_source_commands(initial_controlled_source sample_balances)"
    "coupled_receipts submitted=[linked_certificate 17]"
    "coupled_sent submitted={(0,17),(0,23)}"
    "coupled_blocked submitted={}"
    by (simp_all add: submitted_shape first_fields)
  have source_fact:
    "controlled_source_fact(coupled_source submitted)(0,23)=Some(sample_statement 23)"
    by (simp add: submitted_fields realization_source_commands_def linked_source_data
        sample_statement_def sample_binding_def example_binding_def)
  have source_fact_at_result:
    "controlled_source_fact(run_controlled_source realization_source_commands
      (initial_controlled_source sample_balances))(0,23)=Some(sample_statement 23)"
    using source_fact by (simp only: submitted_fields(7))
  have checked: "realized.certificate_ok(linked_certificate 23)"
    by (rule realization_checked_certificate) simp
  have evidence_inputs: "realized.terminal_evidence_inputs(linked_certificate 23)submitted"
    using checked
    by (simp add: realized.terminal_evidence_inputs_def submitted_fields source_fact source_fact_at_result parent_prefix_state
      realization_parent_first_state source_receipt_slot_available_def realization_certificate_projections
      sample_statement_def sample_binding_def example_binding_def progress_terminal_record_def)
  have evidence_kind: "kind_from_source(statement_status(certificate_statement(linked_certificate 23)))=
      Some Confirmed_Decision"
    by (simp add: realization_certificate_projections sample_statement_def)
  have distinct_certificates: "linked_certificate 23\<noteq>linked_certificate 17"
    by (simp add: linked_certificate_def)
  have prepared_shape:
    "prepared=submitted\<lparr>coupled_receipts:=[linked_certificate 17,linked_certificate 23],
      coupled_core:=progress_prepared_core(linked_certificate 23)Confirmed_Decision(coupled_core submitted)\<rparr>"
    using realized.terminal_evidence_program_records_and_publishes[OF evidence_inputs evidence_kind,
      where endpoint=2]
    by (simp only: prepared_def; simp add: issue_source_receipt_def source_receipt_slot_available_def
      submitted_fields source_fact source_fact_at_result realization_certificate_projections sample_statement_def
      sample_binding_def example_binding_def distinct_certificates)
  have publish_parent:
    "realized.publish_source_certificate(linked_certificate 23)parent_prefix=
      commit_reservation_event(Certificate_Event(linked_certificate 23))parent_prefix"
    using checked
    by (simp add: realized.publish_source_certificate_def parent_prefix_state
      realization_parent_first_state realization_certificate_projections sample_statement_def Let_def)
  have parent_decomposition:
    "realization_parent_second=fst(realized.reconcile_recorded_credit(sample_source_context ACTIVE)
      (realization_credit_request 23)0(\<lambda>_.0)
      (fst(realized.deliver_reserved_credit Bypass_Route example_context(realization_credit_request 23)
        (commit_reservation_event(Certificate_Event(linked_certificate 23))parent_prefix))))"
    by (simp only: realization_parent_second_def realization_parent_credit_word_def
      realized.reservation_run_append parent_prefix_def[symmetric]
      realized.run_reservations.simps realized.reservation_step.simps publish_parent)
  let ?tail = "[
    Coupling_Client True(Client_Protocol 2 0(Deliver_Intent Bypass_Route(realization_credit_request 23))),
    Coupling_Client True(Client_Publication(0,23)),
    Coupling_Client True(Client_Protocol 0 0(Reconcile_Intent(realization_credit_request 23)0[]))]"
  have tail_shape:
    "realized.run_source_coupling ?tail prepared=submitted\<lparr>
      coupled_receipts:=[linked_certificate 17,linked_certificate 23],
      coupled_core:=(coupled_core submitted)\<lparr>core_parent:=realization_parent_second,
        core_records:=(core_records(coupled_core submitted))
          ((0,23):=Some(progress_terminal_record(linked_certificate 23)Confirmed_Decision)),
        core_published:={(0,17),(0,23)},core_epoch:=16\<rparr>\<rparr>"
    by (intro source_coupling_state.equality finality_core.equality;
      simp_all add: prepared_shape progress_prepared_core_def parent_decomposition submitted_fields
        parent_prefix_state realization_parent_first_state source_fact source_fact_at_result conservation_contexts_def
        realization_credit_request_def
        realized.run_source_coupling.simps realized.source_coupling_step.simps
        realized.coupling_client_step_def realized.coupling_client_result.simps
        realized.execute_finality_client_def realized.finality_step_def realized.core_result.simps
        realized.invoke_protocol_def realized.intent_result.simps realized.publish_primary_def
        realized.reconcile_recorded_credit_def realized.deliver_reserved_credit_def
        realized.published_receive_expansion coupling_live_receipt_def
        current_lock_view_def exact_record_reference_def record_reference_def terminal_effect_completed_def
        lift_protocol_result_def vector_lookup_def record_observation_def commit_reservation_event_def
        record_credit_def credit_marker_def empty_message_state_def
        realized.credit_admissible_def realized.authenticated_request_def realization_checked_certificate
        sample_data_defs realization_certificate_projections sample_statement_def progress_terminal_record_def
        sample_confirmed_record_def sent_pair Let_def)
  have split: "realization_source_second=realized.run_source_coupling ?tail prepared"
    by (simp only: realization_source_second_def realization_credit_word_def
      terminal_finish_actions_def terminal_effect_actions_def realized.progress_source_run_append
      submitted_def[symmetric] prepared_def[symmetric] realization_certificate_projections
      realized.run_source_coupling.simps sample_statement_def source_statement.select_convs
      sample_binding_def example_binding_def transfer_binding.select_convs; simp)
  show ?thesis
    by (simp only: split tail_shape submitted_shape;
      intro source_coupling_state.equality finality_core.equality;
      simp_all add: first_fields)
qed

theorem realization_two_roots_are_an_actual_joint_prefix:
  "realization_source_second=realized.run_source_coupling
    (realization_credit_word 17@realization_credit_word 23)
    (initial_source_coupling sample_balances(sample_metadata ACTIVE)conservation_contexts) \<and>
    realized.source_coupling_invariant sample_balances realization_source_second"
proof -
  have execution: "realization_source_second=realized.run_source_coupling
    (realization_credit_word 17@realization_credit_word 23)
    (initial_source_coupling sample_balances(sample_metadata ACTIVE)conservation_contexts)"
    by (simp add: realization_source_second_def realization_source_first_def
      conservation_initial_def realized.progress_source_run_append)
  have invariant: "realized.source_coupling_invariant sample_balances realization_source_second"
    by (simp only: execution; rule realized.all_finite_joint_executions_have_source_provenance)
  show ?thesis by (rule conjI[OF execution invariant])
qed

theorem realization_two_roots_supply_the_actual_consumers:
  "core_parent(coupled_core realization_source_second)=realization_parent_second \<and>
    record_reference(coupled_core realization_source_second)0(sample_binding 17)Confirmed_Decision=
      Some(linked_certificate 17) \<and>
    record_reference(coupled_core realization_source_second)0(sample_binding 23)Confirmed_Decision=
      Some(linked_certificate 23) \<and>
    core_published(coupled_core realization_source_second)={(0,17),(0,23)} \<and>
    receiver_snapshot(core_regulatory(coupled_core realization_source_second))=sample_metadata ACTIVE \<and>
    credit_history(received_messages(machine_state realization_parent_second))=[sample_binding 17,sample_binding 23] \<and>
    funded_units(machine_state realization_parent_second)((0,17),(2,17,3))=5 \<and>
    funded_units(machine_state realization_parent_second)((0,23),(2,17,3))=5 \<and>
    boundary_effects(controlled_endpoint(coupled_source realization_source_second))=[sample_binding 17,sample_binding 23] \<and>
    controlled_returns(coupled_source realization_source_second)=[] \<and>
    boundary_units(controlled_endpoint(coupled_source realization_source_second))(0,17)=0"
  by (simp add: realization_second_source_shape realization_first_source_shape realization_parent_second_state
    realization_parent_first_state record_reference_def progress_terminal_record_def initial_finality_core_def
    realization_source_commands_def linked_source_data linked_certificate_def sample_statement_def
    record_credit_def empty_message_state_def Let_def)

section \<open>The Constructive Plan Consumed After a Real Descendant Prefix\<close>

definition realization_certificates :: "transfer_binding \<Rightarrow> source_certificate" where
  "realization_certificates root=linked_certificate(snd(binding_key root))"

definition realization_seed_effect :: descendant_effect where
  "realization_seed_effect=realization_effect(sample_binding 17)3 4 5"

definition realization_lineage_seed :: source_coupling_state where
  "realization_lineage_seed=realized.run_source_coupling
    (source_realization_word(linked_certificate 17)0 realization_seed_effect)realization_source_second"

lemma realization_second_parent_financial:
  "financial_history_agreement sample_balances realization_parent_second"
proof -
  note joint = conjunct2[OF realization_two_roots_are_an_actual_joint_prefix]
  note parts = joint[unfolded realized.source_coupling_invariant_def]
  have contract: "realized.reservation_contract sample_balances
      (core_parent(coupled_core realization_source_second))"
    by (rule conjunct1[OF conjunct2[OF parts]])
  have projection: "core_parent(coupled_core realization_source_second)=realization_parent_second"
    by (rule conjunct1[OF realization_two_roots_supply_the_actual_consumers])
  have parent_contract: "realized.reservation_contract sample_balances realization_parent_second"
    using contract by (simp only: projection)
  show ?thesis using parent_contract unfolding realized.reservation_contract_def by blast
qed

lemma realization_seed_parent_success:
  "snd(realization_result realization_certificates realization_seed_effect realization_parent_second)=Descendant_Executed"
proof -
  have credit: "sample_binding 17\<in>set(credit_history(received_messages(machine_state realization_parent_second)))"
    using realization_two_roots_supply_the_actual_consumers by simp
  note probe=actual_probe_reply_is_the_funding_threshold[OF realization_second_parent_financial credit,
    where sender=3 and recipient=4 and amount=5 and certificate="linked_certificate 17"]
  show ?thesis using probe realization_two_roots_supply_the_actual_consumers
    by (simp add: realization_result_def realization_certificates_def realization_seed_effect_def
      realization_effect_def sample_binding_def example_binding_def holder_account_def)
qed

lemma realization_seed_actual_step:
  "core_parent(coupled_core realization_lineage_seed)=
      fst(realization_result realization_certificates realization_seed_effect realization_parent_second) \<and>
    coupled_source realization_lineage_seed=coupled_source realization_source_second \<and>
    core_records(coupled_core realization_lineage_seed)=core_records(coupled_core realization_source_second) \<and>
    core_published(coupled_core realization_lineage_seed)=core_published(coupled_core realization_source_second) \<and>
    core_regulatory(coupled_core realization_lineage_seed)=core_regulatory(coupled_core realization_source_second)"
proof -
  have reference: "record_reference(coupled_core realization_source_second)0
    (lineage_root realization_seed_effect)Confirmed_Decision\<noteq>None"
    using realization_two_roots_supply_the_actual_consumers
    by (simp add: realization_seed_effect_def realization_effect_def)
  have published: "binding_key(lineage_root realization_seed_effect)\<in>core_published(coupled_core realization_source_second)"
    using realization_two_roots_supply_the_actual_consumers
    by (simp add: realization_seed_effect_def realization_effect_def sample_binding_def example_binding_def)
  have active: "get_reg_state(receiver_snapshot(core_regulatory(coupled_core realization_source_second)))
    (binding_destination(lineage_root realization_seed_effect))(binding_asset(lineage_root realization_seed_effect))=Some ACTIVE"
    using realization_two_roots_supply_the_actual_consumers
    by (simp add: realization_seed_effect_def realization_effect_def sample_binding_def example_binding_def
      sample_metadata_def get_reg_state_def get_asset_state_def)
  note step=realized.source_realization_one_step_is_the_actual_parent_result[OF reference published active,
    where certificate="linked_certificate 17"]
  show ?thesis using step realization_two_roots_supply_the_actual_consumers
    by (simp add: realization_lineage_seed_def realization_result_def realization_certificates_def
      source_realization_context_def source_realization_request_def realization_seed_effect_def
      realization_effect_def sample_binding_def example_binding_def)
qed

lemma realization_seed_state:
  "machine_state(core_parent(coupled_core realization_lineage_seed))=
    apply_reservation_event(Descendant_Event realization_seed_effect)(machine_state realization_parent_second)"
  using realization_seed_actual_step realization_result_commits[OF realization_seed_parent_success]
  by (simp add: realization_seed_effect_def realization_effect_def record_observation_def commit_reservation_event_def)

lemma realization_seed_funding:
  "funded_units(machine_state(core_parent(coupled_core realization_lineage_seed)))((0,17),(2,17,3))=0"
  "funded_units(machine_state(core_parent(coupled_core realization_lineage_seed)))((0,17),(2,17,4))=5"
  "funded_units(machine_state(core_parent(coupled_core realization_lineage_seed)))((0,23),(2,17,3))=5"
  "funded_units(machine_state(core_parent(coupled_core realization_lineage_seed)))((0,23),(2,17,4))=0"
  "destination_units(machine_state(core_parent(coupled_core realization_lineage_seed)))(2,17,3)=5"
  "destination_units(machine_state(core_parent(coupled_core realization_lineage_seed)))(2,17,4)=5"
  by (simp_all add: realization_seed_state realization_seed_effect_def realization_effect_def
    realization_parent_second_state realization_parent_first_state sample_binding_def example_binding_def
    holder_account_def Let_def)

lemma realization_seed_financial:
  "financial_history_agreement sample_balances(core_parent(coupled_core realization_lineage_seed))"
  using realization_result_financial[OF realization_second_parent_financial realization_seed_parent_success]
    realization_seed_actual_step by simp

definition realization_exchange_target :: "transfer_binding \<Rightarrow> nat \<Rightarrow> nat" where
  "realization_exchange_target root holder=
    (if (binding_key root=(0,17) \<and> holder=3) \<or> (binding_key root=(0,23) \<and> holder=4) then 5 else 0)"

definition realization_exchange_effects :: "descendant_effect list" where
  "realization_exchange_effects=[realization_effect(sample_binding 17)4 3 5,
    realization_effect(sample_binding 23)3 4 5]"

definition realization_exchange_finished :: source_coupling_state where
  "realization_exchange_finished=realized.run_source_coupling
    (source_realization_words realization_certificates(\<lambda>_.0)realization_exchange_effects)realization_lineage_seed"

lemma realization_exchange_is_the_constructed_plan:
  "realization_plan [sample_binding 17,sample_binding 23][3,4]
      (core_parent(coupled_core realization_lineage_seed))realization_exchange_target=realization_exchange_effects"
  by (simp add: realization_plan_def realization_plan_from_def realization_drain_def
    realization_distribute_def realization_move_def realization_units_def realization_seed_funding
    realization_exchange_target_def realization_exchange_effects_def sample_binding_def example_binding_def
    holder_account_def)

lemma realization_exchange_inputs:
  "\<forall>root\<in>set[sample_binding 17,sample_binding 23].
    root\<in>set(credit_history(received_messages(machine_state(core_parent(coupled_core realization_lineage_seed)))))"
  "distinct(map binding_key[sample_binding 17,sample_binding 23])"
  "distinct[3::nat,4]"
  "\<forall>root\<in>set[sample_binding 17,sample_binding 23].
    sum_list(map(realization_exchange_target root)[3,4])=
    sum_list(map(realization_units(core_parent(coupled_core realization_lineage_seed))root)[3,4])"
  "\<forall>root\<in>set[sample_binding 17,sample_binding 23].
    record_reference(coupled_core realization_lineage_seed)0 root Confirmed_Decision\<noteq>None"
  "\<forall>root\<in>set[sample_binding 17,sample_binding 23].
    binding_key root\<in>core_published(coupled_core realization_lineage_seed)"
  "\<forall>root\<in>set[sample_binding 17,sample_binding 23].
    get_reg_state(receiver_snapshot(core_regulatory(coupled_core realization_lineage_seed)))
      (binding_destination root)(binding_asset root)=Some ACTIVE"
proof -
  have message_frame:
    "received_messages(machine_state(core_parent(coupled_core realization_lineage_seed)))=
      received_messages(machine_state realization_parent_second)"
    by (simp add: realization_seed_state Let_def)
  have credits:
    "credit_history(received_messages(machine_state realization_parent_second))=[sample_binding 17,sample_binding 23]"
    using realization_two_roots_supply_the_actual_consumers by blast
  show "\<forall>root\<in>set[sample_binding 17,sample_binding 23].
    root\<in>set(credit_history(received_messages(machine_state(core_parent(coupled_core realization_lineage_seed)))))"
    by (simp add: message_frame credits)
  show "distinct(map binding_key[sample_binding 17,sample_binding 23])"
    by (simp add: sample_binding_def example_binding_def)
  show "distinct[3::nat,4]" by simp
  show "\<forall>root\<in>set[sample_binding 17,sample_binding 23].
    sum_list(map(realization_exchange_target root)[3,4])=
    sum_list(map(realization_units(core_parent(coupled_core realization_lineage_seed))root)[3,4])"
    by (simp add: realization_units_def realization_exchange_target_def
      sample_binding_def example_binding_def holder_account_def realization_seed_funding)
  have records_frame:
    "core_records(coupled_core realization_lineage_seed)=core_records(coupled_core realization_source_second)"
    using realization_seed_actual_step by blast
  have reference_frame: "\<And>root.
    record_reference(coupled_core realization_lineage_seed)0 root Confirmed_Decision=
      record_reference(coupled_core realization_source_second)0 root Confirmed_Decision"
    by (simp only: record_reference_def records_frame)
  have first_reference:
    "record_reference(coupled_core realization_source_second)0(sample_binding 17)Confirmed_Decision=
      Some(linked_certificate 17)"
    and second_reference:
    "record_reference(coupled_core realization_source_second)0(sample_binding 23)Confirmed_Decision=
      Some(linked_certificate 23)"
    using realization_two_roots_supply_the_actual_consumers by blast+
  show "\<forall>root\<in>set[sample_binding 17,sample_binding 23].
    record_reference(coupled_core realization_lineage_seed)0 root Confirmed_Decision\<noteq>None"
    by (simp add: reference_frame first_reference second_reference)
  have publication_frame:
    "core_published(coupled_core realization_lineage_seed)=core_published(coupled_core realization_source_second)"
    using realization_seed_actual_step by blast
  have publications:
    "core_published(coupled_core realization_source_second)={(0,17),(0,23)}"
    using realization_two_roots_supply_the_actual_consumers by blast
  show "\<forall>root\<in>set[sample_binding 17,sample_binding 23].
    binding_key root\<in>core_published(coupled_core realization_lineage_seed)"
    by (simp only: publication_frame publications;
      simp add: sample_binding_def example_binding_def)
  have regulatory_frame:
    "core_regulatory(coupled_core realization_lineage_seed)=core_regulatory(coupled_core realization_source_second)"
    using realization_seed_actual_step by blast
  have snapshot:
    "receiver_snapshot(core_regulatory(coupled_core realization_source_second))=sample_metadata ACTIVE"
    using realization_two_roots_supply_the_actual_consumers by blast
  show "\<forall>root\<in>set[sample_binding 17,sample_binding 23].
    get_reg_state(receiver_snapshot(core_regulatory(coupled_core realization_lineage_seed)))
      (binding_destination root)(binding_asset root)=Some ACTIVE"
    by (simp only: regulatory_frame snapshot;
      simp add: sample_binding_def example_binding_def sample_metadata_def get_reg_state_def get_asset_state_def)
qed

theorem actual_two_root_plan_activates_every_source_dispatch:
  "(\<forall>root\<in>set[sample_binding 17,sample_binding 23]. \<forall>holder\<in>set[3,4].
      realization_units(core_parent(coupled_core realization_exchange_finished))root holder=
        realization_exchange_target root holder) \<and>
    coupled_source realization_exchange_finished=coupled_source realization_lineage_seed \<and>
    (\<forall>i<length realization_exchange_effects.
      realized.source_realization_reply realization_certificates(\<lambda>_.0)(realization_exchange_effects!i)
        (realized.run_source_coupling(source_realization_words realization_certificates(\<lambda>_.0)
          (take i realization_exchange_effects))realization_lineage_seed)=
        Coupling_Client_Reply(Protocol_Response Descendant_Executed))"
  using realized.source_realization_constructive_plan_uses_the_actual_dispatcher
    [OF realization_seed_financial realization_exchange_inputs(1,2,3,4,5,6,7),
      where certificates=realization_certificates]
  by (simp add: realization_exchange_is_the_constructed_plan realization_exchange_finished_def)

lemma realization_exchange_parent_projection:
  "core_parent(coupled_core realization_exchange_finished)=
    run_realization realization_certificates realization_exchange_effects
      (core_parent(coupled_core realization_lineage_seed))"
proof -
  have references: "\<forall>e\<in>set realization_exchange_effects.
    record_reference(coupled_core realization_lineage_seed)0(lineage_root e)Confirmed_Decision\<noteq>None"
    using realization_exchange_inputs(5) by (simp add: realization_exchange_effects_def realization_effect_def)
  have published: "\<forall>e\<in>set realization_exchange_effects.
    binding_key(lineage_root e)\<in>core_published(coupled_core realization_lineage_seed)"
    using realization_exchange_inputs(6) by (simp add: realization_exchange_effects_def realization_effect_def)
  have active: "\<forall>e\<in>set realization_exchange_effects.
    get_reg_state(receiver_snapshot(core_regulatory(coupled_core realization_lineage_seed)))
      (binding_destination(lineage_root e))(binding_asset(lineage_root e))=Some ACTIVE"
    using realization_exchange_inputs(7) by (simp add: realization_exchange_effects_def realization_effect_def)
  show ?thesis using realized.source_realization_finite_word_projection[OF references published active,
    where certificates=realization_certificates]
    by (simp add: realization_exchange_finished_def)
qed

lemma realization_exchange_parent_success:
  "realization_succeeds realization_certificates realization_exchange_effects
    (core_parent(coupled_core realization_lineage_seed))"
proof -
  have initial: "\<forall>root\<in>set[sample_binding 17,sample_binding 23]. \<forall>holder\<in>set[3,4].
    realization_units(core_parent(coupled_core realization_lineage_seed))root holder=
    realization_units(core_parent(coupled_core realization_lineage_seed))root holder" by simp
  note construction=realization_plan_from_is_constructive
    [OF realization_seed_financial realization_exchange_inputs(1,2,3) initial realization_exchange_inputs(4),
      where certificates=realization_certificates]
  show ?thesis using construction realization_exchange_is_the_constructed_plan
    by (simp add: realization_plan_def)
qed

lemma realization_exchange_state:
  "machine_state(core_parent(coupled_core realization_exchange_finished))=
    apply_reservation_event(Descendant_Event(realization_effect(sample_binding 23)3 4 5))
      (apply_reservation_event(Descendant_Event(realization_effect(sample_binding 17)4 3 5))
        (machine_state(core_parent(coupled_core realization_lineage_seed))))"
proof -
  let ?m="core_parent(coupled_core realization_lineage_seed)"
  let ?a="realization_effect(sample_binding 17)4 3 5"
  let ?b="realization_effect(sample_binding 23)3 4 5"
  have first: "snd(realization_result realization_certificates ?a ?m)=Descendant_Executed"
    and second: "snd(realization_result realization_certificates ?b
      (fst(realization_result realization_certificates ?a ?m)))=Descendant_Executed"
    using realization_exchange_parent_success by (simp_all add: realization_exchange_effects_def)
  have first_state: "machine_state(fst(realization_result realization_certificates ?a ?m))=
      apply_reservation_event(Descendant_Event ?a)(machine_state ?m)"
    by (simp only: realization_result_commits[OF first];
      simp add: realization_effect_def record_observation_def commit_reservation_event_def)
  have second_state: "machine_state(fst(realization_result realization_certificates ?b
      (fst(realization_result realization_certificates ?a ?m))))=
      apply_reservation_event(Descendant_Event ?b)
        (machine_state(fst(realization_result realization_certificates ?a ?m)))"
    by (simp only: realization_result_commits[OF second];
      simp add: realization_effect_def record_observation_def commit_reservation_event_def)
  show ?thesis by (simp only: realization_exchange_parent_projection realization_exchange_effects_def
      run_realization.simps second_state first_state)
qed

theorem actual_source_realization_preserves_erased_state_and_source_pool:
  "erase_lineage_state(core_parent(coupled_core realization_exchange_finished))=
      erase_lineage_state(core_parent(coupled_core realization_lineage_seed)) \<and>
    coupled_source realization_exchange_finished=coupled_source realization_source_second \<and>
    boundary_effects(controlled_endpoint(coupled_source realization_exchange_finished))=
      [sample_binding 17,sample_binding 23] \<and>
    controlled_returns(coupled_source realization_exchange_finished)=[] \<and>
    boundary_units(controlled_endpoint(coupled_source realization_exchange_finished))(0,17)=0 \<and>
    destination_units(machine_state(core_parent(coupled_core realization_exchange_finished)))=
      destination_units(machine_state(core_parent(coupled_core realization_lineage_seed)))"
proof -
  have pooled: "destination_units(machine_state(core_parent(coupled_core realization_exchange_finished)))=
    destination_units(machine_state(core_parent(coupled_core realization_lineage_seed)))"
    by (rule ext) (auto simp: realization_exchange_state realization_effect_def
      sample_binding_def example_binding_def holder_account_def realization_seed_funding Let_def)
  have erased: "erase_lineage_state(core_parent(coupled_core realization_exchange_finished))=
    erase_lineage_state(core_parent(coupled_core realization_lineage_seed))"
    by (rule reservation_state.equality)
      (simp_all add: erase_lineage_state_def realization_exchange_state realization_effect_def
        sample_binding_def example_binding_def holder_account_def realization_seed_funding Let_def fun_eq_iff)
  have exchange_source: "coupled_source realization_exchange_finished=coupled_source realization_lineage_seed"
    using actual_two_root_plan_activates_every_source_dispatch by blast
  have seed_source: "coupled_source realization_lineage_seed=coupled_source realization_source_second"
    using realization_seed_actual_step by blast
  have source: "coupled_source realization_exchange_finished=coupled_source realization_source_second"
    by (rule trans[OF exchange_source seed_source])
  have effects: "boundary_effects(controlled_endpoint(coupled_source realization_source_second))=
      [sample_binding 17,sample_binding 23]"
    and returns: "controlled_returns(coupled_source realization_source_second)=[]"
    and units: "boundary_units(controlled_endpoint(coupled_source realization_source_second))(0,17)=0"
    using realization_two_roots_supply_the_actual_consumers by blast+
  show ?thesis by (simp only: source effects returns units erased pooled HOL.simp_thms)
qed

theorem actual_realization_has_no_new_source_credit_or_return:
  "source_units(machine_state(core_parent(coupled_core realization_exchange_finished)))=
      source_units(machine_state(core_parent(coupled_core realization_lineage_seed))) \<and>
    source_effects(machine_state(core_parent(coupled_core realization_exchange_finished)))=
      source_effects(machine_state(core_parent(coupled_core realization_lineage_seed))) \<and>
    received_messages(machine_state(core_parent(coupled_core realization_exchange_finished)))=
      received_messages(machine_state(core_parent(coupled_core realization_lineage_seed))) \<and>
    reservation_at(machine_state(core_parent(coupled_core realization_exchange_finished)))=
      reservation_at(machine_state(core_parent(coupled_core realization_lineage_seed)))"
  by (simp add: realization_exchange_state realization_effect_def Let_def)

text \<open>The receipt interpretation reuses the existing controlled-source
  producer theorem with the two finalized roots as its actual input. Each
  source effect, mirror, receipt, terminal decision, credit, publication and
  reservation reconciliation is an action of the existing joint protocol.
  The generic descendant translation executes a stored-context environment
  update before each client request and consumes the unchanged confirmed
  record, primary marker and current regulatory snapshot. Its equality is
  with the actual parent result, including rejection; no success oracle is
  assumed. Physical adapter authenticity and current-context provenance retain
  the existing external implementation boundary.\<close>

end
