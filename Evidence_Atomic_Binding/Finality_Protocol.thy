(* SPDX-License-Identifier: BSD-3-Clause *)
theory Finality_Protocol
  imports Finality_Types
begin

definition lift_protocol_result :: "reservation_machine \<times> reservation_reply
  \<Rightarrow> reservation_machine \<times> finality_reply" where
  "lift_protocol_result result=(fst result,Protocol_Response(snd result))"

definition reject_protocol_intent :: "protocol_intent \<Rightarrow> finality_core \<Rightarrow> finality_core" where
  "reject_protocol_intent intent s=(case intent_request intent of None \<Rightarrow> s
    | Some r \<Rightarrow> s\<lparr>core_parent:=fst(record_observation r Request_Rejected(core_parent s))\<rparr>)"

definition source_origin_present :: "source_certificate \<Rightarrow> finality_core \<Rightarrow> bool" where
  "source_origin_present cert s=(let b=statement_binding(certificate_statement cert) in
    case binding_operation b of
      Destination_Credit \<Rightarrow> 0<binding_amount b \<and> b\<in>set(source_effects(machine_state(core_parent s)))
    | Regulatory_State_Effect action \<Rightarrow> statement_status(certificate_statement cert)=Finalized
    | _ \<Rightarrow> False)"

fun terminal_intent_guard :: "finality_core \<Rightarrow> nat \<Rightarrow> protocol_intent \<Rightarrow> bool" where
  "terminal_intent_guard s index(Certificate_Intent cert)=
    (case kind_from_source(statement_status(certificate_statement cert)) of None \<Rightarrow> False
     | Some kind \<Rightarrow> exact_record_reference s index(statement_binding(certificate_statement cert))kind cert)"
| "terminal_intent_guard s index(Deliver_Intent route r)=
    exact_record_reference s index(request_binding r)Confirmed_Decision(request_certificate r)"
| "terminal_intent_guard s index(Return_Intent r g versions)=
    exact_record_reference s index(request_binding r)Reversed_Decision(request_certificate r)"
| "terminal_intent_guard s index(Reconcile_Intent r g versions)=
    exact_record_reference s index(request_binding r)Confirmed_Decision(request_certificate r)"
| "terminal_intent_guard s index(Descendant_Intent r root sender recipient amount)=
    (record_reference s index root Confirmed_Decision\<noteq>None \<and> binding_key root\<in>core_published s)"
| "terminal_intent_guard s index(Data_Read_Intent r)=
    (case core_records s(binding_key(request_binding r)) of None \<Rightarrow> True
     | Some record \<Rightarrow> exact_record_reference s index(request_binding r)(terminal_kind record)(request_certificate r))"
| "terminal_intent_guard s index _=True"

definition terminal_effect_completed :: "finality_core \<Rightarrow> terminal_record \<Rightarrow> bool" where
  "terminal_effect_completed s record=(let b=terminal_binding record in
    case terminal_kind record of
      Confirmed_Decision \<Rightarrow>
        (case binding_operation b of
           Destination_Credit \<Rightarrow> b\<in>set(credit_history(received_messages(machine_state(core_parent s))))
         | Regulatory_State_Effect action \<Rightarrow> binding_key b\<in>receiver_applied(core_regulatory s)
         | _ \<Rightarrow> False)
    | Reversed_Decision \<Rightarrow>
        binding_is_registered(machine_state(core_parent s))b \<and>
        phase_at(machine_state(core_parent s))(binding_key b)=Some Source_Returned)"

context source_attestation
begin

fun intent_result :: "lock_context \<Rightarrow> protocol_intent \<Rightarrow> reservation_machine
  \<Rightarrow> reservation_machine \<times> finality_reply" where
  "intent_result c(Reserve_Intent r versions duration)m=lift_protocol_result(acquire_reservation c r(vector_lookup versions)duration m)"
| "intent_result c(Dispatch_Intent r g versions)m=lift_protocol_result(dispatch_source c r g(vector_lookup versions)m)"
| "intent_result c(Source_Intent r g versions)m=lift_protocol_result(execute_source_effect c r g(vector_lookup versions)m)"
| "intent_result c(Cancel_Intent r g versions)m=lift_protocol_result(cancel_before_dispatch c r g(vector_lookup versions)m)"
| "intent_result c(Fence_Intent r g versions)m=lift_protocol_result(fence_unexecuted_source c r g(vector_lookup versions)m)"
| "intent_result c(Reassign_Intent r duration)m=lift_protocol_result(reassign_worker c r duration m)"
| "intent_result c(Write_Intent r g versions value)m=lift_protocol_result(write_asset_data c r g(vector_lookup versions)value m)"
| "intent_result c(Time_Intent elapsed)m=(advance_reservation_time elapsed m,Internal_Completed)"
| "intent_result c(Certificate_Intent cert)m=(publish_source_certificate cert m,Internal_Completed)"
| "intent_result c(Deliver_Intent route r)m=lift_protocol_result(deliver_reserved_credit route(lock_authority c)r m)"
| "intent_result c(Return_Intent r g versions)m=lift_protocol_result(release_to_source c r g(vector_lookup versions)m)"
| "intent_result c(Reconcile_Intent r g versions)m=lift_protocol_result(reconcile_recorded_credit c r g(vector_lookup versions)m)"
| "intent_result c(Descendant_Intent r root sender recipient amount)m=lift_protocol_result(execute_descendant c r root sender recipient amount m)"
| "intent_result c(Data_Read_Intent r)m=lift_protocol_result(read_source_data c r m)"

lemma intent_result_is_actual_parent_step:
  "fst(intent_result c intent m)=reservation_step balances(parent_action c intent)m"
  by (cases intent) (simp_all add: lift_protocol_result_def)

definition record_terminal :: "source_certificate \<Rightarrow> finality_core
  \<Rightarrow> finality_core \<times> finality_reply" where
  "record_terminal cert s=(let b=statement_binding(certificate_statement cert) in
    if \<not>certificate_ok cert \<or> \<not>source_origin_present cert s then (s,Finality_Rejected)
    else case kind_from_source(statement_status(certificate_statement cert)) of
      None \<Rightarrow> (s,Finality_Rejected)
    | Some kind \<Rightarrow>
      (case core_records s(binding_key b) of
        None \<Rightarrow> (s\<lparr>core_records:=(core_records s)(binding_key b:=Some
          \<lparr>terminal_binding=b,terminal_kind=kind,terminal_evidence=[cert]\<rparr>)\<rparr>,Terminal_Recorded)
      | Some record \<Rightarrow>
        if terminal_binding record=b \<and> terminal_kind record=kind
        then (s\<lparr>core_records:=(core_records s)(binding_key b:=Some
          (record\<lparr>terminal_evidence:=if cert\<in>set(terminal_evidence record)
            then terminal_evidence record else terminal_evidence record@[cert]\<rparr>))\<rparr>,Evidence_Refreshed)
        else (s,Finality_Rejected)))"

definition invoke_protocol :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> protocol_intent
  \<Rightarrow> finality_core \<Rightarrow> finality_core \<times> finality_reply" where
  "invoke_protocol endpoint epoch index intent s=
    (if epoch=core_epoch s \<and> terminal_intent_guard s index intent
     then let result=intent_result(current_lock_view s endpoint)intent(core_parent s)
       in (s\<lparr>core_parent:=fst result\<rparr>,snd result)
     else (reject_protocol_intent intent s,Finality_Rejected))"

definition invoke_regulatory :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> execution_request
  \<Rightarrow> finality_core \<Rightarrow> finality_core \<times> finality_reply" where
  "invoke_regulatory endpoint epoch index r s=
    (if epoch\<noteq>core_epoch s \<or>
       \<not>exact_record_reference s index(request_binding r)Confirmed_Decision(request_certificate r)
     then (s,Finality_Rejected)
     else case apply_regulatory_message(lock_authority(current_lock_view s endpoint))r(core_regulatory s) of
       None \<Rightarrow> (s,Finality_Rejected)
     | Some next \<Rightarrow> (s\<lparr>core_regulatory:=next\<rparr>,Regulatory_Applied))"

definition publish_primary :: "source_key \<Rightarrow> finality_core \<Rightarrow> finality_core \<times> finality_reply" where
  "publish_primary key s=(case core_records s key of None \<Rightarrow> (s,Finality_Rejected)
    | Some record \<Rightarrow>
      if terminal_effect_completed s record
      then (s\<lparr>core_published:=insert key(core_published s)\<rparr>,Primary_Published)
      else (s,Finality_Rejected))"

fun core_result :: "finality_operation \<Rightarrow> finality_core \<Rightarrow> finality_core \<times> finality_reply" where
  "core_result(Record_Terminal cert)s=record_terminal cert s"
| "core_result(Invoke_Protocol endpoint epoch index intent)s=invoke_protocol endpoint epoch index intent s"
| "core_result(Invoke_Regulatory endpoint epoch index r)s=invoke_regulatory endpoint epoch index r s"
| "core_result(Publish_Primary key)s=publish_primary key s"
| "core_result(Install_Context endpoint c)s=
    (if context_endpoint(lock_authority c)=endpoint
     then (s\<lparr>core_contexts:=(core_contexts s)(endpoint:=c)\<rparr>,Context_Installed)
     else (s,Finality_Rejected))"

definition finality_step :: "finality_operation \<Rightarrow> finality_core \<Rightarrow> finality_core" where
  "finality_step action s=(fst(core_result action s))\<lparr>core_epoch:=Suc(core_epoch s)\<rparr>"

fun run_finality :: "finality_operation list \<Rightarrow> finality_core \<Rightarrow> finality_core" where
  "run_finality [] s=s"
| "run_finality(action#rest)s=run_finality rest(finality_step action s)"

lemma finality_epoch_advances [simp]: "core_epoch(finality_step action s)=Suc(core_epoch s)"
  by (simp add: finality_step_def)

lemma finality_run_append:
  "run_finality(first@second)s=run_finality second(run_finality first s)"
  by (induction first arbitrary:s) auto

lemma observation_keeps_reservation_contract:
  "reservation_contract balances(fst(record_observation r reply m))=reservation_contract balances m"
  unfolding reservation_contract_def record_observation_def journal_agreement_def
    financial_history_agreement_def return_history_agreement_def
  by simp

lemma rejected_intent_keeps_reservation_contract:
  "reservation_contract balances(core_parent(reject_protocol_intent intent s))=
    reservation_contract balances(core_parent s)"
  by (simp add: reject_protocol_intent_def observation_keeps_reservation_contract split: option.splits)

theorem protocol_invocation_preserves_parent_contract:
  assumes "reservation_contract balances(core_parent s)"
  shows "reservation_contract balances(core_parent(fst(invoke_protocol endpoint epoch index intent s)))"
proof -
  have actual: "reservation_contract balances(fst(intent_result(current_lock_view s endpoint)intent(core_parent s)))"
    by (subst intent_result_is_actual_parent_step[where balances=balances],
        rule actual_step_preserves_reservation_contract[OF assms])
  show ?thesis using actual assms
    by (simp add: invoke_protocol_def rejected_intent_keeps_reservation_contract Let_def)
qed

theorem finality_step_preserves_parent_contract:
  assumes "reservation_contract balances(core_parent s)"
  shows "reservation_contract balances(core_parent(finality_step action s))"
  using assms
  by (cases action)
    (auto simp: finality_step_def record_terminal_def publish_primary_def invoke_regulatory_def
      Let_def intro: protocol_invocation_preserves_parent_contract
      split: option.splits if_splits)

theorem finite_finality_preserves_parent_contract:
  "reservation_contract balances(core_parent s) \<Longrightarrow>
   reservation_contract balances(core_parent(run_finality actions s))"
  by (induction actions arbitrary:s) (auto intro: finality_step_preserves_parent_contract)

theorem finality_supplies_actual_reservation_contract:
  "reservation_contract balances(core_parent(run_finality actions(initial_finality_core balances regulatory contexts)))"
  by (rule finite_finality_preserves_parent_contract)
    (simp add: initial_finality_core_def initial_reservation_contract)

theorem finality_preserves_source_allocation:
  fixes actions :: "finality_operation list" and balances :: "source_account \<Rightarrow> nat"
    and regulatory :: global_state and contexts :: "nat \<Rightarrow> lock_context"
  defines "s \<equiv> run_finality actions(initial_finality_core balances regulatory contexts)"
  shows "int(source_units(machine_state(core_parent s))pool)+unresolved_pool_mass(machine_state(core_parent s))pool+
    destination_pool_funding(machine_state(core_parent s))pool=int(balances pool)"
  by (rule provider_preserves_source_allocation)
    (simp add: s_def finality_supplies_actual_reservation_contract)

text \<open>All source, reservation, credit, return and descendant effects use
  the existing protocol operations. Extra terminal guards constrain their
  provenance and publication without changing the parent's meaning. Context
  replacement is an authenticated environmental input to the logical authority.
  No client-supplied policy snapshot is substituted for the current view.
  Repeated invocations and lost responses require the durable call protocol;
  these core operations alone do not identify two calls as the same request.\<close>

end

end
