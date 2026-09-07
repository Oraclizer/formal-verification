(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Policy_Cases
  imports Reservation_Lineage Reservation_Return_History
begin

section \<open>Current Regulatory Policy and Permanent Return Closure\<close>

lemma current_regulatory_freeze_blocks_old_credit_use:
  "snd(execute_descendant(sample_context FROZEN)(spend_request 17 4 1)(sample_binding 17)3 4 1
      sample_credited)=Request_Rejected \<and>
   snd(execute_descendant(sample_context ACTIVE)(spend_request 17 4 1)(sample_binding 17)3 4 1
      sample_credited)=Descendant_Executed"
  by (simp add: spend_request_def execute_descendant_def descendant_binding_def sample_credited_state staged_trace_defs)

definition descendant_without_policy_admission where
  "descendant_without_policy_admission c r root sender recipient amount m =
    (let operation=binding_operation(request_binding r) in
     if root\<in>set(credit_history(received_messages(machine_state m))) \<and>
        request_binding r=descendant_binding root recipient amount operation \<and>
        (operation=Ordinary_Transfer_Effect \<or> (\<exists>kind. operation=Enforcement_Transfer_Effect kind)) \<and>
        context_endpoint(lock_authority c)=binding_destination root \<and> 0<amount \<and>
        (request_caller r,binding_key root,sender,recipient,amount,operation)\<in>lock_spend_permissions c \<and>
        amount\<le>destination_units(machine_state m)(holder_account root sender) \<and>
        amount\<le>funded_units(machine_state m)(binding_key root,holder_account root sender)
     then record_observation r Descendant_Executed(commit_reservation_event(Descendant_Event
       \<lparr>lineage_root=root,lineage_from=sender,lineage_to=recipient,lineage_amount=amount,
         lineage_operation=operation,lineage_caller=request_caller r,
         lineage_authority_epoch=request_authority_epoch r,lineage_version=request_version r\<rparr>)m)
     else record_observation r Request_Rejected m)"

lemma omitted_policy_admission_spends_while_frozen:
  "snd(descendant_without_policy_admission(sample_context FROZEN)(spend_request 17 4 1)
    (sample_binding 17)3 4 1 sample_credited)=Descendant_Executed \<and>
   funded_units(machine_state(fst(descendant_without_policy_admission(sample_context FROZEN)
    (spend_request 17 4 1)(sample_binding 17)3 4 1 sample_credited)))((0,17),(2,17,4))=1"
  by (simp add: descendant_without_policy_admission_def spend_request_def descendant_binding_def
      sample_credited_state staged_trace_defs)

definition return_without_closure :: "transfer_binding \<Rightarrow> reservation_machine \<Rightarrow> reservation_machine" where
  "return_without_closure b m =
    (let committed=commit_reservation_event(Return_Event b)m in
      committed\<lparr>machine_state:=(machine_state committed)\<lparr>
        reservation_at:=reservation_at(machine_state m),asset_owner:=asset_owner(machine_state m)\<rparr>\<rparr>)"

context source_attestation
begin

definition release_without_closing_record where
  "release_without_closing_record c r g versions m =
    (if owns_recorded_reservation c r g versions(machine_state m) \<and>
        phase_at(machine_state m)(binding_key(request_binding r))=Some Source_Pending \<and>
        reversed_source_evidence(lock_authority c)r(machine_state m)
     then record_observation r Reservation_Released(return_without_closure(request_binding r)m)
     else record_observation r Request_Rejected m)"

end

lemma normal_return_cannot_execute_twice:
  "snd(sample.release_to_source(sample_source_context ACTIVE)(sample_request 22)0(\<lambda>_.0)
    (fst(sample.release_to_source(sample_source_context ACTIVE)(sample_request 22)0(\<lambda>_.0)
      sample_return_ready)))=Request_Rejected"
  by (simp add: sample_return_ready_def sample_data_defs sample_auth_defs sample.protocol_definitions
      sample.run_reservations.simps sample.reservation_step.simps record_observation_def
      commit_reservation_event_def Let_def)

lemma omitting_the_closure_mechanism_returns_twice:
  "source_units(machine_state(fst(sample.release_without_closing_record(sample_source_context ACTIVE)
    (sample_request 22)0(\<lambda>_.0)(fst(sample.release_without_closing_record(sample_source_context ACTIVE)
      (sample_request 22)0(\<lambda>_.0)sample_return_ready)))))(0,22)=10"
  by (simp add: sample.release_without_closing_record_def return_without_closure_def sample_return_ready_def
      sample_data_defs sample_auth_defs sample.protocol_definitions sample.run_reservations.simps
      sample.reservation_step.simps record_observation_def commit_reservation_event_def Let_def)

text \<open>The policy mutation removes the metadata-permission consumer,
  whose normal branch also checks current authorization. The chosen caller
  otherwise has current permission; the relevant regulatory state is Frozen.
  The return mutation omits the coupled phase-and-owner closure mechanism,
  retaining both fields. It is explicitly a two-field effect mutation, not a
  claim that omitting either field alone defeats all remaining guards.\<close>

end
