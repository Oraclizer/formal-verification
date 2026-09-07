(* SPDX-License-Identifier: BSD-3-Clause *)
theory Funding_Guard_Controls
  imports Source_Realization_Link
begin

section \<open>The Exact Spend Permission in a Generated Source Execution\<close>

definition execute_without_exact_spend_guard :: "lock_context \<Rightarrow> execution_request \<Rightarrow> transfer_binding
  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> reservation_machine \<Rightarrow>
  reservation_machine \<times> reservation_reply" where
  "execute_without_exact_spend_guard c r root sender recipient amount m =
    (let operation=binding_operation(request_binding r) in
     if root\<in>set(credit_history(received_messages(machine_state m))) \<and>
        request_binding r=descendant_binding root recipient amount operation \<and>
        (operation=Ordinary_Transfer_Effect \<or> (\<exists>kind. operation=Enforcement_Transfer_Effect kind)) \<and>
        context_endpoint(lock_authority c)=binding_destination root \<and>
        metadata_permission c r (binding_destination root) \<and> 0<amount \<and>
        amount\<le>destination_units(machine_state m)(holder_account root sender) \<and>
        amount\<le>funded_units(machine_state m)(binding_key root,holder_account root sender)
     then record_observation r Descendant_Executed(commit_reservation_event(Descendant_Event
       \<lparr>lineage_root=root,lineage_from=sender,lineage_to=recipient,lineage_amount=amount,
         lineage_operation=operation,lineage_caller=request_caller r,
         lineage_authority_epoch=request_authority_epoch r,lineage_version=request_version r\<rparr>)m)
     else record_observation r Request_Rejected m)"


lemma removing_exact_spend_matches_the_granted_probe:
  "execute_without_exact_spend_guard
      ((funding_probe_context root sender recipient amount)\<lparr>lock_spend_permissions:={}\<rparr>)
      (funding_probe_request certificate root recipient amount) root sender recipient amount machine=
    execute_descendant (funding_probe_context root sender recipient amount)
      (funding_probe_request certificate root recipient amount) root sender recipient amount machine"
proof -
  have metadata:
    "metadata_permission ((funding_probe_context root sender recipient amount)\<lparr>lock_spend_permissions:={}\<rparr>)
      (funding_probe_request certificate root recipient amount)(binding_destination root)=
      metadata_permission (funding_probe_context root sender recipient amount)
        (funding_probe_request certificate root recipient amount)(binding_destination root)"
    by (simp add: metadata_permission_def cong: option.case_cong message_operation.case_cong)
  have grant:
    "(request_caller(funding_probe_request certificate root recipient amount),binding_key root,sender,recipient,amount,
      binding_operation(request_binding(funding_probe_request certificate root recipient amount)))\<in>
        lock_spend_permissions(funding_probe_context root sender recipient amount)"
    by (simp add: funding_probe_context_def funding_probe_request_def descendant_binding_def)
  show ?thesis
    by (simp add: execute_without_exact_spend_guard_def execute_descendant_def Let_def metadata grant)
qed

abbreviation funding_control_context :: lock_context where
  "funding_control_context \<equiv> funding_probe_context(sample_binding 17)3 4 5"

abbreviation funding_control_request :: execution_request where
  "funding_control_request \<equiv>
    funding_probe_request(realization_certificates(sample_binding 17))(sample_binding 17)4 5"

lemma funding_control_is_the_actual_source_seed:
  "execute_descendant funding_control_context funding_control_request (sample_binding 17)3 4 5
    realization_parent_second=realization_result realization_certificates realization_seed_effect realization_parent_second"
  by (simp add: realization_result_def realization_seed_effect_def realization_effect_def)

theorem exact_spend_removal_changes_a_source_generated_execution:
  "snd(execute_descendant (funding_control_context\<lparr>lock_spend_permissions:={}\<rparr>)
      funding_control_request(sample_binding 17)3 4 5 realization_parent_second)=Request_Rejected \<and>
    snd(execute_without_exact_spend_guard (funding_control_context\<lparr>lock_spend_permissions:={}\<rparr>)
      funding_control_request(sample_binding 17)3 4 5 realization_parent_second)=Descendant_Executed \<and>
    funded_units(machine_state(fst(execute_without_exact_spend_guard
      (funding_control_context\<lparr>lock_spend_permissions:={}\<rparr>)funding_control_request
      (sample_binding 17)3 4 5 realization_parent_second)))((0,17),(2,17,4))=5 \<and>
    funded_units(machine_state(fst(execute_descendant
      (funding_control_context\<lparr>lock_spend_permissions:={}\<rparr>)funding_control_request
      (sample_binding 17)3 4 5 realization_parent_second)))((0,17),(2,17,4))=0"
proof -
  have mutant: "execute_without_exact_spend_guard
      (funding_control_context\<lparr>lock_spend_permissions:={}\<rparr>)funding_control_request
      (sample_binding 17)3 4 5 realization_parent_second=
      realization_result realization_certificates realization_seed_effect realization_parent_second"
    by (simp only: removing_exact_spend_matches_the_granted_probe funding_control_is_the_actual_source_seed)
  have rejected: "snd(execute_descendant (funding_control_context\<lparr>lock_spend_permissions:={}\<rparr>)
      funding_control_request(sample_binding 17)3 4 5 realization_parent_second)=Request_Rejected"
    by (simp add: execute_descendant_def record_observation_def Let_def)
  have reply: "snd(execute_without_exact_spend_guard
      (funding_control_context\<lparr>lock_spend_permissions:={}\<rparr>)funding_control_request
      (sample_binding 17)3 4 5 realization_parent_second)=Descendant_Executed"
    by (simp only: mutant realization_seed_parent_success)
  have after: "funded_units(machine_state(fst(execute_without_exact_spend_guard
      (funding_control_context\<lparr>lock_spend_permissions:={}\<rparr>)funding_control_request
      (sample_binding 17)3 4 5 realization_parent_second)))((0,17),(2,17,4))=5"
    using realization_seed_funding(2) realization_seed_actual_step
    by (simp only: mutant; simp)
  have before: "funded_units(machine_state(fst(execute_descendant
      (funding_control_context\<lparr>lock_spend_permissions:={}\<rparr>)funding_control_request
      (sample_binding 17)3 4 5 realization_parent_second)))((0,17),(2,17,4))=0"
    by (simp add: execute_descendant_def record_observation_def Let_def
        realization_parent_second_state realization_parent_first_state)
  show ?thesis by (rule conjI[OF rejected conjI[OF reply conjI[OF after before]]])
qed

text \<open>This local negative control removes only membership of the
  exact caller, root, sender, recipient, amount and operation tuple in
  lock_spend_permissions. All remaining guards and the committed event
  are copied from execute_descendant. Its initial financial state is the
  projection of the two roots' actual source, terminal and credit prefix.
  Deleting the permission check moves five units for a policy that the
  original consumer rejects without moving funds.\<close>

end
