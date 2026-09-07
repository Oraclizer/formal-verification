(* SPDX-License-Identifier: BSD-3-Clause *)
theory Finality_Refinement
  imports Transfer_Ledger_Refinement Finality_Observations
begin

section \<open>Transfer Quantities and Regulatory Support\<close>

type_synonym regulatory_word = "(nat \<times> reg_action \<times> nat) list"

fun run_regulatory_word :: "regulatory_word \<Rightarrow> global_state \<Rightarrow> global_state option" where
  "run_regulatory_word [] state=Some state"
| "run_regulatory_word((domain,action,asset)#rest)state=
    (case sync domain action asset state of None \<Rightarrow> None
     | Some following \<Rightarrow> run_regulatory_word rest following)"

definition finality_alpha :: "finality_core \<Rightarrow> transfer_ledger \<times> global_state" where
  "finality_alpha s=(transfer_projection(core_parent s),receiver_snapshot(core_regulatory s))"

context source_attestation
begin

fun emitted_regulatory_word :: "finality_operation \<Rightarrow> finality_core \<Rightarrow> regulatory_word" where
  "emitted_regulatory_word(Invoke_Regulatory endpoint epoch index r)s=
    (if snd(invoke_regulatory endpoint epoch index r s)=Regulatory_Applied
     then case binding_operation(request_binding r) of
       Regulatory_State_Effect action \<Rightarrow> [(fst(binding_key(request_binding r)),action,binding_asset(request_binding r))]
     | _ \<Rightarrow> [] else [])"
| "emitted_regulatory_word _ s=[]"

lemma actual_regulatory_invocation_refines_cdsp:
  "run_regulatory_word(emitted_regulatory_word(Invoke_Regulatory endpoint epoch index r)s)
      (receiver_snapshot(core_regulatory s))=
    Some(receiver_snapshot(core_regulatory(fst(invoke_regulatory endpoint epoch index r s))))"
  by (auto simp: invoke_regulatory_def apply_regulatory_message_def
    split: if_splits option.splits message_operation.splits)

theorem actual_finality_step_refines_regulatory_word:
  "run_regulatory_word(emitted_regulatory_word action s)(receiver_snapshot(core_regulatory s))=
    Some(receiver_snapshot(core_regulatory(finality_step action s)))"
proof (cases action)
  case (Invoke_Regulatory endpoint epoch index r)
  show ?thesis using actual_regulatory_invocation_refines_cdsp[
      where endpoint=endpoint and epoch=epoch and index=index and r=r and s=s]
    by (simp add: Invoke_Regulatory finality_step_def)
qed (auto simp: finality_step_def record_terminal_def invoke_protocol_def
  reject_protocol_intent_def publish_primary_def Let_def split: if_splits option.splits)

theorem actual_finality_step_refines_product_words:
  assumes "reservation_contract balances(core_parent s)"
  shows "fst(finality_alpha(finality_step action s))=
    run_transfer_ledger(emitted_transfer_word(core_parent s)(core_parent(finality_step action s)))
      (fst(finality_alpha s)) \<and>
    run_regulatory_word(emitted_regulatory_word action s)(snd(finality_alpha s))=
      Some(snd(finality_alpha(finality_step action s)))"
  using actual_finality_step_refines_transfer_action_word[OF assms]
    actual_finality_step_refines_regulatory_word
  by (simp add: finality_alpha_def)

theorem actual_finality_step_preserves_cdsp:
  assumes "valid_state(receiver_snapshot(core_regulatory s))"
  shows "valid_state(receiver_snapshot(core_regulatory(finality_step action s)))"
proof (cases action)
  case (Invoke_Regulatory endpoint epoch index r)
  show ?thesis using assms
    by (auto simp: Invoke_Regulatory finality_step_def invoke_regulatory_def
      intro: completed_regulatory_message_preserves_cdsp split: option.splits if_splits)
qed (use assms in \<open>auto simp: finality_step_def record_terminal_def invoke_protocol_def
  reject_protocol_intent_def publish_primary_def Let_def split: option.splits if_splits\<close>)

theorem generated_finality_has_cdsp:
  assumes "valid_state regulatory"
  shows "valid_state(receiver_snapshot(core_regulatory
    (run_finality actions(initial_finality_core balances regulatory contexts))))"
proof -
  have preservation: "\<And>s. valid_state(receiver_snapshot(core_regulatory s)) \<Longrightarrow>
      valid_state(receiver_snapshot(core_regulatory(run_finality actions s)))"
    by (induction actions) (auto intro: actual_finality_step_preserves_cdsp)
  show ?thesis by (rule preservation) (simp add: initial_finality_core_def assms)
qed

theorem generated_finality_initializes_both_abstract_components:
  "finality_alpha(initial_finality_core balances regulatory contexts)=
    (initial_transfer_ledger balances,regulatory)"
  by (simp add: finality_alpha_def initial_finality_core_def initial_parent_has_initial_transfer_ledger)

end

section \<open>Independent API Reads and Quantity Observations\<close>

fun abstract_quantity_observation :: "application_query \<Rightarrow> transfer_ledger \<Rightarrow> nat option" where
  "abstract_quantity_observation(Source_Balance account)ledger=Some(ledger_source ledger account)"
| "abstract_quantity_observation(Destination_Balance account)ledger=Some(ledger_destination ledger account)"
| "abstract_quantity_observation(Root_Balance key account)ledger=Some(ledger_funding ledger(key,account))"
| "abstract_quantity_observation _ ledger=None"

lemma concrete_cache_quantity_matches_ledger_fields:
  assumes "abstract_quantity_observation query(transfer_projection(core_parent s))=Some amount"
  shows "stored_query query(capture_snapshot s)=Units_Value amount"
  using assms by (cases query) (auto simp: transfer_projection_def capture_snapshot_def)

context source_attestation
begin

theorem successful_current_quantity_has_independent_ledger_observation:
  assumes reply: "snd(execute_observed(Read_Current endpoint query)s)=Current_Value revision value"
    and quantity: "abstract_quantity_observation query(fst(finality_alpha(observed_core s)))=Some amount"
  shows "value=Units_Value amount \<and> revision=core_epoch(observed_core s)"
proof -
  have actual: "value=stored_query query(capture_snapshot(observed_core s))"
    and revision: "revision=core_epoch(observed_core s)"
    using successful_current_reply_has_actual_authority_state[OF reply] by blast+
  have "stored_query query(capture_snapshot(observed_core s))=Units_Value amount"
    by (rule concrete_cache_quantity_matches_ledger_fields)
      (use quantity in \<open>simp add: finality_alpha_def\<close>)
  then show ?thesis using actual revision by simp
qed

theorem successful_current_regulatory_query_reads_actual_cdsp_component:
  assumes "snd(execute_observed(Read_Protected_Current endpoint index r(Regulatory_State domain asset))s)=Current_Value revision value"
  shows "value=Regulatory_Value(get_reg_state(snd(finality_alpha(observed_core s)))domain asset)"
  using protected_current_response_has_revision[of endpoint index r "Regulatory_State domain asset" s revision "value"] assms
  by (simp add: finality_alpha_def capture_snapshot_def)

theorem protected_current_quantity_has_independent_ledger_observation:
  assumes reply: "snd(execute_observed(Read_Protected_Current endpoint index r query)s)=Current_Value revision value"
    and quantity: "abstract_quantity_observation query(fst(finality_alpha(observed_core s)))=Some amount"
  shows "value=Units_Value amount \<and> revision=core_epoch(observed_core s)"
proof -
  have actual: "value=stored_query query(capture_snapshot(observed_core s))"
    and revision: "revision=core_epoch(observed_core s)"
    using protected_current_response_has_revision[of endpoint index r query s revision "value"] reply by auto
  have "stored_query query(capture_snapshot(observed_core s))=Units_Value amount"
    by (rule concrete_cache_quantity_matches_ledger_fields)
      (use quantity in \<open>simp add: finality_alpha_def\<close>)
  then show ?thesis using actual revision by simp
qed

text \<open>The abstract quantity observer is defined on the independent
  transfer ledger. The concrete observer reads an endpoint's stored cache.
  Their correspondence uses the current barrier and the separate ledger
  projection theorem. Regulatory support is the CDSP component, not token
  quantity. The weak transition relation emits finite action words and permits
  internal stuttering; it does not instantiate a finite carrier or a single
  action map for the unbounded lifecycle state. Raw intermediate observations
  retain their values, and atomic pre/post observational equivalence is not
  inferred from this product simulation.\<close>

end

end
