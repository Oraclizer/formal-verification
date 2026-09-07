(* SPDX-License-Identifier: BSD-3-Clause *)
theory Finality_Records
  imports Finality_Protocol
begin

fun source_status_of_kind :: "terminal_kind \<Rightarrow> source_status" where
  "source_status_of_kind Confirmed_Decision=Finalized"
| "source_status_of_kind Reversed_Decision=Reversed"

definition terminal_core :: "terminal_record \<Rightarrow> transfer_binding \<times> terminal_kind" where
  "terminal_core record=(terminal_binding record,terminal_kind record)"

definition terminal_statement :: "terminal_record \<Rightarrow> source_statement" where
  "terminal_statement record=\<lparr>statement_binding=terminal_binding record,
    statement_status=source_status_of_kind(terminal_kind record)\<rparr>"

lemma terminal_statement_determines_core:
  "terminal_statement a=terminal_statement b \<Longrightarrow> terminal_core a=terminal_core b"
  by (cases "terminal_kind a"; cases "terminal_kind b")
     (auto simp: terminal_statement_def terminal_core_def)

context source_attestation
begin

definition valid_terminal_record :: "terminal_record \<Rightarrow> bool" where
  "valid_terminal_record record \<longleftrightarrow> terminal_evidence record\<noteq>[] \<and>
    (\<forall>cert\<in>set(terminal_evidence record). certificate_ok cert \<and>
       statement_binding(certificate_statement cert)=terminal_binding record \<and>
       kind_from_source(statement_status(certificate_statement cert))=Some(terminal_kind record))"

definition terminal_records_valid :: "finality_core \<Rightarrow> bool" where
  "terminal_records_valid s \<longleftrightarrow>
    (\<forall>key record. core_records s key=Some record \<longrightarrow>
      binding_key(terminal_binding record)=key \<and> valid_terminal_record record)"

theorem valid_record_has_stable_source_statement:
  assumes valid: "valid_terminal_record record"
  shows "stable_source(binding_key(terminal_binding record))=Some(terminal_statement record)"
proof -
  obtain cert where member: "cert\<in>set(terminal_evidence record)"
    using valid unfolding valid_terminal_record_def by (cases "terminal_evidence record") auto
  have ok: "certificate_ok cert"
    and bound: "statement_binding(certificate_statement cert)=terminal_binding record"
    and kind: "kind_from_source(statement_status(certificate_statement cert))=Some(terminal_kind record)"
    using valid member unfolding valid_terminal_record_def by blast+
  have status: "statement_status(certificate_statement cert)=source_status_of_kind(terminal_kind record)"
    using kind by (cases "statement_status(certificate_statement cert)"; cases "terminal_kind record") auto
  have stable_status: "statement_status(certificate_statement cert)\<noteq>Observed"
    using status by (cases "terminal_kind record") auto
  have whole: "certificate_statement cert=terminal_statement record"
    using bound status unfolding terminal_statement_def by (cases "certificate_statement cert") auto
  have "stable_source(binding_key(terminal_binding record))=Some(certificate_statement cert)"
    using certificate_authenticates_stable_fact[OF ok stable_status] by (simp only: bound)
  then show ?thesis by (simp only: whole)
qed

theorem independently_produced_records_agree:
  assumes first: "valid_terminal_record a" and second: "valid_terminal_record b"
    and key: "binding_key(terminal_binding a)=binding_key(terminal_binding b)"
  shows "terminal_core a=terminal_core b"
proof -
  have a: "stable_source(binding_key(terminal_binding a))=Some(terminal_statement a)"
    by (rule valid_record_has_stable_source_statement[OF first])
  have b: "stable_source(binding_key(terminal_binding b))=Some(terminal_statement b)"
    by (rule valid_record_has_stable_source_statement[OF second])
  have "terminal_statement a=terminal_statement b" using a b key by (metis option.inject)
  then show ?thesis by (rule terminal_statement_determines_core)
qed

lemma terminal_records_lookup_valid:
  "terminal_records_valid s \<Longrightarrow> core_records s key=Some record \<Longrightarrow>
   binding_key(terminal_binding record)=key \<and> valid_terminal_record record"
  unfolding terminal_records_valid_def by blast

lemma valid_records_update:
  assumes old: "terminal_records_valid s" and valid: "valid_terminal_record record"
  shows "terminal_records_valid(s\<lparr>core_records:=(core_records s)
    (binding_key(terminal_binding record):=Some record)\<rparr>)"
  using old valid unfolding terminal_records_valid_def by auto

lemma record_terminal_preserves_validity:
  assumes old: "terminal_records_valid s"
  shows "terminal_records_valid(fst(record_terminal cert s))"
proof (cases "certificate_ok cert \<and> source_origin_present cert s")
  case False
  then show ?thesis using old by (simp add: record_terminal_def Let_def)
next
  case True
  note admitted = True
  let ?b = "statement_binding(certificate_statement cert)"
  have ok: "certificate_ok cert" using True by blast
  show ?thesis
  proof (cases "kind_from_source(statement_status(certificate_statement cert))")
    case None
    then show ?thesis using old True by (simp add: record_terminal_def Let_def)
  next
    case (Some kind)
    note status = Some
    show ?thesis
    proof (cases "core_records s(binding_key ?b)")
      case None
      have valid: "valid_terminal_record
        \<lparr>terminal_binding=?b,terminal_kind=kind,terminal_evidence=[cert]\<rparr>"
        using ok Some by (simp add: valid_terminal_record_def)
      show ?thesis using valid_records_update[OF old valid] True Some None
        by (simp add: record_terminal_def Let_def)
    next
      case (Some stored_record)
      have stored: "core_records s(binding_key ?b)=Some stored_record" by (rule Some)
      have prior: "valid_terminal_record stored_record"
        using terminal_records_lookup_valid[OF old stored] by blast
      show ?thesis
      proof (cases "terminal_binding stored_record=?b \<and> terminal_kind stored_record=kind")
        case False
        then show ?thesis using old admitted status stored
          by (auto simp: record_terminal_def Let_def)
      next
        case True
        note matched = True
        have binding_match: "statement_binding(certificate_statement cert)=terminal_binding stored_record"
          using matched by simp
        have kind_match: "kind=terminal_kind stored_record"
          using matched by simp
        have new_evidence: "certificate_ok cert \<and>
          statement_binding(certificate_statement cert)=terminal_binding stored_record \<and>
          kind_from_source(statement_status(certificate_statement cert))=Some(terminal_kind stored_record)"
          using ok status binding_match kind_match by blast
        let ?updated = "stored_record\<lparr>terminal_evidence:=if cert\<in>set(terminal_evidence stored_record)
          then terminal_evidence stored_record else terminal_evidence stored_record@[cert]\<rparr>"
        have valid: "valid_terminal_record ?updated"
          using prior new_evidence
          by (simp add: valid_terminal_record_def split: if_splits)
        show ?thesis using valid_records_update[OF old valid]
          admitted matched status stored
          by (simp add: record_terminal_def Let_def)
      qed
    qed
  qed
qed

lemma finality_step_record_projection:
  "core_records(finality_step action s)=(case action of Record_Terminal cert \<Rightarrow>
    core_records(fst(record_terminal cert s)) | _ \<Rightarrow> core_records s)"
  by (cases action)
    (auto simp: finality_step_def invoke_protocol_def reject_protocol_intent_def
      invoke_regulatory_def publish_primary_def Let_def split: option.splits if_splits)

theorem finality_step_preserves_record_validity:
  assumes valid: "terminal_records_valid s"
  shows "terminal_records_valid(finality_step action s)"
proof (cases action)
  case (Record_Terminal cert)
  have "terminal_records_valid(fst(record_terminal cert s))"
    by (rule record_terminal_preserves_validity[OF valid])
  then show ?thesis
    unfolding terminal_records_valid_def
    by (simp only: finality_step_record_projection Record_Terminal finality_operation.case)
qed (use valid in \<open>simp_all add: terminal_records_valid_def finality_step_record_projection\<close>)

theorem finite_finality_has_valid_records:
  "terminal_records_valid s \<Longrightarrow> terminal_records_valid(run_finality actions s)"
  by (induction actions arbitrary:s) (auto intro: finality_step_preserves_record_validity)

theorem generated_finality_records_are_valid:
  "terminal_records_valid(run_finality actions(initial_finality_core balances regulatory contexts))"
  by (rule finite_finality_has_valid_records)
    (simp add: terminal_records_valid_def initial_finality_core_def)

lemma record_terminal_keeps_existing_core:
  assumes "core_records s key=Some old"
  shows "\<exists>next. core_records(fst(record_terminal cert s))key=Some next \<and>
    terminal_core next=terminal_core old"
  using assms
  by (auto simp: record_terminal_def terminal_core_def Let_def split: option.splits if_splits)

theorem finality_step_keeps_existing_core:
  assumes "core_records s key=Some old"
  shows "\<exists>next. core_records(finality_step action s)key=Some next \<and>
    terminal_core next=terminal_core old"
  using assms
  by (cases action)
    (auto simp: finality_step_def invoke_protocol_def reject_protocol_intent_def
      invoke_regulatory_def publish_primary_def Let_def
      intro: record_terminal_keeps_existing_core split: option.splits if_splits)

theorem all_future_operations_keep_the_terminal_core:
  assumes "core_records s key=Some old"
  shows "\<exists>next. core_records(run_finality actions s)key=Some next \<and>
    terminal_core next=terminal_core old"
  using assms
proof (induction actions arbitrary:s old)
  case Nil
  then show ?case by auto
next
  case (Cons action actions)
  obtain middle where at: "core_records(finality_step action s)key=Some middle"
    and same: "terminal_core middle=terminal_core old"
    using finality_step_keeps_existing_core[OF Cons.prems] by blast
  obtain later_record where later: "core_records(run_finality actions(finality_step action s))key=Some later_record"
    "terminal_core later_record=terminal_core middle"
    using Cons.IH[OF at] by blast
  show ?case using later same by auto
qed

theorem two_generated_traces_cannot_disagree_at_one_source_key:
  assumes a: "core_records(run_finality first(initial_finality_core balances regulatory contexts))key=Some left"
    and b: "core_records(run_finality second(initial_finality_core other_balances other_regulatory other_contexts))key=Some right"
  shows "terminal_core left=terminal_core right"
proof -
  have first: "valid_terminal_record left" and first_key: "binding_key(terminal_binding left)=key"
    using generated_finality_records_are_valid a unfolding terminal_records_valid_def by blast+
  have second: "valid_terminal_record right" and second_key: "binding_key(terminal_binding right)=key"
    using generated_finality_records_are_valid b unfolding terminal_records_valid_def by blast+
  show ?thesis by (rule independently_produced_records_agree[OF first second])
    (simp only: first_key second_key)
qed

theorem protocol_response_uses_current_record_guard:
  assumes "snd(invoke_protocol endpoint epoch index intent s)=Protocol_Response reply"
  shows "epoch=core_epoch s \<and> terminal_intent_guard s index intent"
  using assms by (auto simp: invoke_protocol_def Let_def split: if_splits)

theorem actual_credit_response_consumes_confirmation:
  assumes "snd(invoke_protocol endpoint epoch index(Deliver_Intent route r)s)=
    Protocol_Response(Delivery_Response(New_Credit b))"
  shows "exact_record_reference s index(request_binding r)Confirmed_Decision(request_certificate r) \<and>
    epoch=core_epoch s"
  using protocol_response_uses_current_record_guard[OF assms] by simp

theorem actual_return_response_consumes_reversal:
  assumes "snd(invoke_protocol endpoint epoch index(Return_Intent r g versions)s)=
    Protocol_Response Reservation_Released"
  shows "exact_record_reference s index(request_binding r)Reversed_Decision(request_certificate r) \<and>
    epoch=core_epoch s"
  using protocol_response_uses_current_record_guard[OF assms] by simp

text \<open>Record agreement is relative to the inherited stable source facts.
  It applies across the source and relay epochs admitted by that fixed
  instance. It is not a proof of Byzantine rounds, membership reconfiguration
  or a physical replicated-log implementation. Re-attestation can add a new
  certificate while the original binding and decision kind remain unchanged.\<close>

end

end
