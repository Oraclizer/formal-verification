(* SPDX-License-Identifier: BSD-3-Clause *)
theory Source_Coupling
  imports Source_Finality_Link
begin

section \<open>One Source Adapter and Its Child Consumer\<close>

text \<open>The sender records a key before attempting transmission, including
  attempts whose request or acknowledgment is lost. A successful local
  cancellation of a never-sent key blocks all later transmission. Previously
  sent keys need an authoritative source fence. Sent history is never deleted;
  a sent and blocked key is permitted when its source fence is recorded.

  These are logical authoritative adapter records, not volatile client
  observations. Their complete persistence, atomic write-before-send boundary,
  exclusive transmission path and physical source authentication are
  UNVERIFIED. No additional public consensus service is introduced.
  Monetary provenance is strengthened here; other regulatory operations retain
  their existing child semantics and their separate producer obligations.\<close>

record source_coupling_state =
  coupled_source :: controlled_source_state
  coupled_core :: finality_core
  coupled_receipts :: "source_certificate list"
  coupled_sent :: "source_key set"
  coupled_blocked :: "source_key set"

datatype source_coupling_action =
    Coupling_Source bool bool controlled_source_command
  | Coupling_Issue bool source_certificate
  | Coupling_Client bool client_command
  | Coupling_Environment nat lock_context

datatype source_coupling_reply =
    Coupling_Source_Reply controlled_source_reply
  | Coupling_Source_Unavailable
  | Coupling_Client_Reply finality_reply
  | Coupling_Receipt_Stored
  | Coupling_Rejected

definition initial_source_coupling :: "(source_account \<Rightarrow> nat) \<Rightarrow> global_state
  \<Rightarrow> (nat \<Rightarrow> lock_context) \<Rightarrow> source_coupling_state" where
  "initial_source_coupling balances regulatory contexts=
    \<lparr>coupled_source=initial_controlled_source balances,
      coupled_core=initial_finality_core balances regulatory contexts,coupled_receipts=[],
      coupled_sent={},coupled_blocked={}\<rparr>"

fun coupling_application :: "controlled_source_command \<Rightarrow> transfer_binding option" where
  "coupling_application (Controlled_Boundary (Boundary_Apply b))=Some b"
| "coupling_application _=None"

definition coupling_monetary :: "transfer_binding \<Rightarrow> bool" where
  "coupling_monetary b \<longleftrightarrow> binding_operation b=Destination_Credit"

definition coupling_live_receipt :: "source_coupling_state \<Rightarrow> source_certificate \<Rightarrow> bool"
  where
  "coupling_live_receipt s cert \<longleftrightarrow> cert\<in>set (coupled_receipts s) \<and>
    controlled_source_fact (coupled_source s)
      (binding_key (statement_binding (certificate_statement cert)))=
      Some (certificate_statement cert)"

definition coupling_effect_witness :: "source_coupling_state \<Rightarrow> transfer_binding \<Rightarrow> bool"
  where
  "coupling_effect_witness s b \<longleftrightarrow>
    boundary_evidence_matches b (Boundary_Effect_Witness b) (controlled_endpoint (coupled_source s))"

definition coupling_fence_witness :: "source_coupling_state \<Rightarrow> transfer_binding \<Rightarrow> bool"
  where
  "coupling_fence_witness s b \<longleftrightarrow>
    boundary_evidence_matches b (Boundary_No_Effect_Witness b)
      (controlled_endpoint (coupled_source s))"

definition coupling_close_allowed :: "bool \<Rightarrow> source_coupling_state \<Rightarrow>
  transfer_binding \<Rightarrow> bool" where
  "coupling_close_allowed available s b \<longleftrightarrow>
    binding_key b\<notin>coupled_sent s \<or> (available \<and> coupling_fence_witness s b)"

fun coupling_intent_guard :: "bool \<Rightarrow> source_coupling_state \<Rightarrow> protocol_intent \<Rightarrow>
  bool" where
  "coupling_intent_guard available s (Source_Intent r generation versions)=
    (\<not>coupling_monetary (request_binding r) \<or>
      (available \<and> coupling_effect_witness s (request_binding r)))"
| "coupling_intent_guard available s (Cancel_Intent r generation versions)=
    (\<not>coupling_monetary (request_binding r) \<or>
      coupling_close_allowed available s (request_binding r))"
| "coupling_intent_guard available s (Fence_Intent r generation versions)=
    (\<not>coupling_monetary (request_binding r) \<or>
      coupling_close_allowed available s (request_binding r))"
| "coupling_intent_guard available s (Return_Intent r generation versions)=
    (coupling_live_receipt s (request_certificate r) \<and>
      controlled_source_fact (coupled_source s) (binding_key (request_binding r))=
      Some \<lparr>statement_binding=request_binding r,statement_status=Reversed\<rparr>)"
| "coupling_intent_guard available s (Certificate_Intent cert)=
    (\<not>coupling_monetary (statement_binding (certificate_statement cert)) \<or>
      coupling_live_receipt s cert)"
| "coupling_intent_guard available s (Deliver_Intent route r)=
    coupling_live_receipt s (request_certificate r)"
| "coupling_intent_guard available s (Reconcile_Intent r generation versions)=
    coupling_live_receipt s (request_certificate r)"
| "coupling_intent_guard available s _=True"

fun coupling_guard :: "bool \<Rightarrow> source_coupling_state \<Rightarrow> client_command \<Rightarrow> bool"
  where
  "coupling_guard available s (Client_Terminal cert)=
    (\<not>coupling_monetary (statement_binding (certificate_statement cert)) \<or>
      coupling_live_receipt s cert)"
| "coupling_guard available s (Client_Protocol endpoint index intent)=
    coupling_intent_guard available s intent"
| "coupling_guard available s _=True"

fun coupling_closed_binding :: "client_command \<Rightarrow> finality_reply \<Rightarrow>
  transfer_binding option" where
  "coupling_closed_binding (Client_Protocol endpoint index (Cancel_Intent r generation versions))
      (Protocol_Response Reservation_Released)=
    (if coupling_monetary (request_binding r) then Some (request_binding r) else None)"
| "coupling_closed_binding (Client_Protocol endpoint index (Fence_Intent r generation versions))
      (Protocol_Response Source_Fenced)=
    (if coupling_monetary (request_binding r) then Some (request_binding r) else None)"
| "coupling_closed_binding _ _=None"

definition coupling_source_result :: "bool \<Rightarrow> bool \<Rightarrow> controlled_source_command \<Rightarrow>
  source_coupling_state \<Rightarrow> source_coupling_state \<times> source_coupling_reply" where
  "coupling_source_result arrived replied command s=
    (if (\<exists>b. coupling_application command=Some b \<and> binding_key b\<in>coupled_blocked s)
     then (s,Coupling_Rejected)
     else let sent=(case coupling_application command of None \<Rightarrow> coupled_sent s
                    | Some b \<Rightarrow> insert (binding_key b) (coupled_sent s));
              result=(if arrived then controlled_source_step command (coupled_source s)
                      else (coupled_source s,Controlled_Outcome_Unknown))
          in (s\<lparr>coupled_source:=fst result,coupled_sent:=sent\<rparr>,
            if arrived \<and> replied then Coupling_Source_Reply (snd result)
            else Coupling_Source_Unavailable))"

definition coupling_issue_result :: "bool \<Rightarrow> source_certificate \<Rightarrow> source_coupling_state
  \<Rightarrow> source_coupling_state \<times> source_coupling_reply" where
  "coupling_issue_result available cert s=
    (if \<not>available then (s,Coupling_Source_Unavailable)
     else let issued=issue_source_receipt (coupled_source s) cert (coupled_receipts s)
          in (s\<lparr>coupled_receipts:=issued\<rparr>,
            if cert\<in>set issued then Coupling_Receipt_Stored else Coupling_Rejected))"

context source_attestation
begin

fun coupling_client_result :: "client_command \<Rightarrow> source_coupling_state \<Rightarrow>
  finality_core \<times> finality_reply" where
  "coupling_client_result (Client_Protocol endpoint index (Return_Intent r generation versions)) s=
    snd (mirror_source_return (coupled_source s) endpoint (core_epoch (coupled_core s))
      index r generation versions (coupled_core s))"
| "coupling_client_result command s=execute_finality_client command (coupled_core s)"

definition coupling_client_step :: "bool \<Rightarrow> client_command \<Rightarrow> source_coupling_state
  \<Rightarrow> source_coupling_state \<times> source_coupling_reply" where
  "coupling_client_step available command s=
    (if \<not>coupling_guard available s command then (s,Coupling_Rejected)
     else let result=coupling_client_result command s;
              blocked=(case coupling_closed_binding command (snd result) of
                None \<Rightarrow> coupled_blocked s
              | Some b \<Rightarrow> insert (binding_key b) (coupled_blocked s))
          in (s\<lparr>coupled_core:=fst result,coupled_blocked:=blocked\<rparr>,
            Coupling_Client_Reply (snd result)))"

fun source_coupling_step :: "source_coupling_action \<Rightarrow> source_coupling_state \<Rightarrow>
  source_coupling_state \<times> source_coupling_reply" where
  "source_coupling_step (Coupling_Source arrived replied command) s=
    coupling_source_result arrived replied command s"
| "source_coupling_step (Coupling_Issue available cert) s=coupling_issue_result available cert s"
| "source_coupling_step (Coupling_Client available command) s=coupling_client_step available command s"
| "source_coupling_step (Coupling_Environment endpoint context) s=
    (let result=execute_finality_environment (endpoint,context) (coupled_core s)
     in (s\<lparr>coupled_core:=fst result\<rparr>,Coupling_Client_Reply (snd result)))"

fun run_source_coupling :: "source_coupling_action list \<Rightarrow> source_coupling_state \<Rightarrow>
  source_coupling_state" where
  "run_source_coupling [] s=s"
| "run_source_coupling (action#rest) s=run_source_coupling rest (fst (source_coupling_step action s))"

end

definition coupling_receipts_sound :: "source_coupling_state \<Rightarrow> bool" where
  "coupling_receipts_sound s \<longleftrightarrow>
    (\<forall>cert\<in>set (coupled_receipts s). controlled_source_fact (coupled_source s)
      (binding_key (statement_binding (certificate_statement cert)))=Some (certificate_statement cert))"

definition coupling_sent_covers_effects :: "source_coupling_state \<Rightarrow> bool" where
  "coupling_sent_covers_effects s \<longleftrightarrow>
    (\<forall>b\<in>set (boundary_effects (controlled_endpoint (coupled_source s))).
      binding_key b\<in>coupled_sent s)"

definition coupling_blocked_protected :: "source_coupling_state \<Rightarrow> bool" where
  "coupling_blocked_protected s \<longleftrightarrow>
    (\<forall>key\<in>coupled_blocked s. key\<notin>coupled_sent s \<or>
      (\<exists>b. boundary_records (controlled_endpoint (coupled_source s)) key=Some (Boundary_Fenced b)))"

context source_attestation
begin

definition source_coupling_invariant :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  source_coupling_state \<Rightarrow> bool" where
  "source_coupling_invariant balances s \<longleftrightarrow>
    controlled_source_invariant balances (coupled_source s) \<and>
    reservation_contract balances (core_parent (coupled_core s)) \<and>
    source_mirror_provenance (coupled_source s) (core_parent (coupled_core s)) \<and>
    coupling_receipts_sound s \<and> coupling_sent_covers_effects s \<and> coupling_blocked_protected s"

end

section \<open>Primitive History and Fence Preservation\<close>

definition coupling_source_candidates :: "controlled_source_command \<Rightarrow> transfer_binding set" where
  "coupling_source_candidates command=
    (case coupling_application command of None \<Rightarrow> {} | Some b \<Rightarrow> {b})"

lemma boundary_step_effect_bound:
  "set (boundary_effects (fst (boundary_step command source)))\<subseteq>
    set (boundary_effects source)\<union>
      (case command of Boundary_Apply b \<Rightarrow> {b} | _ \<Rightarrow> {})"
  by (cases command)
     (auto simp: boundary_apply_def boundary_fence_def boundary_record_effect_def boundary_record_fence_def
       split: option.splits source_boundary_record.splits)

lemma controlled_step_effect_bound:
  "set (boundary_effects (controlled_endpoint (fst (controlled_source_step command source))))\<subseteq>
    set (boundary_effects (controlled_endpoint source))\<union>coupling_source_candidates command"
proof (cases command)
  case (Controlled_Boundary action)
  have bound: "set (boundary_effects (fst (boundary_step action (controlled_endpoint source))))\<subseteq>
    set (boundary_effects (controlled_endpoint source))\<union>
      (case action of Boundary_Apply b \<Rightarrow> {b} | _ \<Rightarrow> {})"
    by (rule boundary_step_effect_bound)
  show ?thesis using bound Controlled_Boundary
    by (cases action) (auto simp: controlled_boundary_def coupling_source_candidates_def Let_def)
qed (auto simp: controlled_finalize_def controlled_reverse_def controlled_record_finalized_def
  controlled_record_reversed_def coupling_source_candidates_def
  split: option.splits controlled_source_outcome.splits)

lemma controlled_step_history_extends:
  "set (boundary_effects (controlled_endpoint source))\<subseteq>
      set (boundary_effects (controlled_endpoint (fst (controlled_source_step command source)))) \<and>
    set (controlled_returns source)\<subseteq>set (controlled_returns (fst (controlled_source_step command source)))"
proof (cases command)
  case (Controlled_Boundary action)
  then show ?thesis
    by (cases action)
       (auto simp: controlled_boundary_def boundary_apply_def boundary_fence_def
         boundary_record_effect_def boundary_record_fence_def Let_def
         split: option.splits source_boundary_record.splits)
qed (auto simp: controlled_finalize_def controlled_reverse_def
  controlled_record_finalized_def controlled_record_reversed_def
  split: option.splits controlled_source_outcome.splits)

lemma controlled_boundary_record_persists:
  assumes "boundary_records (controlled_endpoint source) key=Some entry"
  shows "boundary_records (controlled_endpoint (fst (controlled_source_step command source))) key=Some entry"
proof (cases command)
  case (Controlled_Boundary action)
  have keep: "boundary_records (fst (boundary_step action (controlled_endpoint source))) key=Some entry"
    by (rule boundary_existing_record_survives_step[OF assms])
  show ?thesis using keep assms Controlled_Boundary
    by (simp add: controlled_boundary_def Let_def)
qed (use assms in \<open>auto simp: controlled_finalize_def controlled_reverse_def
  controlled_record_finalized_def controlled_record_reversed_def
  split: option.splits controlled_source_outcome.splits\<close>)

lemma controlled_fact_survives_one_step:
  assumes "controlled_source_fact source key=Some statement"
  shows "controlled_source_fact (fst (controlled_source_step command source)) key=Some statement"
  using controlled_fact_survives_continuation
    [where s=source and key=key and statement=statement and commands="[command]", OF assms]
  by simp

lemma coupling_effect_witness_is_recorded:
  assumes "controlled_source_invariant balances (coupled_source s)" "coupling_effect_witness s b"
  shows "b\<in>set (boundary_effects (controlled_endpoint (coupled_source s)))"
proof -
  have history: "boundary_history_consistent (controlled_endpoint (coupled_source s))"
    using assms(1) unfolding controlled_source_invariant_def by blast
  show ?thesis
    by (rule boundary_effect_evidence_has_recorded_effect[OF history])
       (use assms(2) in \<open>simp add: coupling_effect_witness_def\<close>)
qed

lemma current_reversal_has_a_return_record:
  assumes inv: "controlled_source_invariant balances source"
    and fact: "controlled_source_fact source (binding_key b)=
      Some \<lparr>statement_binding=b,statement_status=Reversed\<rparr>"
  shows "b\<in>set (controlled_returns source)"
proof -
  obtain outcome where lookup: "controlled_outcomes source (binding_key b)=Some outcome"
    and statement: "controlled_outcome_statement outcome=
      \<lparr>statement_binding=b,statement_status=Reversed\<rparr>"
    using fact unfolding controlled_source_fact_def by (cases "controlled_outcomes source (binding_key b)") auto
  have reversed: "controlled_outcomes source (binding_key b)=Some (Controlled_Reversed b)"
    using lookup statement by (cases outcome) auto
  show ?thesis using inv reversed
    unfolding controlled_source_invariant_def controlled_return_history_def by blast
qed

lemma coupling_existing_fence_persists_source:
  assumes "boundary_records (controlled_endpoint (coupled_source s)) key=Some (Boundary_Fenced b)"
  shows "boundary_records (controlled_endpoint
    (coupled_source (fst (coupling_source_result arrived replied command s)))) key=Some (Boundary_Fenced b)"
  using controlled_boundary_record_persists
    [where source="coupled_source s" and key=key and entry="Boundary_Fenced b" and command=command, OF assms]
    assms
  by (auto simp: coupling_source_result_def Let_def)

lemma source_transmission_never_deletes_sent_history:
  "coupled_sent s\<subseteq>coupled_sent (fst (coupling_source_result arrived replied command s))"
  by (auto simp: coupling_source_result_def Let_def split: option.splits)

lemma blocked_transmission_is_rejected:
  assumes "coupling_application command=Some b" "binding_key b\<in>coupled_blocked s"
  shows "coupling_source_result arrived replied command s=(s,Coupling_Rejected)"
  using assms by (auto simp: coupling_source_result_def)

lemma lost_source_request_is_still_recorded_as_sent:
  assumes "coupling_application command=Some b" "binding_key b\<notin>coupled_blocked s"
  shows "binding_key b\<in>coupled_sent (fst (coupling_source_result False replied command s)) \<and>
    coupled_source (fst (coupling_source_result False replied command s))=coupled_source s"
  using assms by (simp add: coupling_source_result_def Let_def)

section \<open>Actual Child Effects and Their Source Candidates\<close>

fun coupling_intent_debits :: "protocol_intent \<Rightarrow> transfer_binding set" where
  "coupling_intent_debits (Source_Intent r generation versions)=
    (if coupling_monetary (request_binding r) then {request_binding r} else {})"
| "coupling_intent_debits _={}"

fun coupling_intent_returns :: "protocol_intent \<Rightarrow> transfer_binding set" where
  "coupling_intent_returns (Return_Intent r generation versions)={request_binding r}"
| "coupling_intent_returns _={}"

fun coupling_client_debits :: "client_command \<Rightarrow> transfer_binding set" where
  "coupling_client_debits (Client_Protocol endpoint index intent)=coupling_intent_debits intent"
| "coupling_client_debits _={}"

fun coupling_client_returns :: "client_command \<Rightarrow> transfer_binding set" where
  "coupling_client_returns (Client_Protocol endpoint index intent)=coupling_intent_returns intent"
| "coupling_client_returns _={}"

context source_attestation
begin

lemma actual_intent_history_bounds:
  "set (source_effects (machine_state (fst (intent_result context intent parent))))\<subseteq>
      set (source_effects (machine_state parent))\<union>coupling_intent_debits intent \<and>
    set (returned_bindings (machine_journal (fst (intent_result context intent parent))))\<subseteq>
      set (returned_bindings (machine_journal parent))\<union>coupling_intent_returns intent"
  by (cases intent)
     (auto simp: lift_protocol_result_def protocol_definitions coupling_monetary_def
       record_observation_def commit_reservation_event_def finish_reservation_def set_phase_def Let_def
       split: option.splits message_reply.splits)

lemma actual_client_history_bounds:
  "set (source_effects (machine_state (core_parent (fst (execute_finality_client command core)))))\<subseteq>
      set (source_effects (machine_state (core_parent core)))\<union>coupling_client_debits command \<and>
    set (returned_bindings (machine_journal (core_parent (fst (execute_finality_client command core)))))\<subseteq>
      set (returned_bindings (machine_journal (core_parent core)))\<union>coupling_client_returns command"
proof (cases command)
  case (Client_Protocol endpoint index intent)
  have bounds: "set (source_effects (machine_state (fst
      (intent_result (current_lock_view core endpoint) intent (core_parent core)))))\<subseteq>
      set (source_effects (machine_state (core_parent core)))\<union>coupling_intent_debits intent \<and>
    set (returned_bindings (machine_journal (fst
      (intent_result (current_lock_view core endpoint) intent (core_parent core)))))\<subseteq>
      set (returned_bindings (machine_journal (core_parent core)))\<union>coupling_intent_returns intent"
    by (rule actual_intent_history_bounds)
  show ?thesis using bounds Client_Protocol
    by (auto simp: execute_finality_client_def finality_step_def invoke_protocol_def
      reject_protocol_intent_def record_observation_def Let_def split: option.splits)
qed (auto simp: execute_finality_client_def finality_step_def record_terminal_def
  invoke_regulatory_def publish_primary_def Let_def split: option.splits)

lemma guarded_client_is_the_actual_child:
  assumes "coupling_guard available s command"
  shows "coupling_client_result command s=execute_finality_client command (coupled_core s)"
proof (cases command)
  case (Client_Protocol endpoint index intent)
  then show ?thesis using assms
    by (cases intent) (auto simp: mirror_source_return_def)
qed auto

lemma guarded_client_candidates_have_source_records:
  assumes "controlled_source_invariant balances (coupled_source s)" "coupling_guard available s command"
  shows "coupling_client_debits command\<subseteq>
      set (boundary_effects (controlled_endpoint (coupled_source s))) \<and>
    coupling_client_returns command\<subseteq>set (controlled_returns (coupled_source s))"
proof (cases command)
  case (Client_Protocol endpoint index intent)
  then show ?thesis using assms coupling_effect_witness_is_recorded current_reversal_has_a_return_record
    by (cases intent) auto
qed auto

lemma guarded_client_preserves_mirror_provenance:
  assumes inv: "controlled_source_invariant balances (coupled_source s)"
    and before: "source_mirror_provenance (coupled_source s) (core_parent (coupled_core s))"
    and guard: "coupling_guard available s command"
  shows "source_mirror_provenance (coupled_source s)
    (core_parent (fst (coupling_client_result command s)))"
proof -
  have actual: "coupling_client_result command s=execute_finality_client command (coupled_core s)"
    by (rule guarded_client_is_the_actual_child[OF guard])
  have candidates: "coupling_client_debits command\<subseteq>
      set (boundary_effects (controlled_endpoint (coupled_source s))) \<and>
    coupling_client_returns command\<subseteq>set (controlled_returns (coupled_source s))"
    by (rule guarded_client_candidates_have_source_records[OF inv guard])
  show ?thesis using before candidates actual_client_history_bounds[of command "coupled_core s"]
    unfolding actual source_mirror_provenance_def by blast
qed

lemma closed_binding_has_a_source_protection_guard:
  assumes "coupling_guard available s command" "coupling_closed_binding command reply=Some b"
  shows "binding_key b\<notin>coupled_sent s \<or> coupling_fence_witness s b"
  using assms
  by (induction command reply rule: coupling_closed_binding.induct)
     (auto simp: coupling_close_allowed_def split: if_splits)

end

section \<open>The Joint Invariant\<close>

lemma source_result_preserves_mirror_provenance:
  assumes "source_mirror_provenance (coupled_source s) (core_parent (coupled_core s))"
  shows "source_mirror_provenance (coupled_source (fst (coupling_source_result arrived replied command s)))
    (core_parent (coupled_core (fst (coupling_source_result arrived replied command s))))"
  using assms controlled_step_history_extends[of "coupled_source s" command]
  by (auto simp: source_mirror_provenance_def coupling_source_result_def Let_def)

lemma source_result_preserves_receipts:
  assumes sound: "coupling_receipts_sound s"
  shows "coupling_receipts_sound (fst (coupling_source_result arrived replied command s))"
proof (unfold coupling_receipts_sound_def, intro ballI)
  fix cert
  assume member: "cert\<in>set (coupled_receipts (fst (coupling_source_result arrived replied command s)))"
  have old_member: "cert\<in>set (coupled_receipts s)"
    using member by (simp add: coupling_source_result_def Let_def split: if_splits)
  have old_fact: "controlled_source_fact (coupled_source s)
    (binding_key (statement_binding (certificate_statement cert)))=Some (certificate_statement cert)"
    using sound old_member unfolding coupling_receipts_sound_def by blast
  have next_fact: "controlled_source_fact (fst (controlled_source_step command (coupled_source s)))
    (binding_key (statement_binding (certificate_statement cert)))=Some (certificate_statement cert)"
    by (rule controlled_fact_survives_one_step
      [where source="coupled_source s" and key="binding_key (statement_binding (certificate_statement cert))"
        and statement="certificate_statement cert" and command=command])
       (rule old_fact)
  show "controlled_source_fact (coupled_source (fst (coupling_source_result arrived replied command s)))
    (binding_key (statement_binding (certificate_statement cert)))=Some (certificate_statement cert)"
    using old_fact next_fact by (simp add: coupling_source_result_def Let_def split: if_splits)
qed

lemma source_result_preserves_sent_coverage:
  assumes "coupling_sent_covers_effects s"
  shows "coupling_sent_covers_effects (fst (coupling_source_result arrived replied command s))"
  using assms controlled_step_effect_bound[of command "coupled_source s"]
  by (auto simp: coupling_sent_covers_effects_def coupling_source_result_def
    coupling_source_candidates_def Let_def split: option.splits if_splits)

lemma source_result_preserves_blocked_protection:
  assumes protected: "coupling_blocked_protected s"
  shows "coupling_blocked_protected (fst (coupling_source_result arrived replied command s))"
proof (unfold coupling_blocked_protected_def, intro ballI)
  fix key
  assume member: "key\<in>coupled_blocked (fst (coupling_source_result arrived replied command s))"
  have old_member: "key\<in>coupled_blocked s"
    using member by (simp add: coupling_source_result_def Let_def split: if_splits)
  have old: "key\<notin>coupled_sent s \<or>
    (\<exists>b. boundary_records (controlled_endpoint (coupled_source s)) key=Some (Boundary_Fenced b))"
    using protected old_member unfolding coupling_blocked_protected_def by blast
  show "key\<notin>coupled_sent (fst (coupling_source_result arrived replied command s)) \<or>
    (\<exists>b. boundary_records (controlled_endpoint
      (coupled_source (fst (coupling_source_result arrived replied command s)))) key=Some (Boundary_Fenced b))"
  proof (cases "key\<in>coupled_sent s")
    case True
    then obtain b where fence_record: "boundary_records (controlled_endpoint (coupled_source s)) key=
      Some (Boundary_Fenced b)" using old by blast
    show ?thesis using coupling_existing_fence_persists_source[OF fence_record] by blast
  next
    case False
    have absent: "key\<notin>coupled_sent (fst (coupling_source_result arrived replied command s))"
      using False old_member
      by (auto simp: coupling_source_result_def Let_def split: option.splits if_splits)
    then show ?thesis by blast
  qed
qed

lemma issuance_preserves_current_receipts:
  assumes "coupling_receipts_sound s"
  shows "coupling_receipts_sound (fst (coupling_issue_result available cert s))"
  using assms
  by (auto simp: coupling_receipts_sound_def coupling_issue_result_def issue_source_receipt_def Let_def)

context source_attestation
begin

lemma initial_source_coupling_invariant:
  "source_coupling_invariant balances (initial_source_coupling balances regulatory contexts)"
proof -
  have source: "controlled_source_invariant balances (initial_controlled_source balances)"
    by (rule controlled_initial_invariant)
  have parent: "reservation_contract balances (initial_reservation_machine balances)"
    by (rule initial_reservation_contract)
  have mirror: "source_mirror_provenance (initial_controlled_source balances)
    (initial_reservation_machine balances)"
    by (simp add: source_mirror_provenance_def initial_controlled_source_def initial_source_boundary_def
      initial_reservation_machine_def initial_reservation_state_def)
  have receipts: "coupling_receipts_sound (initial_source_coupling balances regulatory contexts)"
    by (simp add: coupling_receipts_sound_def initial_source_coupling_def)
  have sent: "coupling_sent_covers_effects (initial_source_coupling balances regulatory contexts)"
    by (simp add: coupling_sent_covers_effects_def initial_source_coupling_def
      initial_controlled_source_def initial_source_boundary_def)
  have blocked: "coupling_blocked_protected (initial_source_coupling balances regulatory contexts)"
    by (simp add: coupling_blocked_protected_def initial_source_coupling_def)
  show ?thesis using source parent mirror receipts sent blocked
    by (simp add: source_coupling_invariant_def initial_source_coupling_def initial_finality_core_def)
qed

lemma source_action_preserves_coupling_invariant:
  assumes "source_coupling_invariant balances s"
  shows "source_coupling_invariant balances (fst (coupling_source_result arrived replied command s))"
proof -
  have source: "controlled_source_invariant balances (coupled_source s)"
    and parent: "reservation_contract balances (core_parent (coupled_core s))"
    and mirror: "source_mirror_provenance (coupled_source s) (core_parent (coupled_core s))"
    and receipts: "coupling_receipts_sound s"
    and sent: "coupling_sent_covers_effects s"
    and blocked: "coupling_blocked_protected s"
    using assms unfolding source_coupling_invariant_def by blast+
  have source_after: "controlled_source_invariant balances (fst (controlled_source_step command (coupled_source s)))"
    by (rule controlled_step_preserves_invariant[OF source])
  show ?thesis
    using source parent source_after source_result_preserves_mirror_provenance[OF mirror]
      source_result_preserves_receipts[OF receipts] source_result_preserves_sent_coverage[OF sent]
      source_result_preserves_blocked_protection[OF blocked]
    by (auto simp: source_coupling_invariant_def coupling_source_result_def Let_def)
qed

lemma client_step_preserves_blocked_protection:
  assumes protected: "coupling_blocked_protected s"
  shows "coupling_blocked_protected (fst (coupling_client_step available command s))"
proof (cases "coupling_guard available s command")
  case False
  then show ?thesis using protected by (simp add: coupling_client_step_def)
next
  case True
  show ?thesis
  proof (cases "coupling_closed_binding command (snd (coupling_client_result command s))")
    case None
    then show ?thesis using True protected
      by (simp add: coupling_client_step_def coupling_blocked_protected_def Let_def)
  next
    case (Some b)
    have guard: "binding_key b\<notin>coupled_sent s \<or> coupling_fence_witness s b"
      by (rule closed_binding_has_a_source_protection_guard[OF True Some])
    have certified: "binding_key b\<notin>coupled_sent s \<or>
      boundary_records (controlled_endpoint (coupled_source s)) (binding_key b)=Some (Boundary_Fenced b)"
      using guard by (simp add: coupling_fence_witness_def boundary_evidence_exact boundary_has_no_effect_def)
    show ?thesis using True Some protected certified
      by (auto simp: coupling_client_step_def coupling_blocked_protected_def Let_def)
  qed
qed

lemma client_action_preserves_coupling_invariant:
  assumes inv: "source_coupling_invariant balances s"
  shows "source_coupling_invariant balances (fst (coupling_client_step available command s))"
proof (cases "coupling_guard available s command")
  case False
  then show ?thesis using inv by (simp add: coupling_client_step_def)
next
  case True
  have source: "controlled_source_invariant balances (coupled_source s)"
    and parent: "reservation_contract balances (core_parent (coupled_core s))"
    and mirror: "source_mirror_provenance (coupled_source s) (core_parent (coupled_core s))"
    and receipts: "coupling_receipts_sound s"
    and sent: "coupling_sent_covers_effects s"
    and blocked: "coupling_blocked_protected s"
    using inv unfolding source_coupling_invariant_def by blast+
  have actual: "coupling_client_result command s=execute_finality_client command (coupled_core s)"
    by (rule guarded_client_is_the_actual_child[OF True])
  have parent_after: "reservation_contract balances
    (core_parent (fst (coupling_client_result command s)))"
    unfolding actual execute_finality_client_def
    by (simp only: fst_conv, rule finality_step_preserves_parent_contract[OF parent])
  have mirror_after: "source_mirror_provenance (coupled_source s)
    (core_parent (fst (coupling_client_result command s)))"
    by (rule guarded_client_preserves_mirror_provenance[OF source mirror True])
  have blocked_after: "coupling_blocked_protected (fst (coupling_client_step available command s))"
    by (rule client_step_preserves_blocked_protection[OF blocked])
  show ?thesis using True source parent_after mirror_after receipts sent blocked_after
    by (auto simp: source_coupling_invariant_def coupling_client_step_def Let_def
      coupling_receipts_sound_def coupling_sent_covers_effects_def
      split: option.splits)
qed

theorem source_coupling_step_preserves_invariant:
  assumes "source_coupling_invariant balances s"
  shows "source_coupling_invariant balances (fst (source_coupling_step action s))"
proof (cases action)
  case (Coupling_Source arrived replied command)
  show ?thesis by (simp only: Coupling_Source source_coupling_step.simps,
    rule source_action_preserves_coupling_invariant[OF assms])
next
  case (Coupling_Client available command)
  show ?thesis by (simp only: Coupling_Client source_coupling_step.simps,
    rule client_action_preserves_coupling_invariant[OF assms])
next
  case (Coupling_Issue available cert)
  have receipt: "coupling_receipts_sound s"
    using assms unfolding source_coupling_invariant_def by blast
  show ?thesis using assms issuance_preserves_current_receipts[OF receipt]
    by (simp add: Coupling_Issue source_coupling_invariant_def coupling_issue_result_def Let_def
      coupling_sent_covers_effects_def coupling_blocked_protected_def split: if_splits)
next
  case (Coupling_Environment endpoint provider_context)
  show ?thesis using assms
    by (auto simp: Coupling_Environment source_coupling_invariant_def execute_finality_environment_def
      finality_step_def Let_def source_mirror_provenance_def coupling_receipts_sound_def
      coupling_sent_covers_effects_def coupling_blocked_protected_def)
qed

theorem source_coupling_run_preserves_invariant:
  "source_coupling_invariant balances s \<Longrightarrow>
    source_coupling_invariant balances (run_source_coupling actions s)"
  by (induction actions arbitrary:s) (auto intro: source_coupling_step_preserves_invariant)

theorem all_finite_joint_executions_have_source_provenance:
  "source_coupling_invariant balances
    (run_source_coupling actions (initial_source_coupling balances regulatory contexts))"
  by (rule source_coupling_run_preserves_invariant[OF initial_source_coupling_invariant])

theorem joint_execution_supplies_exact_source_mirror_provenance:
  "source_mirror_provenance
    (coupled_source (run_source_coupling actions (initial_source_coupling balances regulatory contexts)))
    (core_parent (coupled_core (run_source_coupling actions
      (initial_source_coupling balances regulatory contexts))))"
  using all_finite_joint_executions_have_source_provenance[of balances actions regulatory contexts]
  unfolding source_coupling_invariant_def by blast

end

section \<open>Persistent No-Effect Completion\<close>

context source_attestation
begin

lemma coupling_blocked_keys_have_no_source_effect:
  assumes inv: "source_coupling_invariant balances s" and blocked: "key\<in>coupled_blocked s"
  shows "key\<notin>set (map binding_key (boundary_effects (controlled_endpoint (coupled_source s))))"
proof
  assume present: "key\<in>set (map binding_key (boundary_effects (controlled_endpoint (coupled_source s))))"
  obtain b where member: "b\<in>set (boundary_effects (controlled_endpoint (coupled_source s)))"
    and key: "binding_key b=key" using present by auto
  have coverage: "coupling_sent_covers_effects s" and protection: "coupling_blocked_protected s"
    and history: "boundary_history_consistent (controlled_endpoint (coupled_source s))"
    using inv unfolding source_coupling_invariant_def controlled_source_invariant_def by blast+
  have sent: "key\<in>coupled_sent s"
    using coverage member key unfolding coupling_sent_covers_effects_def by blast
  obtain old where fence: "boundary_records (controlled_endpoint (coupled_source s)) key=
    Some (Boundary_Fenced old)"
    using protection blocked sent unfolding coupling_blocked_protected_def by blast
  have effect: "boundary_records (controlled_endpoint (coupled_source s)) (binding_key b)=
    Some (Boundary_Effect b)"
    using history member unfolding boundary_history_consistent_def by blast
  show False using fence effect key by simp
qed

theorem blocked_and_effect_keys_are_disjoint:
  assumes "source_coupling_invariant balances s"
  shows "coupled_blocked s\<inter>set
    (map binding_key (boundary_effects (controlled_endpoint (coupled_source s))))={}"
  using coupling_blocked_keys_have_no_source_effect[OF assms] by blast

lemma coupling_step_keeps_blocked_keys:
  "coupled_blocked s\<subseteq>coupled_blocked (fst (source_coupling_step action s))"
  by (cases action)
     (auto simp: coupling_source_result_def coupling_issue_result_def coupling_client_step_def
       Let_def split: option.splits)

lemma coupling_run_keeps_blocked_keys:
  "coupled_blocked s\<subseteq>coupled_blocked (run_source_coupling actions s)"
proof (induction actions arbitrary:s)
  case Nil
  then show ?case by simp
next
  case (Cons action actions)
  have step: "coupled_blocked s\<subseteq>
    coupled_blocked (fst (source_coupling_step action s))"
    by (rule coupling_step_keeps_blocked_keys)
  have continuation: "coupled_blocked (fst (source_coupling_step action s))\<subseteq>
    coupled_blocked (run_source_coupling actions (fst (source_coupling_step action s)))"
    by (rule Cons.IH)
  have "coupled_blocked s\<subseteq>
    coupled_blocked (run_source_coupling actions (fst (source_coupling_step action s)))"
    by (rule subset_trans[OF step continuation])
  then show ?case by simp
qed

theorem successful_no_effect_completion_blocks_the_exact_key:
  assumes reply: "snd (source_coupling_step (Coupling_Client available command) s)=Coupling_Client_Reply result"
    and closes: "coupling_closed_binding command result=Some b"
  shows "binding_key b\<in>coupled_blocked
    (fst (source_coupling_step (Coupling_Client available command) s))"
  using reply closes by (auto simp: coupling_client_step_def Let_def split: if_splits)

definition coupling_after_client :: "source_coupling_action list \<Rightarrow> bool \<Rightarrow>
  client_command \<Rightarrow> source_coupling_state \<Rightarrow> source_coupling_state" where
  "coupling_after_client continuation available command s=
    run_source_coupling continuation (fst (source_coupling_step (Coupling_Client available command) s))"

theorem completed_no_effect_has_no_past_or_future_source_effect:
  assumes inv: "source_coupling_invariant balances s"
    and reply: "snd (source_coupling_step (Coupling_Client available command) s)=Coupling_Client_Reply result"
    and closes: "coupling_closed_binding command result=Some b"
  shows "binding_key b\<in>coupled_blocked (coupling_after_client continuation available command s) \<and>
    binding_key b\<notin>set (map binding_key
      (boundary_effects (controlled_endpoint
        (coupled_source (coupling_after_client continuation available command s)))))"
proof -
  let ?after="coupling_after_client continuation available command s"
  have first: "binding_key b\<in>coupled_blocked
    (fst (source_coupling_step (Coupling_Client available command) s))"
    by (rule successful_no_effect_completion_blocks_the_exact_key[OF reply closes])
  have later: "binding_key b\<in>coupled_blocked ?after"
    using first coupling_run_keeps_blocked_keys
    unfolding coupling_after_client_def by blast
  have valid: "source_coupling_invariant balances ?after"
    unfolding coupling_after_client_def
    by (rule source_coupling_run_preserves_invariant,
        rule source_coupling_step_preserves_invariant[OF inv])
  show ?thesis using later coupling_blocked_keys_have_no_source_effect[OF valid later] by blast
qed

theorem completed_no_effect_rejects_every_late_transmission:
  assumes inv: "source_coupling_invariant balances s"
    and reply: "snd (source_coupling_step (Coupling_Client available command) s)=Coupling_Client_Reply result"
    and closes: "coupling_closed_binding command result=Some b"
    and same_key: "binding_key late=binding_key b"
  shows "coupling_source_result arrived replied (Controlled_Boundary (Boundary_Apply late))
      (coupling_after_client continuation available command s)=
    (coupling_after_client continuation available command s,Coupling_Rejected)"
proof -
  have blocked: "binding_key b\<in>coupled_blocked (coupling_after_client continuation available command s)"
    using completed_no_effect_has_no_past_or_future_source_effect
      [OF inv reply closes, where continuation=continuation] by blast
  have late_blocked: "binding_key late\<in>
    coupled_blocked (coupling_after_client continuation available command s)"
    using blocked same_key by simp
  show ?thesis
    by (rule blocked_transmission_is_rejected[where b=late])
       (simp, rule late_blocked)
qed

theorem future_receipt_cannot_be_used_early:
  assumes monetary: "coupling_monetary (statement_binding (certificate_statement cert))"
    and absent: "\<not>coupling_live_receipt s cert"
  shows "source_coupling_step (Coupling_Client available (Client_Terminal cert)) s=(s,Coupling_Rejected)"
  using assms by (simp add: coupling_client_step_def)

theorem existing_child_guards_are_always_consumed:
  assumes "snd (source_coupling_step (Coupling_Client available command) s)=Coupling_Client_Reply reply"
  shows "coupling_guard available s command \<and>
    execute_finality_client command (coupled_core s)=
      (coupled_core (fst (source_coupling_step (Coupling_Client available command) s)),reply)"
  using assms guarded_client_is_the_actual_child
  by (auto simp: coupling_client_step_def Let_def split: option.splits if_splits)

end

section \<open>Actual Prefixes and Guard-Removal Witnesses\<close>

definition coupling_example_start :: source_coupling_state where
  "coupling_example_start=initial_source_coupling sample_balances (sample_metadata ACTIVE)
    (\<lambda>_.sample_source_context ACTIVE)"

definition coupling_prepare :: "nat \<Rightarrow> source_coupling_action list" where
  "coupling_prepare event=[
    Coupling_Client True (Client_Protocol 0 0 (Reserve_Intent (sample_request event) [] 10)),
    Coupling_Client True (Client_Protocol 0 0 (Dispatch_Intent (sample_request event) 0 []))]"

definition coupling_submitted :: "nat \<Rightarrow> source_coupling_state" where
  "coupling_submitted event=linked.run_source_coupling (coupling_prepare event) coupling_example_start"

definition coupling_lost_ack :: "nat \<Rightarrow> source_coupling_state" where
  "coupling_lost_ack event=fst (linked.source_coupling_step
    (Coupling_Source True False (Controlled_Boundary (Boundary_Apply (sample_binding event))))
    (coupling_submitted event))"

lemmas coupling_example_data = coupling_example_start_def initial_source_coupling_def
  coupling_prepare_def coupling_submitted_def initial_controlled_source_def initial_source_boundary_def
  linked.coupling_client_step_def linked.execute_finality_client_def linked.finality_step_def
  linked.core_result.simps linked.invoke_protocol_def linked.intent_result.simps lift_protocol_result_def
  linked.run_source_coupling.simps linked.source_coupling_step.simps linked.coupling_client_result.simps
  initial_finality_core_def current_lock_view_def vector_lookup_def
  sample_data_defs acquire_reservation_def dispatch_source_def execute_source_effect_def
  record_observation_def commit_reservation_event_def

lemma coupling_submitted_projection:
  "event\<in>{17,22} \<Longrightarrow>
    coupled_source (coupling_submitted event)=initial_controlled_source sample_balances \<and>
    coupled_sent (coupling_submitted event)={} \<and> coupled_blocked (coupling_submitted event)={} \<and>
    source_effects (machine_state (core_parent (coupled_core (coupling_submitted event))))=[] \<and>
    phase_at (machine_state (core_parent (coupled_core (coupling_submitted event))))
      (binding_key (sample_binding event))=Some Source_Submitted"
  by (auto simp: coupling_example_data Let_def)

theorem bare_child_can_record_an_effect_before_the_source:
  "source_effects (machine_state (core_parent (fst (linked.execute_finality_client
      (Client_Protocol 0 0 (Source_Intent (sample_request 17) 0 []))
      (coupled_core (coupling_submitted 17))))))=[sample_binding 17] \<and>
    boundary_effects (controlled_endpoint (coupled_source (coupling_submitted 17)))=[]"
  by (simp add: coupling_example_data Let_def)

theorem coupling_rejects_the_premature_source_mirror:
  "linked.source_coupling_step
      (Coupling_Client True (Client_Protocol 0 0 (Source_Intent (sample_request 17) 0 [])))
      (coupling_submitted 17)=(coupling_submitted 17,Coupling_Rejected)"
  by (simp add: linked.coupling_client_step_def coupling_monetary_def coupling_effect_witness_def
    boundary_evidence_exact boundary_has_effect_def coupling_submitted_projection
    initial_controlled_source_def initial_source_boundary_def sample_request_def sample_binding_def example_binding_def)

lemma lost_ack_source_projection:
  "event\<in>{17,22} \<Longrightarrow>
    coupled_core (coupling_lost_ack event)=coupled_core (coupling_submitted event) \<and>
    coupled_sent (coupling_lost_ack event)={binding_key (sample_binding event)} \<and>
    coupled_blocked (coupling_lost_ack event)={} \<and>
    boundary_has_effect (sample_binding event) (controlled_endpoint (coupled_source (coupling_lost_ack event)))"
  by (auto simp: coupling_lost_ack_def coupling_source_result_def coupling_submitted_projection
    controlled_boundary_def initial_controlled_source_def initial_source_boundary_def
    boundary_apply_def boundary_record_effect_def boundary_has_effect_def boundary_valid_binding_def
    sample_binding_def example_binding_def sample_balances_def source_account_of_def Let_def)

theorem bare_child_fence_can_close_after_an_unacknowledged_source_effect:
  "snd (linked.execute_finality_client
      (Client_Protocol 0 0 (Fence_Intent (sample_request 17) 0 []))
      (coupled_core (coupling_lost_ack 17)))=Protocol_Response Source_Fenced \<and>
    boundary_has_effect (sample_binding 17) (controlled_endpoint (coupled_source (coupling_lost_ack 17)))"
proof -
  have core: "coupled_core (coupling_lost_ack 17)=coupled_core (coupling_submitted 17)"
    and effect: "boundary_has_effect (sample_binding 17)
      (controlled_endpoint (coupled_source (coupling_lost_ack 17)))"
    using lost_ack_source_projection[of 17] by auto
  show ?thesis
  proof (rule conjI)
    show "snd (linked.execute_finality_client
        (Client_Protocol 0 0 (Fence_Intent (sample_request 17) 0 []))
        (coupled_core (coupling_lost_ack 17)))=Protocol_Response Source_Fenced"
      by (simp add: core coupling_example_data fence_unexecuted_source_def Let_def)
    show "boundary_has_effect (sample_binding 17)
      (controlled_endpoint (coupled_source (coupling_lost_ack 17)))"
      by (rule effect)
  qed
qed

theorem coupling_rejects_the_unsafe_local_fence:
  "linked.source_coupling_step
      (Coupling_Client True (Client_Protocol 0 0 (Fence_Intent (sample_request 17) 0 [])))
      (coupling_lost_ack 17)=(coupling_lost_ack 17,Coupling_Rejected)"
  using lost_ack_source_projection[of 17]
  by (simp add: linked.coupling_client_step_def coupling_close_allowed_def coupling_fence_witness_def
    boundary_evidence_exact boundary_has_no_effect_def boundary_has_effect_def
    coupling_monetary_def sample_request_def sample_binding_def example_binding_def)

theorem valid_source_mirror_succeeds_after_a_lost_acknowledgment:
  "snd (linked.source_coupling_step
    (Coupling_Client True (Client_Protocol 0 0 (Source_Intent (sample_request 17) 0 [])))
    (coupling_lost_ack 17))=Coupling_Client_Reply (Protocol_Response Source_Debited)"
  using lost_ack_source_projection[of 17]
  by (simp add: linked.coupling_client_step_def coupling_effect_witness_def boundary_evidence_exact
    coupling_monetary_def coupling_example_data Let_def)

definition coupling_sent_unarrived :: source_coupling_state where
  "coupling_sent_unarrived=fst (linked.source_coupling_step
    (Coupling_Source False False (Controlled_Boundary (Boundary_Apply (sample_binding 17))))
    (coupling_submitted 17))"

definition coupling_source_fenced :: source_coupling_state where
  "coupling_source_fenced=fst (linked.source_coupling_step
    (Coupling_Source True True (Controlled_Boundary (Boundary_Fence (sample_binding 17))))
    coupling_sent_unarrived)"

theorem valid_no_effect_fence_succeeds:
  "snd (linked.source_coupling_step
    (Coupling_Client True (Client_Protocol 0 0 (Fence_Intent (sample_request 17) 0 [])))
    coupling_source_fenced)=Coupling_Client_Reply (Protocol_Response Source_Fenced)"
  by (simp add: coupling_source_fenced_def coupling_sent_unarrived_def coupling_source_result_def coupling_example_data
    controlled_boundary_def boundary_fence_def boundary_record_fence_def boundary_valid_binding_def
    coupling_close_allowed_def coupling_fence_witness_def boundary_evidence_exact
    boundary_has_no_effect_def coupling_monetary_def fence_unexecuted_source_def Let_def)

theorem a_sent_but_fenced_key_may_be_blocked:
  "let after=fst (linked.source_coupling_step
      (Coupling_Client True (Client_Protocol 0 0 (Fence_Intent (sample_request 17) 0 [])))
      coupling_source_fenced)
   in (0,17)\<in>coupled_sent after \<and> (0,17)\<in>coupled_blocked after"
  by (simp add: coupling_source_fenced_def coupling_sent_unarrived_def coupling_source_result_def coupling_example_data
    controlled_boundary_def boundary_fence_def boundary_record_fence_def boundary_valid_binding_def
    coupling_close_allowed_def coupling_fence_witness_def boundary_evidence_exact
    boundary_has_no_effect_def coupling_monetary_def fence_unexecuted_source_def Let_def)

definition coupling_return_word :: "source_coupling_action list" where
  "coupling_return_word=coupling_prepare 22@[
    Coupling_Source True False (Controlled_Boundary (Boundary_Apply (sample_binding 22))),
    Coupling_Client True (Client_Protocol 0 0 (Source_Intent (sample_request 22) 0 [])),
    Coupling_Source True True (Controlled_Reverse (sample_binding 22)),
    Coupling_Issue True (linked_certificate 22),
    Coupling_Client True (Client_Terminal (linked_certificate 22)),
    Coupling_Client True (Client_Protocol 0 0 (Certificate_Intent (linked_certificate 22)))]"

definition coupling_before_return :: source_coupling_state where
  "coupling_before_return=linked.run_source_coupling coupling_return_word coupling_example_start"

theorem valid_return_uses_the_actual_source_and_child:
  "snd (linked.source_coupling_step
    (Coupling_Client True (Client_Protocol 0 0 (Return_Intent linked_return_request 0 [])))
    coupling_before_return)=Coupling_Client_Reply (Protocol_Response Reservation_Released) \<and>
    coupled_source (fst (linked.source_coupling_step
      (Coupling_Client True (Client_Protocol 0 0 (Return_Intent linked_return_request 0 [])))
      coupling_before_return))=coupled_source coupling_before_return"
proof -
  let ?b="sample_binding 22"
  let ?cert="linked_certificate 22"
  let ?request="linked_return_request"
  let ?view="sample_source_context ACTIVE"
  let ?source_command="Client_Protocol 0 0 (Source_Intent (sample_request 22) 0 [])"
  let ?return_command="Client_Protocol 0 0 (Return_Intent ?request 0 [])"
  let ?entry="\<lparr>terminal_binding=?b,terminal_kind=Reversed_Decision,
    terminal_evidence=[?cert]\<rparr>"
  define sourced where "sourced=fst (linked.source_coupling_step
    (Coupling_Client True ?source_command) (coupling_lost_ack 22))"
  define reversed where "reversed=fst (linked.source_coupling_step
    (Coupling_Source True True (Controlled_Reverse ?b)) sourced)"
  define issued where "issued=fst (linked.source_coupling_step (Coupling_Issue True ?cert) reversed)"
  define terminal where "terminal=fst (linked.source_coupling_step
    (Coupling_Client True (Client_Terminal ?cert)) issued)"
  define published where "published=fst (linked.source_coupling_step
    (Coupling_Client True (Client_Protocol 0 0 (Certificate_Intent ?cert))) terminal)"
  have word: "coupling_before_return=published"
    unfolding coupling_before_return_def coupling_return_word_def
      published_def terminal_def issued_def reversed_def sourced_def
      coupling_lost_ack_def coupling_submitted_def coupling_prepare_def
    by (simp only: append.simps linked.run_source_coupling.simps)

  have certificate: "certificate_statement ?cert=
    \<lparr>statement_binding=?b,statement_status=Reversed\<rparr>"
    by (simp add: linked_certificate_def sample_statement_def)
  have certificate_epoch: "certificate_epoch ?cert=8"
    by (simp add: linked_certificate_def)
  have certificate_ok: "linked.certificate_ok ?cert"
    using linked_certificates_pass_the_parent_checker[of 22] by simp
  have return_binding: "request_binding ?request=?b"
    and return_certificate: "request_certificate ?request=?cert"
    using linked_return_request_projection by blast+
  have binding_operation: "binding_operation ?b=Destination_Credit"
    and binding_positive: "0<binding_amount ?b"
    by (simp_all add: sample_binding_def example_binding_def)
  have lost_core: "coupled_core (coupling_lost_ack 22)=coupled_core (coupling_submitted 22)"
    and lost_effect: "boundary_has_effect ?b
      (controlled_endpoint (coupled_source (coupling_lost_ack 22)))"
    using lost_ack_source_projection[of 22] by auto
  have lost_outcome: "controlled_outcomes (coupled_source (coupling_lost_ack 22)) (binding_key ?b)=None"
    by (simp add: coupling_lost_ack_def coupling_source_result_def coupling_submitted_projection
      controlled_boundary_def initial_controlled_source_def Let_def)
  have lost_receipts: "coupled_receipts (coupling_lost_ack 22)=[]"
    by (simp add: coupling_lost_ack_def coupling_source_result_def coupling_example_data Let_def)
  have source_guard: "coupling_guard True (coupling_lost_ack 22) ?source_command"
    using lost_effect
    by (simp add: coupling_effect_witness_def boundary_evidence_exact sample_request_def)
  define source_core where "source_core=fst (linked.execute_finality_client
    ?source_command (coupled_core (coupling_submitted 22)))"
  have source_reply: "snd (linked.execute_finality_client
      ?source_command (coupled_core (coupling_submitted 22)))=Protocol_Response Source_Debited"
    by (simp add: coupling_example_data Let_def)
  have source_step: "linked.source_coupling_step
      (Coupling_Client True ?source_command) (coupling_lost_ack 22)=
    ((coupling_lost_ack 22)\<lparr>coupled_core:=source_core\<rparr>,
      Coupling_Client_Reply (Protocol_Response Source_Debited))"
    using source_guard source_reply
    by (simp add: linked.coupling_client_step_def source_core_def lost_core Let_def)
  have sourced_core: "coupled_core sourced=source_core"
    and sourced_source: "coupled_source sourced=coupled_source (coupling_lost_ack 22)"
    and sourced_receipts: "coupled_receipts sourced=[]"
    by (simp_all add: sourced_def source_step[unfolded linked.source_coupling_step.simps] lost_receipts)
  have source_effects: "source_effects (machine_state (core_parent source_core))=[?b]"
    and source_pending: "phase_at (machine_state (core_parent source_core)) (binding_key ?b)=Some Source_Pending"
    and source_ownership: "owns_recorded_reservation ?view ?request 0 (vector_lookup [])
      (machine_state (core_parent source_core))"
    and source_context: "current_lock_view source_core 0=?view"
    and source_epoch: "core_epoch source_core=3"
    and source_records: "core_records source_core=(\<lambda>_.None)"
    and source_certificates: "issued_certificates (machine_state (core_parent source_core))=[]"
    by (simp_all add: source_core_def coupling_example_data linked_return_request_def Let_def)

  have remote_reverse: "linked.source_coupling_step
      (Coupling_Source True True (Controlled_Reverse ?b)) sourced=
    (sourced\<lparr>coupled_source:=controlled_record_reversed ?b (coupled_source sourced)\<rparr>,
      Coupling_Source_Reply (Controlled_Outcome_Reply
        \<lparr>statement_binding=?b,statement_status=Reversed\<rparr>))"
    using lost_effect lost_outcome
    by (simp add: coupling_source_result_def controlled_reverse_def sourced_source Let_def)
  have reversed_fact: "controlled_source_fact (coupled_source reversed) (binding_key ?b)=
    Some \<lparr>statement_binding=?b,statement_status=Reversed\<rparr>"
    by (simp add: reversed_def remote_reverse[unfolded linked.source_coupling_step.simps]
      controlled_source_fact_def controlled_record_reversed_def)
  have reversed_core: "coupled_core reversed=source_core"
    and reversed_receipts: "coupled_receipts reversed=[]"
    by (simp_all add: reversed_def remote_reverse[unfolded linked.source_coupling_step.simps]
      sourced_core sourced_receipts)

  have issue_step: "linked.source_coupling_step (Coupling_Issue True ?cert) reversed=
    (reversed\<lparr>coupled_receipts:=[?cert]\<rparr>,Coupling_Receipt_Stored)"
    by (simp add: coupling_issue_result_def issue_source_receipt_def source_receipt_slot_available_def
      reversed_fact reversed_receipts certificate Let_def)
  have issued_core: "coupled_core issued=source_core"
    and issued_source: "coupled_source issued=coupled_source reversed"
    and issued_receipts: "coupled_receipts issued=[?cert]"
    by (simp_all add: issued_def issue_step[unfolded linked.source_coupling_step.simps] reversed_core)
  have issued_live: "coupling_live_receipt issued ?cert"
    by (simp add: coupling_live_receipt_def issued_source issued_receipts reversed_fact certificate)

  have terminal_execution: "linked.execute_finality_client (Client_Terminal ?cert) source_core=
    ((source_core\<lparr>core_records:=(core_records source_core)(binding_key ?b:=Some ?entry)\<rparr>)
      \<lparr>core_epoch:=4\<rparr>,Terminal_Recorded)"
    by (simp add: linked.execute_finality_client_def linked.finality_step_def
      linked.core_result.simps linked.record_terminal_def certificate_ok certificate
      source_origin_present_def source_effects source_records source_epoch binding_operation binding_positive Let_def)
  define terminal_core where "terminal_core=fst
    (linked.execute_finality_client (Client_Terminal ?cert) source_core)"
  have terminal_step: "linked.source_coupling_step (Coupling_Client True (Client_Terminal ?cert)) issued=
    (issued\<lparr>coupled_core:=terminal_core\<rparr>,Coupling_Client_Reply Terminal_Recorded)"
    using issued_live
    by (simp add: linked.coupling_client_step_def issued_core terminal_core_def terminal_execution Let_def)
  have terminal_parent: "core_parent terminal_core=core_parent source_core"
    and terminal_context: "current_lock_view terminal_core 0=?view"
    and terminal_epoch: "core_epoch terminal_core=4"
    and terminal_record: "core_records terminal_core (binding_key ?b)=Some ?entry"
    by (simp_all add: terminal_core_def terminal_execution current_lock_view_def source_context[unfolded current_lock_view_def])
  have terminal_coupled_core: "coupled_core terminal=terminal_core"
    and terminal_source: "coupled_source terminal=coupled_source reversed"
    and terminal_receipts: "coupled_receipts terminal=[?cert]"
    by (simp_all add: terminal_def terminal_step[unfolded linked.source_coupling_step.simps]
      issued_source issued_receipts)
  have terminal_live: "coupling_live_receipt terminal ?cert"
    by (simp add: coupling_live_receipt_def terminal_source terminal_receipts reversed_fact certificate)

  have certificate_publication: "linked.publish_source_certificate ?cert (core_parent source_core)=
    commit_reservation_event (Certificate_Event ?cert) (core_parent source_core)"
    by (simp add: linked.publish_source_certificate_def certificate_ok certificate source_effects Let_def)
  have publication_execution: "linked.execute_finality_client
      (Client_Protocol 0 0 (Certificate_Intent ?cert)) terminal_core=
    ((terminal_core\<lparr>core_parent:=commit_reservation_event (Certificate_Event ?cert)
        (core_parent source_core)\<rparr>)\<lparr>core_epoch:=5\<rparr>,Internal_Completed)"
    by (simp add: linked.execute_finality_client_def linked.finality_step_def linked.core_result.simps
      linked.invoke_protocol_def linked.intent_result.simps certificate terminal_record
      terminal_parent terminal_epoch exact_record_reference_def record_reference_def certificate_publication Let_def)
  define published_core where "published_core=fst (linked.execute_finality_client
    (Client_Protocol 0 0 (Certificate_Intent ?cert)) terminal_core)"
  have publication_step: "linked.source_coupling_step
      (Coupling_Client True (Client_Protocol 0 0 (Certificate_Intent ?cert))) terminal=
    (terminal\<lparr>coupled_core:=published_core\<rparr>,Coupling_Client_Reply Internal_Completed)"
    using terminal_live
    by (simp add: linked.coupling_client_step_def terminal_coupled_core published_core_def
      publication_execution Let_def)
  have published_parent: "core_parent published_core=
      commit_reservation_event (Certificate_Event ?cert) (core_parent source_core)"
    and published_context: "current_lock_view published_core 0=?view"
    and published_epoch: "core_epoch published_core=5"
    and published_record: "core_records published_core (binding_key ?b)=Some ?entry"
    by (simp_all add: published_core_def publication_execution terminal_record
      current_lock_view_def terminal_context[unfolded current_lock_view_def])
  have published_coupled_core: "coupled_core published=published_core"
    and published_source: "coupled_source published=coupled_source reversed"
    and published_receipts: "coupled_receipts published=[?cert]"
    by (simp_all add: published_def publication_step[unfolded linked.source_coupling_step.simps]
      terminal_source terminal_receipts)
  have published_live: "coupling_live_receipt published ?cert"
    by (simp add: coupling_live_receipt_def published_source published_receipts reversed_fact certificate)
  have published_fact: "controlled_source_fact (coupled_source published) (binding_key ?b)=
    Some \<lparr>statement_binding=?b,statement_status=Reversed\<rparr>"
    by (simp only: published_source reversed_fact)
  have published_ownership: "owns_recorded_reservation ?view ?request 0 (vector_lookup [])
    (machine_state (core_parent published_core))"
    by (simp add: published_parent source_link_certificate_event_frames
      source_link_issued_certificate_update_frames source_ownership)
  have published_pending: "phase_at (machine_state (core_parent published_core))
    (binding_key ?b)=Some Source_Pending"
    by (simp add: published_parent source_link_certificate_event_frames
      source_link_issued_certificate_update_frames source_pending)
  have published_evidence: "linked.reversed_source_evidence (lock_authority ?view) ?request
    (machine_state (core_parent published_core))"
    unfolding linked.reversed_source_evidence_def
    by (simp add: return_binding return_certificate certificate_ok certificate certificate_epoch published_parent
      commit_reservation_event_def source_certificates sample_source_context_def sample_context_def example_context_def)
  have parent_release: "snd (linked.release_to_source ?view ?request 0 (vector_lookup [])
    (core_parent published_core))=Reservation_Released"
    by (simp only: linked.evidence_release_exact_guard)
       (use published_ownership published_pending published_evidence
          in \<open>simp add: return_binding\<close>)
  have child_release: "snd (linked.execute_finality_client ?return_command published_core)=
    Protocol_Response Reservation_Released"
    using parent_release
    by (simp add: linked.execute_finality_client_def linked.core_result.simps linked.invoke_protocol_def
      linked.intent_result.simps lift_protocol_result_def published_context published_record
      return_binding return_certificate exact_record_reference_def record_reference_def Let_def)
  have return_guard: "coupling_guard True published ?return_command"
    using published_live published_fact
    by (simp add: return_binding return_certificate)
  have coupled_release: "snd (linked.source_coupling_step
      (Coupling_Client True ?return_command) published)=
    Coupling_Client_Reply (Protocol_Response Reservation_Released)"
    using return_guard published_fact child_release
    by (simp add: linked.coupling_client_step_def linked.mirror_source_return_def
      return_binding return_certificate published_coupled_core Let_def)
  have release: "snd (linked.source_coupling_step
      (Coupling_Client True ?return_command) coupling_before_return)=
    Coupling_Client_Reply (Protocol_Response Reservation_Released)"
    by (simp only: word coupled_release)
  have source_frame:
    "coupled_source (fst (linked.source_coupling_step
      (Coupling_Client True ?return_command) coupling_before_return))=
      coupled_source coupling_before_return"
    by (auto simp: linked.coupling_client_step_def Let_def)
  show ?thesis using release source_frame by blast
qed

text \<open>The first negative runs the existing child Source function without
  the adapter evidence guard. The second executes the remote source effect,
  loses its acknowledgment, and then runs the existing child Fence function
  while the local parent still says Submitted. The guarded dispatcher rejects
  both unsafe calls. Its transmission history is not cleared by lost replies.

  Every client and environment operation uses this dispatcher; admitted client
  effects are the existing child effects. Blocked keys cannot acquire an
  effect in any later finite joint execution. A never-sent local block and an
  authoritative source fence are distinct concrete justifications. Neither
  a local missing acknowledgment nor an unverified journal is a no-effect proof.
  Physical source control, receipt authentication, exclusive adapter routing
  and atomic persistence remain implementation obligations.\<close>

end
