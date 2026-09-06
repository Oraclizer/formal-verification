(* SPDX-License-Identifier: BSD-3-Clause *)
theory Message_Execution
  imports Source_Certificates Credit_Once_Kernel
begin

section \<open>Destination Credit Execution\<close>

context source_attestation
begin

definition credit_admissible :: "execution_context \<Rightarrow> execution_request \<Rightarrow> bool" where
  "credit_admissible c r \<longleftrightarrow> authenticated_request c r \<and>
     binding_operation (request_binding r) = Destination_Credit \<and>
     0 < binding_amount (request_binding r)"

definition receive_credit :: "message_route \<Rightarrow> execution_context \<Rightarrow> execution_request
  \<Rightarrow> message_state \<Rightarrow> message_state \<times> message_reply" where
  "receive_credit route c r s =
     (if \<not> credit_admissible c r then (s, Message_Rejected)
      else if credit_marker (request_binding r) \<in> consumed_at s
      then (s, Duplicate_Credit (request_binding r))
      else (record_credit (request_binding r) s, New_Credit (request_binding r)))"

lemma receive_credit_is_local_once_kernel:
  "receive_credit route c r s = once_receive credit_admissible route c r s"
  by (simp only: receive_credit_def once_receive_def)

lemma authenticated_destinations_are_functional:
  "destination_functional credit_admissible"
  unfolding destination_functional_def
proof (intro allI impI)
  fix c r d t
  assume admitted: "credit_admissible c r \<and> credit_admissible d t \<and>
    binding_key (request_binding r) = binding_key (request_binding t)"
  have first: "stable_source (binding_key (request_binding r)) =
    Some \<lparr>statement_binding = request_binding r, statement_status = Finalized\<rparr>"
    using request_has_stable_binding admitted unfolding credit_admissible_def by blast
  have second: "stable_source (binding_key (request_binding t)) =
    Some \<lparr>statement_binding = request_binding t, statement_status = Finalized\<rparr>"
    using request_has_stable_binding admitted unfolding credit_admissible_def by blast
  have same: "Some (\<lparr>statement_binding = request_binding r, statement_status = Finalized\<rparr> ::
    source_statement) =
    Some \<lparr>statement_binding = request_binding t, statement_status = Finalized\<rparr>"
    using first second admitted by metis
  show "binding_destination (request_binding r) = binding_destination (request_binding t)"
    using arg_cong[OF same, where f="\<lambda>x. binding_destination (statement_binding (the x))"]
    by (simp only: option.sel source_statement.select_convs)
qed

definition message_invariant :: "message_state \<Rightarrow> bool" where
  "message_invariant s \<longleftrightarrow>
     consumed_at s = set (map credit_marker (credit_history s)) \<and>
     distinct (map binding_key (credit_history s)) \<and>
     (\<forall>b \<in> set (credit_history s). stable_source (binding_key b) =
       Some \<lparr>statement_binding = b, statement_status = Finalized\<rparr>)"

lemma empty_message_invariant: "message_invariant empty_message_state"
  by (simp add: message_invariant_def empty_message_state_def)

lemma accepted_new_key_is_fresh:
  assumes inv: "message_invariant s"
    and admitted: "credit_admissible c r"
    and unused: "credit_marker (request_binding r) \<notin> consumed_at s"
  shows "binding_key (request_binding r) \<notin> set (map binding_key (credit_history s))"
proof
  assume old: "binding_key (request_binding r) \<in> set (map binding_key (credit_history s))"
  then obtain b where b: "b \<in> set (credit_history s)" "binding_key b = binding_key (request_binding r)"
    by auto
  have old_fact: "stable_source (binding_key b) =
    Some \<lparr>statement_binding = b, statement_status = Finalized\<rparr>"
    using inv b(1) unfolding message_invariant_def by blast
  have authenticated: "authenticated_request c r" using admitted unfolding credit_admissible_def by simp
  have new_fact: "stable_source (binding_key (request_binding r)) =
    Some \<lparr>statement_binding = request_binding r, statement_status = Finalized\<rparr>"
    using request_has_stable_binding[OF authenticated] .
  have source_eq:
    "stable_source (binding_key b) = stable_source (binding_key (request_binding r))"
    by (rule arg_cong[OF b(2)])
  have some_eq:
    "Some (\<lparr>statement_binding = b, statement_status = Finalized\<rparr> :: source_statement) =
      Some \<lparr>statement_binding = request_binding r, statement_status = Finalized\<rparr>"
    by (rule trans[OF trans[OF old_fact[symmetric] source_eq] new_fact])
  have same: "b = request_binding r"
    using arg_cong[OF some_eq, where f = "\<lambda>x. statement_binding (the x)"]
    by (simp only: option.sel source_statement.select_convs)
  have "credit_marker b \<in> consumed_at s"
    using inv b(1) unfolding message_invariant_def by auto
  with same unused show False by simp
qed

lemma record_new_credit_preserves_invariant:
  assumes inv: "message_invariant s"
    and admitted: "credit_admissible c r"
    and unused: "credit_marker (request_binding r) \<notin> consumed_at s"
  shows "message_invariant (record_credit (request_binding r) s)"
proof -
  have fresh: "binding_key (request_binding r) \<notin> set (map binding_key (credit_history s))"
    using accepted_new_key_is_fresh[OF inv admitted unused] .
  have fact: "stable_source (binding_key (request_binding r)) =
    Some \<lparr>statement_binding = request_binding r, statement_status = Finalized\<rparr>"
    using request_has_stable_binding admitted unfolding credit_admissible_def by blast
  show ?thesis using inv fresh fact
    by (auto simp: message_invariant_def record_credit_def)
qed

theorem receive_credit_preserves_invariant:
  assumes "message_invariant s"
  shows "message_invariant (fst (receive_credit route c r s))"
  using assms record_new_credit_preserves_invariant
  by (auto simp: receive_credit_def split: if_splits)

fun run_messages :: "(message_route \<times> execution_context \<times> execution_request) list
  \<Rightarrow> message_state \<Rightarrow> message_state" where
  "run_messages [] s = s"
| "run_messages ((route,c,r)#rest) s = run_messages rest (fst (receive_credit route c r s))"

theorem arbitrary_delivery_trace_preserves_invariant:
  assumes "message_invariant s"
  shows "message_invariant (run_messages trace s)"
  using assms
proof (induction trace arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons input rest)
  obtain route c r where input: "input = (route,c,r)"
    by (cases input) auto
  have next_inv: "message_invariant (fst (receive_credit route c r s))"
    using receive_credit_preserves_invariant[OF Cons.prems] .
  have "message_invariant (run_messages rest (fst (receive_credit route c r s)))"
    using Cons.IH[OF next_inv] .
  then show ?case by (simp only: input run_messages.simps)
qed

lemma run_messages_is_kernel_run:
  "run_messages xs s = run_once credit_admissible xs s"
  by (induction xs arbitrary: s)
     (auto simp: receive_credit_is_local_once_kernel split: prod.splits)

theorem family_wide_at_most_once:
  "count_list (map binding_key (credit_history (run_messages trace empty_message_state))) key \<le> 1"
proof -
  have "count_list (map binding_key (credit_history
    (run_once credit_admissible trace empty_message_state))) key \<le> 1"
    using functional_destinations_suffice[OF authenticated_destinations_are_functional] .
  then show ?thesis by (simp only: run_messages_is_kernel_run)
qed

theorem every_executed_credit_has_authenticated_source:
  assumes "b \<in> set (credit_history (run_messages trace empty_message_state))"
  shows "stable_source (binding_key b) =
    Some \<lparr>statement_binding = b, statement_status = Finalized\<rparr>"
  using arbitrary_delivery_trace_preserves_invariant[OF empty_message_invariant] assms
  unfolding message_invariant_def by blast

theorem new_credit_has_current_permission:
  assumes "snd (receive_credit route c r s) = New_Credit b"
  shows "b = request_binding r \<and> current_use_allowed c r \<and>
    statement_binding (certificate_statement (request_certificate r)) = b \<and>
    context_endpoint c = binding_destination b"
  using assms
  by (auto simp: receive_credit_def credit_admissible_def authenticated_request_def split: if_splits)

lemma rejected_or_duplicate_changes_no_credit:
  assumes "snd (receive_credit route c r s) \<noteq> New_Credit (request_binding r)"
  shows "fst (receive_credit route c r s) = s"
  using assms by (auto simp: receive_credit_def split: if_splits)

theorem durable_marker_reconstruction:
  assumes "message_invariant s"
  shows "restore_message_state (credit_history s) = s"
  using assms unfolding message_invariant_def restore_message_state_def
  by (cases s) auto

theorem recovery_preserves_future_deliveries:
  assumes "message_invariant s"
  shows "run_messages continuation (restore_message_state (credit_history s)) = run_messages continuation s"
  using durable_marker_reconstruction[OF assms] by simp

text \<open>This recovery result concerns the recorded destination credits and
  their once markers. It does not authorize discarding unrelated application
  effects, reconstruct current policy from historical evidence, or choose a
  new terminal decision.\<close>

end

end
