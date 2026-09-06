(* SPDX-License-Identifier: BSD-3-Clause *)
theory Credit_Once_Kernel
  imports Message_Types
begin

section \<open>The Exact Condition for Local Markers to Give Global Uniqueness\<close>

definition once_receive :: "(execution_context \<Rightarrow> execution_request \<Rightarrow> bool)
  \<Rightarrow>
  message_route \<Rightarrow> execution_context \<Rightarrow> execution_request \<Rightarrow>
  message_state \<Rightarrow> message_state \<times> message_reply" where
  "once_receive admission route c r s =
     (if \<not> admission c r then (s, Message_Rejected)
      else if credit_marker (request_binding r) \<in> consumed_at s
      then (s, Duplicate_Credit (request_binding r))
      else (record_credit (request_binding r) s, New_Credit (request_binding r)))"

fun run_once :: "(execution_context \<Rightarrow> execution_request \<Rightarrow> bool) \<Rightarrow>
  (message_route \<times> execution_context \<times> execution_request) list \<Rightarrow> message_state
    \<Rightarrow> message_state" where
  "run_once admission [] s = s"
| "run_once admission ((route,c,r)#xs) s = run_once admission xs (fst (once_receive admission route c r s))"

definition destination_functional :: "(execution_context \<Rightarrow> execution_request \<Rightarrow> bool)
  \<Rightarrow> bool" where
  "destination_functional admission \<longleftrightarrow>
    (\<forall>c r d t. admission c r \<and> admission d t \<and>
       binding_key (request_binding r) = binding_key (request_binding t) \<longrightarrow>
       binding_destination (request_binding r) = binding_destination (request_binding t))"

definition kernel_invariant :: "(execution_context \<Rightarrow> execution_request \<Rightarrow> bool)
  \<Rightarrow> message_state \<Rightarrow> bool" where
  "kernel_invariant admission s \<longleftrightarrow>
     consumed_at s = set (map credit_marker (credit_history s)) \<and>
     distinct (map binding_key (credit_history s)) \<and>
     (\<forall>b \<in> set (credit_history s). \<exists>c r. admission c r \<and> request_binding r = b)"

lemma kernel_initial: "kernel_invariant admission empty_message_state"
  by (simp add: kernel_invariant_def empty_message_state_def)

lemma functional_new_key_fresh:
  assumes functional: "destination_functional admission"
    and inv: "kernel_invariant admission s"
    and accept: "admission c r"
    and unused: "credit_marker (request_binding r) \<notin> consumed_at s"
  shows "binding_key (request_binding r) \<notin> set (map binding_key (credit_history s))"
proof
  assume old: "binding_key (request_binding r) \<in> set (map binding_key (credit_history s))"
  obtain b where b: "b \<in> set (credit_history s)" "binding_key b = binding_key (request_binding r)"
    using old by auto
  obtain d t where origin: "admission d t" "request_binding t = b"
    using inv b(1) unfolding kernel_invariant_def by blast
  have same_destination: "binding_destination b = binding_destination (request_binding r)"
    using functional origin accept b(2) unfolding destination_functional_def by blast
  have same_marker: "credit_marker b = credit_marker (request_binding r)"
    unfolding credit_marker_def using b(2) same_destination by simp
  have "credit_marker b \<in> consumed_at s"
    using inv b(1) unfolding kernel_invariant_def by auto
  then show False using unused same_marker by simp
qed

lemma kernel_record_preserves:
  assumes "destination_functional admission" "kernel_invariant admission s" "admission c r"
    "credit_marker (request_binding r) \<notin> consumed_at s"
  shows "kernel_invariant admission (record_credit (request_binding r) s)"
  using functional_new_key_fresh[OF assms] assms(2,3)
  by (auto simp: kernel_invariant_def record_credit_def)

lemma kernel_step_preserves:
  assumes "destination_functional admission" "kernel_invariant admission s"
  shows "kernel_invariant admission (fst (once_receive admission route c r s))"
  using assms kernel_record_preserves
  by (auto simp: once_receive_def split: if_splits)

lemma kernel_run_preserves:
  assumes functional: "destination_functional admission" and inv: "kernel_invariant admission s"
  shows "kernel_invariant admission (run_once admission xs s)"
  using inv
proof (induction xs arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons input rest)
  obtain route c r where input: "input = (route,c,r)" by (cases input) auto
  have step: "kernel_invariant admission (fst (once_receive admission route c r s))"
    using kernel_step_preserves[OF functional Cons.prems] .
  have "kernel_invariant admission (run_once admission rest (fst (once_receive admission route c r s)))"
    using Cons.IH[OF step] .
  then show ?case by (simp only: input run_once.simps)
qed

lemma distinct_key_count_bound:
  "distinct xs \<Longrightarrow> count_list xs key \<le> 1"
  by (induction xs) (auto simp: count_list_0_iff)

theorem functional_destinations_suffice:
  assumes "destination_functional admission"
  shows "count_list (map binding_key (credit_history (run_once admission xs empty_message_state))) key \<le>
    1"
proof -
  have "kernel_invariant admission (run_once admission xs empty_message_state)"
    using kernel_run_preserves[OF assms kernel_initial] .
  then have "distinct (map binding_key (credit_history (run_once admission xs empty_message_state)))"
    unfolding kernel_invariant_def by simp
  then show ?thesis by (rule distinct_key_count_bound)
qed

lemma two_destinations_generate_two_credits:
  assumes a: "admission c r" and b: "admission d t"
    and key: "binding_key (request_binding r) = binding_key (request_binding t)"
    and different: "binding_destination (request_binding r) \<noteq> binding_destination (request_binding
      t)"
  shows "count_list (map binding_key (credit_history
      (run_once admission [(Validated_Route,c,r),(Bypass_Route,d,t)] empty_message_state)))
        (binding_key (request_binding r)) = 2"
proof -
  have marker: "credit_marker (request_binding t) \<noteq> credit_marker (request_binding r)"
    using different by (auto simp: credit_marker_def)
  show ?thesis
    by (simp add: once_receive_def a b marker record_credit_def empty_message_state_def key)
qed

theorem local_markers_give_global_once_iff:
  "(\<forall>xs key. count_list (map binding_key (credit_history
      (run_once admission xs empty_message_state))) key \<le> 1)
    \<longleftrightarrow> destination_functional admission"
proof
  assume bound: "\<forall>xs key. count_list (map binding_key (credit_history
    (run_once admission xs empty_message_state))) key \<le> 1"
  show "destination_functional admission"
    unfolding destination_functional_def
  proof (intro allI impI)
    fix c r d t
    assume admitted_pair: "admission c r \<and> admission d t \<and>
      binding_key (request_binding r) = binding_key (request_binding t)"
    show "binding_destination (request_binding r) = binding_destination (request_binding t)"
    proof (rule ccontr)
      assume different: "binding_destination (request_binding r) \<noteq> binding_destination
        (request_binding t)"
      have two: "count_list (map binding_key (credit_history
        (run_once admission [(Validated_Route,c,r),(Bypass_Route,d,t)] empty_message_state)))
        (binding_key (request_binding r)) = 2"
        using two_destinations_generate_two_credits admitted_pair different by blast
      have "count_list (map binding_key (credit_history
        (run_once admission [(Validated_Route,c,r),(Bypass_Route,d,t)] empty_message_state)))
        (binding_key (request_binding r)) \<le> 1" using bound by blast
      with two show False by simp
    qed
  qed
next
  assume "destination_functional admission"
  then show "\<forall>xs key. count_list (map binding_key (credit_history
    (run_once admission xs empty_message_state))) key \<le> 1"
    using functional_destinations_suffice by blast
qed

text \<open>The equivalence characterizes this state-independent admission and
  destination-key marker kernel. It does not make authentication, payload
  integrity or current authorization redundant. Those properties impose
  additional obligations on the admission function.\<close>

end
