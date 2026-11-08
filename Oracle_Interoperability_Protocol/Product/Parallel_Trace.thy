theory Parallel_Trace
  imports Parallel_Exchange
begin

section \<open>Adjacent exchanges at reached prefixes preserve the whole result\<close>

fun run_occurrences where
  "run_occurrences execute [] s replies = (s, replies)"
| "run_occurrences execute ((label, action) # rest) s replies =
    (let result = execute action s
     in run_occurrences execute rest (fst result) (replies(label := Some (snd result))))"

lemma run_occurrences_append:
  "run_occurrences execute (prefix @ suffix) s replies =
   (let middle = run_occurrences execute prefix s replies
     in run_occurrences execute suffix (fst middle) (snd middle))"
  by (induction prefix arbitrary: s replies) (auto simp: Let_def split: prod.splits)

inductive verified_adjacent_swap for execute compatible initial where
  swap_at_reached_prefix:
    "label_a \<noteq> label_b \<Longrightarrow>
     compatible a b (fst (run_occurrences execute prefix initial (\<lambda>_. None))) \<Longrightarrow>
     verified_adjacent_swap execute compatible initial
       (prefix @ [(label_a,a),(label_b,b)] @ suffix) (prefix @ [(label_b,b),(label_a,a)] @ suffix)"

lemma one_adjacent_exchange_keeps_the_state_and_each_occurrence_reply:
  assumes exchange: "verified_adjacent_swap execute compatible initial first second"
    and pair: "\<And>a b s. compatible a b s \<Longrightarrow> service_ordered_pair execute a b s = service_exchanged_pair execute a b s"
  shows "run_occurrences execute first initial (\<lambda>_. None) = run_occurrences execute second initial (\<lambda>_. None)"
proof (cases rule: verified_adjacent_swap.cases[OF exchange])
  fix label_a label_b a b prefix suffix
  assume labels: "label_a \<noteq> label_b"
    and compatible: "compatible a b (fst (run_occurrences execute prefix initial (\<lambda>_. None)))"
    and first: "first = prefix @ [(label_a,a),(label_b,b)] @ suffix"
    and second: "second = prefix @ [(label_b,b),(label_a,a)] @ suffix"
  let ?middle = "run_occurrences execute prefix initial (\<lambda>_. None)"
  have state_and_replies: "service_ordered_pair execute a b (fst ?middle) = service_exchanged_pair execute a b (fst ?middle)"
    by (rule pair[OF compatible])
  show ?thesis unfolding first second
    using state_and_replies labels
    by (simp add: run_occurrences_append Let_def service_ordered_pair_def service_exchanged_pair_def fun_upd_twist)
qed

lemma finite_adjacent_exchanges_preserve_product_effects_and_replies:
  assumes "rtranclp (verified_adjacent_swap execute compatible initial) first second"
    and pair: "\<And>a b s. compatible a b s \<Longrightarrow> service_ordered_pair execute a b s = service_exchanged_pair execute a b s"
  shows "run_occurrences execute first initial (\<lambda>_. None) = run_occurrences execute second initial (\<lambda>_. None)"
  using assms(1)
  by (induction rule: rtranclp_induct) (auto intro: one_adjacent_exchange_keeps_the_state_and_each_occurrence_reply[OF _ pair])

definition compatible_retained_actions where
  "compatible_retained_actions connection a b retained \<longleftrightarrow>
    compatible_service_actions a b (service_settlement (reopen_retained_product connection retained))"

datatype scheduling_choice = Exchange_At_Validated_State | Run_In_Input_Order

definition consume_pair_schedule where
  "consume_pair_schedule connection execute requested first second retained =
    (if requested \<and> compatible_retained_actions connection first second retained then
       (Exchange_At_Validated_State, service_exchanged_pair execute first second retained)
     else (Run_In_Input_Order, service_ordered_pair execute first second retained))"

lemma conflicting_pair_is_revalidated_in_input_order:
  assumes "\<not> compatible_retained_actions connection first second retained"
  shows "consume_pair_schedule connection execute requested first second retained =
    (Run_In_Input_Order, service_ordered_pair execute first second retained)"
  using assms by (simp add: consume_pair_schedule_def)

lemma only_the_currently_compatible_pair_can_take_the_exchange_path:
  assumes "fst (consume_pair_schedule connection execute requested first second retained) = Exchange_At_Validated_State"
  shows "requested \<and> compatible_retained_actions connection first second retained"
  using assms by (simp add: consume_pair_schedule_def split: if_splits)

context source_attestation
begin

theorem the_actual_product_finite_exchange_closure:
  fixes run :: "'token retained_service_action \<Rightarrow> retained_product \<Rightarrow> retained_product \<times> scheduled_service_reply"
    and directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack connection
  defines "run \<equiv> schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack connection"
  assumes exchanges: "rtranclp (verified_adjacent_swap run (compatible_retained_actions connection) initial) first second"
  shows "run_occurrences run first initial (\<lambda>_. None) = run_occurrences run second initial (\<lambda>_. None)"
proof (rule finite_adjacent_exchanges_preserve_product_effects_and_replies[OF exchanges])
  fix a b :: "'token retained_service_action" and retained :: retained_product
  assume compatible: "compatible_retained_actions connection a b retained"
  show "service_ordered_pair run a b retained = service_exchanged_pair run a b retained"
    unfolding run_def
    by (rule compatible_actual_product_actions_exchange[OF compatible[unfolded compatible_retained_actions_def]])
qed

end

end
