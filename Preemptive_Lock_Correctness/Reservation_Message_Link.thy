(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Message_Link
  imports Source_Non_Reuse
begin

section \<open>Source Evidence Is Consumed by the Message Receiver\<close>

context source_attestation
begin

definition published_fact_origin :: "reservation_state \<Rightarrow> bool" where
  "published_fact_origin s \<longleftrightarrow>
    (\<forall>cert\<in>set(issued_certificates s). certificate_ok cert \<and>
      statement_status(certificate_statement cert)\<noteq>Observed \<and>
      statement_binding(certificate_statement cert)\<in>set(source_effects s))"

definition credited_source_origin :: "reservation_state \<Rightarrow> bool" where
  "credited_source_origin s \<longleftrightarrow>
    set(credit_history(received_messages s))\<subseteq>set(source_effects s)"

definition message_source_invariant :: "reservation_state \<Rightarrow> bool" where
  "message_source_invariant s \<longleftrightarrow> published_fact_origin s \<and>
    credited_source_origin s \<and> message_invariant(received_messages s)"

lemma message_source_initial:
  "message_source_invariant(initial_reservation_state balances)"
  by (simp add: message_source_invariant_def published_fact_origin_def credited_source_origin_def
      initial_reservation_state_def empty_message_state_def message_invariant_def)

lemma recorded_credit_history [simp]:
  "credit_history(record_credit b messages)=credit_history messages@[b]"
  by (simp add: record_credit_def)

lemma published_receiver_preserves_message_invariant:
  assumes "message_invariant(received_messages s)"
  shows "message_invariant(fst(published_receive route c r s))"
  using source_attestation.receive_credit_preserves_invariant[
    OF published_verifier_interpretation assms]
  by (simp add: published_receive_def)

lemma new_published_credit_has_earlier_source_effect:
  assumes origin: "published_fact_origin s"
    and credit: "snd(published_receive route c r s)=New_Credit b"
  shows "b\<in>set(source_effects s)"
  using origin credit
  by (auto simp: published_fact_origin_def published_receive_expansion
      credit_admissible_def authenticated_request_def split: if_splits)

lemma record_delivered_credit_preserves_parent:
  assumes "message_invariant(received_messages s)"
    "snd(published_receive route c r s)=New_Credit b"
  shows "message_invariant(record_credit b(received_messages s))"
proof -
  have safe: "message_invariant(fst(published_receive route c r s))"
    by (rule published_receiver_preserves_message_invariant[OF assms(1)])
  have result: "fst(published_receive route c r s)=record_credit b(received_messages s)"
    using assms(2) by (auto simp: published_receive_expansion split: if_splits)
  show ?thesis using safe result by simp
qed

theorem actual_parent_message_projection:
  "received_messages(machine_state(fst(deliver_reserved_credit route c r m)))=
    fst(published_receive route c r(machine_state m))"
  by (auto simp: deliver_reserved_credit_def published_receive_expansion
      record_observation_def commit_reservation_event_def split: if_splits)

lemma delivery_preserves_message_source:
  assumes "message_source_invariant(machine_state m)"
  shows "message_source_invariant(machine_state(fst(deliver_reserved_credit route c r m)))"
  using assms
  by (auto simp: deliver_reserved_credit_def message_source_invariant_def
      published_fact_origin_def credited_source_origin_def record_observation_def
      commit_reservation_event_def
      intro: record_delivered_credit_preserves_parent new_published_credit_has_earlier_source_effect
      split: message_reply.splits)

theorem reservation_step_preserves_message_source:
  assumes inv: "message_source_invariant(machine_state m)" and journal: "journal_agreement balances m"
  shows "message_source_invariant(machine_state(reservation_step balances action m))"
proof (cases action)
  case (Deliver_Action route c r)
  then show ?thesis using delivery_preserves_message_source[OF inv] by simp
next
  case Restart_Action
  then show ?thesis using restart_reconstructs_committed_state[OF journal] inv by simp
qed (use inv in \<open>auto simp: protocol_definitions Let_def message_source_invariant_def
  published_fact_origin_def credited_source_origin_def record_observation_def commit_reservation_event_def
  set_phase_def finish_reservation_def split: option.splits\<close>)

theorem finite_interleaving_preserves_message_source:
  assumes "message_source_invariant(machine_state m)" "journal_agreement balances m"
  shows "message_source_invariant(machine_state(run_reservations balances actions m))"
  using assms
  by (induction actions arbitrary:m)
     (auto intro: reservation_step_preserves_message_source reservation_step_preserves_journal)

lemma generated_message_source_invariant:
  "message_source_invariant(machine_state
    (run_reservations balances actions(initial_reservation_machine balances)))"
proof (rule finite_interleaving_preserves_message_source)
  show "message_source_invariant(machine_state(initial_reservation_machine balances))"
    by (simp add: initial_reservation_machine_def message_source_initial)
  show "journal_agreement balances(initial_reservation_machine balances)"
    by (rule initial_journal_agreement)
qed

theorem source_non_reuse_and_destination_once:
  "count_list(map binding_key(source_effects(machine_state
       (run_reservations balances actions(initial_reservation_machine balances)))))key\<le>1 \<and>
   count_list(map binding_key(credit_history(received_messages(machine_state
       (run_reservations balances actions(initial_reservation_machine balances))))))key\<le>1 \<and>
   set(credit_history(received_messages(machine_state
       (run_reservations balances actions(initial_reservation_machine balances)))))\<subseteq>
     set(source_effects(machine_state(run_reservations balances actions(initial_reservation_machine balances))))"
proof -
  have inv: "message_source_invariant(machine_state
    (run_reservations balances actions(initial_reservation_machine balances)))"
    by (rule generated_message_source_invariant)
  have distinct: "distinct(map binding_key(credit_history(received_messages(machine_state
    (run_reservations balances actions(initial_reservation_machine balances))))))"
    using inv unfolding message_source_invariant_def message_invariant_def by blast
  show ?thesis using source_effect_at_most_once[of balances actions key]
    distinct_key_count_bound[OF distinct,of key] inv
    unfolding message_source_invariant_def credited_source_origin_def by blast
qed

theorem accepted_credit_uses_prior_source:
  assumes "message_source_invariant(machine_state m)"
    "snd(deliver_reserved_credit route c r m)=Delivery_Response(New_Credit b)"
  shows "b\<in>set(source_effects(machine_state m))"
  using assms new_published_credit_has_earlier_source_effect
  by (auto simp: deliver_reserved_credit_def record_observation_def message_source_invariant_def
      split: message_reply.splits)

text \<open>The source effect is in the state before this delivery, not merely
  in the resulting history. The receiver projection invokes the existing
  message implementation. These results connect source control to destination
  uniqueness; they do not establish distributed observational atomicity.\<close>

end

end
