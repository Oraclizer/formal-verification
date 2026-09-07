(* SPDX-License-Identifier: BSD-3-Clause *)
theory Source_Non_Reuse
  imports Reservation_Execution
begin

section \<open>Source Effects Cannot Be Reused\<close>

definition source_history_unique :: "reservation_state \<Rightarrow> bool" where
  "source_history_unique s \<longleftrightarrow> distinct(map binding_key(source_effects s))"

lemma source_history_initial:
  "source_history_unique(initial_reservation_state balances)"
  by (simp add: source_history_unique_def initial_reservation_state_def)

lemma source_history_phase [simp]: "source_effects(set_phase key phase s)=source_effects s"
  by (simp add: set_phase_def)

lemma source_history_finish [simp]: "source_effects(finish_reservation key phase s)=source_effects s"
  by (simp add: finish_reservation_def)

context source_attestation
begin

theorem reservation_step_preserves_source_uniqueness:
  assumes "source_history_unique(machine_state m)" "journal_agreement balances m"
  shows "source_history_unique(machine_state(reservation_step balances action m))"
  using assms restart_reconstructs_committed_state[OF assms(2)]
  by (cases action)
     (auto simp: protocol_definitions Let_def source_history_unique_def
       source_was_debited_def record_observation_def commit_reservation_event_def
       set_phase_def finish_reservation_def
       split: option.splits message_reply.splits)

theorem finite_interleaving_preserves_source_uniqueness:
  assumes "source_history_unique(machine_state m)" "journal_agreement balances m"
  shows "source_history_unique(machine_state(run_reservations balances actions m))"
  using assms
  by (induction actions arbitrary:m)
     (auto intro: reservation_step_preserves_source_uniqueness reservation_step_preserves_journal)

theorem source_effect_at_most_once:
  "count_list(map binding_key(source_effects(machine_state
    (run_reservations balances actions(initial_reservation_machine balances)))))key\<le>1"
proof -
  have unique: "source_history_unique(machine_state
    (run_reservations balances actions(initial_reservation_machine balances)))"
  proof (rule finite_interleaving_preserves_source_uniqueness)
    show "source_history_unique(machine_state(initial_reservation_machine balances))"
      by (simp add: initial_reservation_machine_def source_history_initial)
    show "journal_agreement balances(initial_reservation_machine balances)"
      by (rule initial_journal_agreement)
  qed
  show ?thesis using unique unfolding source_history_unique_def by (rule distinct_key_count_bound)
qed

theorem source_history_is_never_discarded:
  assumes "journal_agreement balances m"
  shows "\<exists>suffix. source_effects(machine_state(reservation_step balances action m))=
    source_effects(machine_state m)@suffix"
  using assms restart_reconstructs_committed_state[OF assms]
  by (cases action)
     (auto simp: protocol_definitions Let_def record_observation_def commit_reservation_event_def
       set_phase_def finish_reservation_def
       split: option.splits message_reply.splits)

theorem source_consumption_survives_finite_continuation:
  assumes "journal_agreement balances m" "source_was_debited(machine_state m)key"
  shows "source_was_debited(machine_state(run_reservations balances actions m))key"
  using assms
proof (induction actions arbitrary:m)
  case Nil
  then show ?case by simp
next
  case (Cons action rest)
  obtain suffix where extension:
    "source_effects(machine_state(reservation_step balances action m))=source_effects(machine_state m)@suffix"
    using source_history_is_never_discarded[OF Cons.prems(1)] by blast
  have consumed: "source_was_debited(machine_state(reservation_step balances action m))key"
    using Cons.prems(2) extension unfolding source_was_debited_def by simp
  have journal: "journal_agreement balances(reservation_step balances action m)"
    by (rule reservation_step_preserves_journal[OF Cons.prems(1)])
  show ?case using Cons.IH[OF journal consumed] by simp
qed

end

theorem source_retry_cannot_debit_again:
  assumes "source_was_debited(machine_state m)(binding_key(request_binding r))"
  shows "machine_state(fst(execute_source_effect c r g versions m))=machine_state m"
  using assms by (simp add: execute_source_effect_def Let_def record_observation_def)

theorem timeout_has_no_terminal_or_financial_authority:
  "reservation_at(machine_state(advance_reservation_time elapsed m))=reservation_at(machine_state m) \<and>
    asset_owner(machine_state(advance_reservation_time elapsed m))=asset_owner(machine_state m) \<and>
    source_units(machine_state(advance_reservation_time elapsed m))=source_units(machine_state m) \<and>
    destination_units(machine_state(advance_reservation_time elapsed m))=destination_units(machine_state m) \<and>
    source_effects(machine_state(advance_reservation_time elapsed m))=source_effects(machine_state m) \<and>
    received_messages(machine_state(advance_reservation_time elapsed m))=received_messages(machine_state m)"
  by (simp add: advance_reservation_time_def commit_reservation_event_def)

end
