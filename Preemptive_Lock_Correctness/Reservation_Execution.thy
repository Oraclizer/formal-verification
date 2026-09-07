(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Execution
  imports Reservation_Protocol
begin

section \<open>Finite Interleavings and Replay\<close>

datatype reservation_action =
    Acquire_Action lock_context execution_request "nat \<Rightarrow> nat" nat
  | Dispatch_Action lock_context execution_request nat "nat \<Rightarrow> nat"
  | Source_Action lock_context execution_request nat "nat \<Rightarrow> nat"
  | Cancel_Action lock_context execution_request nat "nat \<Rightarrow> nat"
  | Fence_Action lock_context execution_request nat "nat \<Rightarrow> nat"
  | Reassign_Action lock_context execution_request nat
  | Write_Action lock_context execution_request nat "nat \<Rightarrow> nat" nat
  | Time_Action nat
  | Publish_Action source_certificate
  | Deliver_Action message_route execution_context execution_request
  | Return_Action lock_context execution_request nat "nat \<Rightarrow> nat"
  | Reconcile_Action lock_context execution_request nat "nat \<Rightarrow> nat"
  | Descendant_Action lock_context execution_request transfer_binding nat nat nat
  | Read_Action lock_context execution_request
  | Restart_Action

definition restart_reservation_machine :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  reservation_machine \<Rightarrow> reservation_machine" where
  "restart_reservation_machine balances m =
    m\<lparr>machine_state:=replay_reservation_events balances(machine_journal m)\<rparr>"

context source_attestation
begin

fun reservation_step :: "(source_account \<Rightarrow> nat) \<Rightarrow> reservation_action \<Rightarrow>
  reservation_machine \<Rightarrow> reservation_machine" where
  "reservation_step balances (Acquire_Action c r versions duration) m = fst(acquire_reservation c r versions duration m)"
| "reservation_step balances (Dispatch_Action c r g versions) m = fst(dispatch_source c r g versions m)"
| "reservation_step balances (Source_Action c r g versions) m = fst(execute_source_effect c r g versions m)"
| "reservation_step balances (Cancel_Action c r g versions) m = fst(cancel_before_dispatch c r g versions m)"
| "reservation_step balances (Fence_Action c r g versions) m = fst(fence_unexecuted_source c r g versions m)"
| "reservation_step balances (Reassign_Action c r duration) m = fst(reassign_worker c r duration m)"
| "reservation_step balances (Write_Action c r g versions value) m = fst(write_asset_data c r g versions value m)"
| "reservation_step balances (Time_Action elapsed) m = advance_reservation_time elapsed m"
| "reservation_step balances (Publish_Action cert) m = publish_source_certificate cert m"
| "reservation_step balances (Deliver_Action route c r) m = fst(deliver_reserved_credit route c r m)"
| "reservation_step balances (Return_Action c r g versions) m = fst(release_to_source c r g versions m)"
| "reservation_step balances (Reconcile_Action c r g versions) m = fst(reconcile_recorded_credit c r g versions m)"
| "reservation_step balances (Descendant_Action c r root sender recipient amount) m = fst(execute_descendant c r root sender recipient amount m)"
| "reservation_step balances (Read_Action c r) m = fst(read_source_data c r m)"
| "reservation_step balances Restart_Action m = restart_reservation_machine balances m"

fun run_reservations :: "(source_account \<Rightarrow> nat) \<Rightarrow> reservation_action list \<Rightarrow>
  reservation_machine \<Rightarrow> reservation_machine" where
  "run_reservations balances [] m=m"
| "run_reservations balances (action#rest) m =
     run_reservations balances rest (reservation_step balances action m)"

end

definition journal_agreement :: "(source_account \<Rightarrow> nat) \<Rightarrow> reservation_machine \<Rightarrow> bool"
  where
  "journal_agreement balances m \<longleftrightarrow>
    machine_state m=replay_reservation_events balances(machine_journal m)"

lemma initial_journal_agreement:
  "journal_agreement balances(initial_reservation_machine balances)"
  by (simp add: journal_agreement_def initial_reservation_machine_def replay_reservation_events_def)

lemma replay_append_event:
  "replay_reservation_events balances (events@[event]) =
    apply_reservation_event event(replay_reservation_events balances events)"
  by (simp add: replay_reservation_events_def)

lemma commit_preserves_journal_agreement:
  "journal_agreement balances m \<Longrightarrow> journal_agreement balances(commit_reservation_event event m)"
  by (simp add: journal_agreement_def commit_reservation_event_def replay_append_event)

lemma observe_preserves_journal_agreement:
  "journal_agreement balances m \<Longrightarrow> journal_agreement balances(fst(record_observation r reply m))"
  by (simp add: record_observation_def journal_agreement_def)

lemma restart_has_journal_agreement:
  "journal_agreement balances(restart_reservation_machine balances m)"
  by (simp add: restart_reservation_machine_def journal_agreement_def)

lemma restart_reconstructs_committed_state:
  "journal_agreement balances m \<Longrightarrow> restart_reservation_machine balances m=m"
  by (simp add: journal_agreement_def restart_reservation_machine_def)

context source_attestation
begin

lemmas protocol_definitions = acquire_reservation_def dispatch_source_def execute_source_effect_def
  cancel_before_dispatch_def fence_unexecuted_source_def reassign_worker_def write_asset_data_def advance_reservation_time_def
  publish_source_certificate_def deliver_reserved_credit_def release_to_source_def
  reconcile_recorded_credit_def execute_descendant_def read_source_data_def

theorem reservation_step_preserves_journal:
  assumes "journal_agreement balances m"
  shows "journal_agreement balances(reservation_step balances action m)"
  using assms
  by (cases action)
     (auto simp: protocol_definitions Let_def
       intro: commit_preserves_journal_agreement observe_preserves_journal_agreement
       restart_has_journal_agreement
       split: option.splits message_reply.splits)

theorem finite_interleaving_preserves_journal:
  "journal_agreement balances m \<Longrightarrow>
    journal_agreement balances(run_reservations balances actions m)"
  by (induction actions arbitrary:m)
     (auto intro: reservation_step_preserves_journal)

theorem generated_journal_reconstructs_all_financial_state:
  "restart_reservation_machine balances
    (run_reservations balances actions(initial_reservation_machine balances)) =
    run_reservations balances actions(initial_reservation_machine balances)"
  by (rule restart_reconstructs_committed_state,
      rule finite_interleaving_preserves_journal, rule initial_journal_agreement)

theorem journal_recovery_preserves_finite_continuations:
  assumes "journal_agreement balances m"
  shows "run_reservations balances continuation(restart_reservation_machine balances m)=
    run_reservations balances continuation m"
  using restart_reconstructs_committed_state[OF assms] by simp

end

text \<open>Replay consumes the complete journal generated by these operations
  and the same genesis allocation. The observer's completed history is kept
  separately across a modeled restart; it is not reconstructed from the
  financial journal. New authorization and regulatory views are supplied with
  continuation requests. Authenticity and completeness of an externally
  supplied journal are separate producer obligations.\<close>

end
