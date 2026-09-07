(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Recovery
  imports Reservation_Lineage Reservation_Information
begin

section \<open>Rebuilding a Lost Cache from the Complete Journal\<close>

theorem complete_journal_recovers_arbitrary_cache_loss:
  assumes "journal_agreement balances m"
  shows "restart_reservation_machine balances(m\<lparr>machine_state:=lost_cache\<rparr>)=m"
  using assms by (simp add: journal_agreement_def restart_reservation_machine_def)

context source_attestation
begin

theorem complete_journal_preserves_actual_continuations_after_cache_loss:
  assumes "journal_agreement balances m"
  shows "run_reservations balances continuation
    (restart_reservation_machine balances(m\<lparr>machine_state:=lost_cache\<rparr>))=
    run_reservations balances continuation m"
  using complete_journal_recovers_arbitrary_cache_loss[OF assms] by simp

end

lemma mixed_base_journal:
  "journal_agreement sample_balances mixed_base"
  unfolding mixed_base_def sample_initial_def
  by (rule sample.finite_interleaving_preserves_journal[OF initial_journal_agreement])

lemma lineage_history_journal:
  "journal_agreement sample_balances(lineage_history root)"
  using sample.reservation_step_preserves_journal[OF mixed_base_journal,
    of "Descendant_Action(sample_context ACTIVE)(spend_request root 4 5)(sample_binding root)3 4 5"]
  by (simp add: lineage_history_def)

lemma actual_recovery_keeps_lawful_onward_spending:
  "snd(execute_descendant(sample_context ACTIVE)(spend_request 17 5 1)(sample_binding 17)4 5 1
    (restart_reservation_machine sample_balances((lineage_history 17)\<lparr>
      machine_state:=initial_reservation_state sample_balances\<rparr>)))=Descendant_Executed"
proof -
  have restored: "restart_reservation_machine sample_balances((lineage_history 17)\<lparr>
      machine_state:=initial_reservation_state sample_balances\<rparr>)=lineage_history 17"
    by (rule complete_journal_recovers_arbitrary_cache_loss[OF lineage_history_journal])
  show ?thesis using restored same_current_continuation_distinguishes_lineage by simp
qed

definition replay_losing_once where
  "replay_losing_once balances m =
    (let restored=restart_reservation_machine balances m in
      restored\<lparr>machine_state:=(machine_state restored)\<lparr>received_messages:=empty_message_state\<rparr>\<rparr>)"

lemma replay_losing_once_on_lineage:
  "replay_losing_once sample_balances(lineage_history root)=(lineage_history root)\<lparr>
    machine_state:=(machine_state(lineage_history root))\<lparr>received_messages:=empty_message_state\<rparr>\<rparr>"
  by (simp only: replay_losing_once_def restart_reconstructs_committed_state[OF lineage_history_journal] Let_def)

lemma normal_recovery_rejects_duplicate_credit:
  "snd(sample.deliver_reserved_credit Bypass_Route example_context(sample_request 17)
    (restart_reservation_machine sample_balances(lineage_history 17)))=
      Delivery_Response(Duplicate_Credit(sample_binding 17))"
  by (subst restart_reconstructs_committed_state[OF lineage_history_journal])
     (simp add: lineage_trace_defs sample.deliver_reserved_credit_def sample.published_receive_expansion)

lemma losing_recovered_once_state_reissues_root_funding:
  defines "bad \<equiv> fst(sample.deliver_reserved_credit Bypass_Route example_context(sample_request 17)
    (replay_losing_once sample_balances(lineage_history 17)))"
  shows "funded_units(machine_state bad)((0,17),(2,17,3))=5 \<and>
    funded_units(machine_state bad)((0,17),(2,17,4))=5 \<and>
    source_effects(machine_state bad)=[sample_binding 17,sample_binding 23]"
  unfolding bad_def
  by (simp only: replay_losing_once_on_lineage)
     (simp add: lineage_trace_defs sample.deliver_reserved_credit_def sample.published_receive_expansion)

text \<open>Loss of the cache may be arbitrary; the journal and genesis input
  are complete and authentic, and completed observations are retained outside
  the cache. This does not cover a crash between an external irreversible
  effect and its journal record. Recovery reconstructs financial lineage and
  once markers together; resetting just the receiver state can reissue funding
  even while source debit history and previous onward effects are retained.\<close>

end
