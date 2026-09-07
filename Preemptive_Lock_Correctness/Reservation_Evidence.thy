(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Evidence
  imports Reservation_Message_Link Reservation_Ownership
begin

section \<open>Executable Reversal Evidence and Conflicting Credit\<close>

context source_attestation
begin

lemma reversed_evidence_is_stable:
  assumes "reversed_source_evidence c r s"
  shows "stable_source(binding_key(request_binding r)) =
    Some \<lparr>statement_binding=request_binding r,statement_status=Reversed\<rparr>"
proof -
  have ok: "certificate_ok(request_certificate r)"
    and bound: "statement_binding(certificate_statement(request_certificate r))=request_binding r"
    and status: "statement_status(certificate_statement(request_certificate r))=Reversed"
    using assms unfolding reversed_source_evidence_def by auto
  have whole: "certificate_statement(request_certificate r)=
    \<lparr>statement_binding=request_binding r,statement_status=Reversed\<rparr>"
    using bound status by (cases "certificate_statement(request_certificate r)") auto
  show ?thesis using certificate_authenticates_stable_fact[OF ok] status whole by simp
qed

theorem reversed_evidence_excludes_any_conflicting_credit:
  assumes reversed: "reversed_source_evidence c r s"
    and key: "binding_key(request_binding other)=binding_key(request_binding r)"
  shows "\<not>credit_admissible current other"
proof
  assume "credit_admissible current other"
  then have "stable_source(binding_key(request_binding other))=
    Some \<lparr>statement_binding=request_binding other,statement_status=Finalized\<rparr>"
    using request_has_stable_binding unfolding credit_admissible_def by blast
  then show False using reversed_evidence_is_stable[OF reversed] key
    by (metis option.inject source_statement.select_convs(2) source_status.distinct(5))
qed

theorem reversed_evidence_excludes_existing_credit:
  assumes reversed: "reversed_source_evidence c r s"
    and inv: "message_invariant(received_messages s)"
  shows "binding_key(request_binding r)\<notin>set(map binding_key(credit_history(received_messages s)))"
proof
  assume "binding_key(request_binding r)\<in>set(map binding_key(credit_history(received_messages s)))"
  then obtain b where b: "b\<in>set(credit_history(received_messages s))"
    "binding_key b=binding_key(request_binding r)" by auto
  have "stable_source(binding_key b)=Some \<lparr>statement_binding=b,statement_status=Finalized\<rparr>"
    using inv b unfolding message_invariant_def by blast
  then show False using reversed_evidence_is_stable[OF reversed] b(2)
    by (metis option.inject source_statement.select_convs(2) source_status.distinct(5))
qed

theorem evidence_release_exact_guard:
  "snd(release_to_source c r g versions m)=Reservation_Released \<longleftrightarrow>
   owns_recorded_reservation c r g versions(machine_state m) \<and>
   phase_at(machine_state m)(binding_key(request_binding r))=Some Source_Pending \<and>
   reversed_source_evidence(lock_authority c)r(machine_state m)"
  by (simp add: release_to_source_def record_observation_def)

theorem evidence_release_preserves_destination_and_completed_data:
  "destination_units(machine_state(fst(release_to_source c r g versions m)))=
       destination_units(machine_state m) \<and>
   funded_units(machine_state(fst(release_to_source c r g versions m)))=funded_units(machine_state m) \<and>
   received_messages(machine_state(fst(release_to_source c r g versions m)))=received_messages(machine_state m) \<and>
   lawful_descendants(machine_state(fst(release_to_source c r g versions m)))=lawful_descendants(machine_state m) \<and>
   asset_value(machine_state(fst(release_to_source c r g versions m)))=asset_value(machine_state m) \<and>
   asset_version(machine_state(fst(release_to_source c r g versions m)))=asset_version(machine_state m)"
  by (simp add: release_to_source_def record_observation_def commit_reservation_event_def
      finish_reservation_def set_phase_def)

theorem successful_release_restores_exact_amount_and_closes:
  assumes "snd(release_to_source c r g versions m)=Reservation_Released"
  shows "source_units(machine_state(fst(release_to_source c r g versions m)))
        (source_account_of(request_binding r)) =
      source_units(machine_state m)(source_account_of(request_binding r))+binding_amount(request_binding r) \<and>
    phase_at(machine_state(fst(release_to_source c r g versions m)))(binding_key(request_binding r))=
      Some Source_Returned \<and>
    (\<forall>a. asset_owner(machine_state m)a=Some(binding_key(request_binding r)) \<longrightarrow>
      asset_owner(machine_state(fst(release_to_source c r g versions m)))a=None)"
proof -
  have guards: "owns_recorded_reservation c r g versions(machine_state m)"
    "phase_at(machine_state m)(binding_key(request_binding r))=Some Source_Pending"
    "reversed_source_evidence(lock_authority c)r(machine_state m)"
    using assms evidence_release_exact_guard by blast+
  show ?thesis using guards
    by (auto simp: release_to_source_def record_observation_def commit_reservation_event_def
        phase_at_def finish_reservation_def set_phase_def split: option.splits)
qed

theorem released_source_has_no_current_or_future_credit:
  assumes release: "snd(release_to_source c r g versions m)=Reservation_Released"
    and key: "binding_key(request_binding other)=binding_key(request_binding r)"
  shows "snd(published_receive route current other future)=Message_Rejected"
proof -
  have reversed: "reversed_source_evidence(lock_authority c)r(machine_state m)"
    using release evidence_release_exact_guard by blast
  have "\<not>credit_admissible current other"
    by (rule reversed_evidence_excludes_any_conflicting_credit[OF reversed key])
  then show ?thesis by (simp add: published_receive_expansion)
qed

theorem released_source_never_appears_in_reachable_destination:
  assumes release: "snd(release_to_source c r g versions m)=Reservation_Released"
  shows "binding_key(request_binding r)\<notin>set(map binding_key(credit_history(received_messages
    (machine_state(run_reservations balances actions(initial_reservation_machine balances))))))"
proof -
  have reversed: "reversed_source_evidence(lock_authority c)r(machine_state m)"
    using release evidence_release_exact_guard by blast
  have stable: "stable_source(binding_key(request_binding r))=
    Some \<lparr>statement_binding=request_binding r,statement_status=Reversed\<rparr>"
    by (rule reversed_evidence_is_stable[OF reversed])
  have inv: "message_invariant(received_messages(machine_state
    (run_reservations balances actions(initial_reservation_machine balances))))"
    using generated_message_source_invariant[of balances actions]
    unfolding message_source_invariant_def by blast
  show ?thesis using stable inv
    by (auto simp: message_invariant_def; metis option.inject source_statement.select_convs(2) source_status.distinct(5))
qed

text \<open>The future exclusion quantifies over all later contexts, envelopes
  and states of the same source-attestation instance. Its load-bearing premise
  is the parent's stable source fact: a later change from Finalized to Reversed
  for one immutable key is outside that instance. This is a source-outcome
  profile, not an independently established distributed terminal decision.\<close>

end

end
