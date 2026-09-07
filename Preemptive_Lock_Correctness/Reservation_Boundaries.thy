(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Boundaries
  imports Reservation_Scenarios
begin

section \<open>Identical Pending State with Different Stable Outcomes\<close>

definition opposite_statement :: source_statement where
  "opposite_statement=\<lparr>statement_binding=sample_binding 17,statement_status=Reversed\<rparr>"
definition opposite_truth where
  "opposite_truth statement \<longleftrightarrow> statement=opposite_statement"
definition opposite_signed where
  "opposite_signed signer epoch statement \<longleftrightarrow> signer=0 \<or> opposite_truth statement"
definition opposite_verifies where
  "opposite_verifies cert \<longleftrightarrow> certificate_signature cert=42 \<and>
    (\<forall>signer\<in>set(certificate_signers cert).
      opposite_signed signer(certificate_epoch cert)(certificate_statement cert))"
definition opposite_source where
  "opposite_source key=(if key=(0,17) then Some opposite_statement else None)"

interpretation opposite: source_attestation example_roster example_faulty example_bound example_threshold
  opposite_verifies opposite_signed opposite_truth opposite_source
proof unfold_locales
  fix epoch
  show "finite(example_roster epoch)" by (simp add: example_roster_def)
  show "example_faulty epoch\<subseteq>example_roster epoch" by (simp add: example_faulty_def example_roster_def)
  show "card(example_faulty epoch)\<le>example_bound epoch" by (simp add: example_faulty_def example_bound_def)
  show "example_bound epoch<example_threshold epoch" by (simp add: example_bound_def example_threshold_def)
next
  fix cert signer
  assume "opposite_verifies cert" "signer\<in>set(certificate_signers cert)"
  then show "opposite_signed signer(certificate_epoch cert)(certificate_statement cert)"
    by (simp add: opposite_verifies_def)
next
  fix signer epoch statement
  assume "signer\<in>example_roster epoch" "signer\<notin>example_faulty epoch" "opposite_signed signer epoch statement"
  then show "opposite_truth statement" by (simp add: opposite_signed_def example_faulty_def)
next
  fix statement
  assume "opposite_truth statement" "statement_status statement\<noteq>Observed"
  then show "opposite_source(binding_key(statement_binding statement))=Some statement"
    by (simp add: opposite_truth_def opposite_source_def opposite_statement_def sample_binding_def example_binding_def)
qed

definition opposite_certificate where
  "opposite_certificate=(sample_certificate 17)\<lparr>certificate_statement:=opposite_statement\<rparr>"
definition opposite_request where
  "opposite_request=(sample_request 17)\<lparr>request_certificate:=opposite_certificate\<rparr>"

lemma opposite_source_prefix_is_identical:
  "opposite.run_reservations sample_balances(sample_prefix 17)sample_initial=sample_burnt 17"
  by (simp add: sample_burnt_def sample_prefix_def sample.run_reservations.simps sample.reservation_step.simps
      opposite.run_reservations.simps opposite.reservation_step.simps)

definition expired_pending_sample where
  "expired_pending_sample=advance_reservation_time 10(sample_burnt 17)"
definition taken_pending_sample where
  "taken_pending_sample=fst(reassign_worker(sample_source_context ACTIVE)(sample_request 17)5 expired_pending_sample)"

lemmas pending_boundary_defs = expired_pending_sample_def taken_pending_sample_def sample_data_defs sample_auth_defs
  sample.protocol_definitions sample.run_reservations.simps sample.reservation_step.simps
  sample.published_receive_expansion record_observation_def commit_reservation_event_def
  record_credit_def empty_message_state_def Let_def

lemma the_same_key_binding_and_expired_pending_state:
  "advance_reservation_time 10(opposite.run_reservations sample_balances(sample_prefix 17)sample_initial)=
      expired_pending_sample \<and>
   phase_at(machine_state expired_pending_sample)(0,17)=Some Source_Pending \<and>
   reservation_clock(machine_state expired_pending_sample)=10 \<and>
   source_units(machine_state expired_pending_sample)(0,17)=5 \<and>
   credit_history(received_messages(machine_state expired_pending_sample))=[]"
  by (simp add: opposite_source_prefix_is_identical pending_boundary_defs)

lemma pending_timeout_still_allows_late_credit:
  "snd(sample.deliver_reserved_credit Bypass_Route example_context(sample_request 17)
    (sample.publish_source_certificate(sample_certificate 17)expired_pending_sample))=
      Delivery_Response(New_Credit(sample_binding 17))"
  by (simp add: pending_boundary_defs)

lemma same_pending_state_allows_evidence_based_opposite_outcome:
  "snd(opposite.release_to_source(sample_source_context ACTIVE)opposite_request 1(\<lambda>_.0)
    (opposite.publish_source_certificate opposite_certificate taken_pending_sample))=Reservation_Released"
  by (simp add: opposite.release_to_source_def opposite.publish_source_certificate_def
      opposite.reversed_source_evidence_def opposite.certificate_ok_def opposite_certificate_def opposite_request_def
      opposite_statement_def opposite_verifies_def opposite_signed_def opposite_truth_def pending_boundary_defs)

definition timeout_only_refund where
  "timeout_only_refund r m =
    (if phase_at(machine_state m)(binding_key(request_binding r))=Some Source_Pending \<and>
       (\<exists>res. reservation_at(machine_state m)(binding_key(request_binding r))=Some res \<and>
         reservation_deadline res\<le>reservation_clock(machine_state m))
     then commit_reservation_event(Return_Event(request_binding r))m else m)"

lemma timeout_only_refund_and_late_credit_duplicate_money:
  defines "bad \<equiv> fst(sample.deliver_reserved_credit Bypass_Route example_context(sample_request 17)
    (sample.publish_source_certificate(sample_certificate 17)
      (timeout_only_refund(sample_request 17)expired_pending_sample)))"
  shows "source_units(machine_state bad)(0,17)=10 \<and>
    destination_units(machine_state bad)(2,17,3)=5 \<and>
    credit_history(received_messages(machine_state bad))=[sample_binding 17]"
  unfolding bad_def by (simp add: timeout_only_refund_def pending_boundary_defs)

theorem no_timeout_only_classifier_can_recover_both_outcome_consumers:
  "\<not>(\<exists>classify :: reservation_machine \<Rightarrow> bool.
    classify expired_pending_sample=(snd(sample.deliver_reserved_credit Bypass_Route example_context
      (sample_request 17)(sample.publish_source_certificate(sample_certificate 17)expired_pending_sample))=
        Delivery_Response(New_Credit(sample_binding 17))) \<and>
    classify expired_pending_sample=(snd(opposite.deliver_reserved_credit Bypass_Route example_context
      opposite_request(opposite.publish_source_certificate opposite_certificate expired_pending_sample))=
        Delivery_Response(New_Credit(sample_binding 17))))"
  by (simp add: pending_timeout_still_allows_late_credit opposite.deliver_reserved_credit_def
      opposite.published_receive_expansion opposite.credit_admissible_def opposite.authenticated_request_def
      opposite_certificate_def opposite_request_def opposite_statement_def record_observation_def)

text \<open>Both source-attestation instances satisfy the parent's assumptions
  and produce the exact same acquisition, debit and expired local state for
  the same immutable key and binding. Their stable outcomes differ across
  instances, not over time inside one instance. A function of that local state
  alone cannot recover both outcome-sensitive consumer decisions. Actual
  evidence distinguishes them, and the reversed instance has a successful
  authorized release. The timeout refund is an explicitly unsafe replacement
  policy; the published protocol never performs it.\<close>

end
