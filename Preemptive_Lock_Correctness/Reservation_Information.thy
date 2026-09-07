(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Information
  imports Reservation_Lineage
begin

section \<open>Publication-Sensitive Internal Information\<close>

context source_attestation
begin

definition publication_checked_summary :: "source_certificate list \<Rightarrow> normal_envelope \<Rightarrow>
  checked_descriptor option" where
  "publication_checked_summary published envelope =
    (if request_certificate(envelope_request envelope)\<in>set published
     then checked_summary envelope else None)"

theorem publication_summary_preserves_actual_receiver:
  "summary_receive c (publication_checked_summary(issued_certificates s)
      \<lparr>envelope_id=uuid,envelope_request=r\<rparr>)(received_messages s)=
    published_receive route c r s"
  by (auto simp: publication_checked_summary_def checked_summary_def summary_receive_def
      request_descriptor_def published_receive_expansion credit_admission_splits split: if_splits)

definition receive_with_publications :: "source_certificate list \<Rightarrow> execution_context \<Rightarrow>
  normal_envelope \<Rightarrow> message_state \<Rightarrow> message_state \<times> message_reply" where
  "receive_with_publications published c envelope messages =
    published_receive Validated_Route c(envelope_request envelope)
      ((initial_reservation_state(\<lambda>_.0))\<lparr>issued_certificates:=published,received_messages:=messages\<rparr>)"

lemma fixed_publication_summary_factorization:
  "receive_with_publications published c envelope messages=
    summary_receive c(publication_checked_summary published envelope)messages"
  using publication_summary_preserves_actual_receiver[of c
    "(initial_reservation_state(\<lambda>_.0))\<lparr>issued_certificates:=published,received_messages:=messages\<rparr>"
    "envelope_id envelope" "envelope_request envelope" Validated_Route]
  by (cases envelope) (simp add: receive_with_publications_def)

theorem publication_sensitive_summary_is_exact_for_fixed_publications:
  "publication_checked_summary published first=publication_checked_summary published second \<longleftrightarrow>
    (\<forall>c messages. receive_with_publications published c first messages=
      receive_with_publications published c second messages)"
proof
  assume same: "publication_checked_summary published first=publication_checked_summary published second"
  show "\<forall>c messages. receive_with_publications published c first messages=
      receive_with_publications published c second messages"
    by (simp add: fixed_publication_summary_factorization same)
next
  assume same: "\<forall>c messages. receive_with_publications published c first messages=
      receive_with_publications published c second messages"
  show "publication_checked_summary published first=publication_checked_summary published second"
    by (rule summary_observations_are_injective)
       (use same in \<open>simp add: fixed_publication_summary_factorization\<close>)
qed

theorem journal_recovery_preserves_publication_summary:
  assumes "journal_agreement balances m"
  shows "publication_checked_summary(issued_certificates(machine_state(restart_reservation_machine balances m))) envelope=
    publication_checked_summary(issued_certificates(machine_state m)) envelope"
  using restart_reconstructs_committed_state[OF assms] by simp

end

definition alternate_certificate where
  "alternate_certificate=(sample_certificate 17)\<lparr>certificate_signers:=[2,3]\<rparr>"
definition alternate_request where
  "alternate_request=(sample_request 17)\<lparr>request_certificate:=alternate_certificate\<rparr>"

lemma original_summary_loses_publication_information:
  "sample.certificate_ok(sample_certificate 17) \<and> sample.certificate_ok alternate_certificate \<and>
    sample.checked_summary\<lparr>envelope_id=1,envelope_request=sample_request 17\<rparr>=
      sample.checked_summary\<lparr>envelope_id=2,envelope_request=alternate_request\<rparr> \<and>
    sample.publication_checked_summary[sample_certificate 17]
      \<lparr>envelope_id=1,envelope_request=sample_request 17\<rparr>\<noteq>
    sample.publication_checked_summary[sample_certificate 17]
      \<lparr>envelope_id=2,envelope_request=alternate_request\<rparr>"
  by (simp add: alternate_certificate_def alternate_request_def sample.publication_checked_summary_def
      sample.checked_summary_def sample.intrinsic_credit_ok_def request_descriptor_def sample_data_defs sample_auth_defs)

text \<open>The additional membership check is evaluated against the current
  publication state, and the original intrinsic certificate checks still run.
  This internal summary is exact only for this message consumer and a fixed
  publication set, over the modeled contexts and message states. The old
  summary's unconditional lift fails. These are standard factorization
  arguments applied to the actual additional consumer, not a claim of a new
  general information theorem or a complete representation of reservation
  continuation, source terminal decisions, or runtime storage.\<close>

end
