(* SPDX-License-Identifier: BSD-3-Clause *)
theory Message_Examples
  imports Message_Summary
begin

section \<open>A Concrete Source and Verifier Model\<close>

definition example_binding :: "nat \<Rightarrow> transfer_binding" where
  "example_binding event =
    \<lparr>binding_key = (0,event), binding_asset = event, binding_amount = 5,
      binding_destination = 2, binding_recipient = 3, binding_source_epoch = 7,
      binding_operation = (if event = 18 then Ordinary_Transfer_Effect
        else if event = 19 then Enforcement_Transfer_Effect Legal_Recover
        else if event = 20 then Regulatory_State_Effect FREEZE
        else if event = 21 then Regulatory_State_Effect UNFREEZE else Destination_Credit),
      binding_separator = 11\<rparr>"

definition example_statement :: "nat \<Rightarrow> source_statement" where
  "example_statement event =
    \<lparr>statement_binding = example_binding event,
      statement_status = (if event = 22 then Reversed else Finalized)\<rparr>"

definition example_observation :: source_statement where
  "example_observation = (example_statement 17)\<lparr>statement_status := Observed\<rparr>"

definition example_truth :: "source_statement \<Rightarrow> bool" where
  "example_truth statement \<longleftrightarrow>
    statement \<in> {example_statement 17, example_statement 18, example_statement 19,
      example_statement 20, example_statement 21, example_statement 22, example_observation}"

definition example_source :: "source_key \<Rightarrow> source_statement option" where
  "example_source key = (if key = (0,17) then Some (example_statement 17)
    else if key = (0,18) then Some (example_statement 18)
    else if key = (0,19) then Some (example_statement 19)
    else if key = (0,20) then Some (example_statement 20)
    else if key = (0,21) then Some (example_statement 21)
    else if key = (0,22) then Some (example_statement 22) else None)"

definition example_roster :: "nat \<Rightarrow> nat set" where
  "example_roster epoch = {0,1,2,3}"

definition example_faulty :: "nat \<Rightarrow> nat set" where
  "example_faulty epoch = {0}"

definition example_bound :: "nat \<Rightarrow> nat" where
  "example_bound epoch = 1"

definition example_threshold :: "nat \<Rightarrow> nat" where
  "example_threshold epoch = 2"

definition example_signed :: "nat \<Rightarrow> nat \<Rightarrow> source_statement \<Rightarrow> bool" where
  "example_signed signer epoch statement \<longleftrightarrow> signer = 0 \<or> example_truth statement"

definition example_verifies :: "source_certificate \<Rightarrow> bool" where
  "example_verifies cert \<longleftrightarrow> certificate_signature cert = 42 \<and>
    (\<forall>signer \<in> set (certificate_signers cert).
      example_signed signer (certificate_epoch cert) (certificate_statement cert))"

lemma example_stable_truth:
  assumes "example_truth statement" "statement_status statement \<noteq> Observed"
  shows "example_source (binding_key (statement_binding statement)) = Some statement"
  using assms
  by (auto simp: example_truth_def example_source_def example_statement_def
      example_binding_def example_observation_def)

interpretation example: source_attestation
  example_roster example_faulty example_bound example_threshold
  example_verifies example_signed example_truth example_source
proof unfold_locales
  fix epoch
  show "finite (example_roster epoch)" by (simp add: example_roster_def)
  show "example_faulty epoch \<subseteq> example_roster epoch"
    by (simp add: example_faulty_def example_roster_def)
  show "card (example_faulty epoch) \<le> example_bound epoch"
    by (simp add: example_faulty_def example_bound_def)
  show "example_bound epoch < example_threshold epoch"
    by (simp add: example_bound_def example_threshold_def)
next
  fix cert signer
  assume "example_verifies cert" "signer \<in> set (certificate_signers cert)"
  then show "example_signed signer (certificate_epoch cert) (certificate_statement cert)"
    by (simp add: example_verifies_def)
next
  fix signer epoch statement
  assume "signer \<in> example_roster epoch" "signer \<notin> example_faulty epoch"
    "example_signed signer epoch statement"
  then show "example_truth statement" by (simp add: example_faulty_def example_signed_def)
next
  fix statement
  assume "example_truth statement" "statement_status statement \<noteq> Observed"
  then show "example_source (binding_key (statement_binding statement)) = Some statement"
    by (rule example_stable_truth)
qed

definition example_certificate :: "nat \<Rightarrow> source_certificate" where
  "example_certificate event =
    \<lparr>certificate_statement = example_statement event, certificate_epoch = 8,
      certificate_signers = [1,2], certificate_signature = 42\<rparr>"

definition example_context :: execution_context where
  "example_context =
    \<lparr>context_endpoint = 2, context_relay_epoch = 8, context_authority_epoch = 9,
      context_version = 4, context_permissions = {p. fst p = 7}, context_readers = {7,8}\<rparr>"

definition example_request :: "nat \<Rightarrow> execution_request" where
  "example_request event =
    \<lparr>request_binding = example_binding event, request_certificate = example_certificate event,
      request_caller = 7, request_authority_epoch = 9, request_version = 4\<rparr>"

definition example_envelope :: "nat \<Rightarrow> nat \<Rightarrow> normal_envelope" where
  "example_envelope uuid event = \<lparr>envelope_id = uuid, envelope_request = example_request
    event\<rparr>"

lemma example_certificate_accepted:
  "example.certificate_ok (example_certificate 17)"
  by (simp add: example.certificate_ok_def example_certificate_def example_roster_def
      example_threshold_def example_verifies_def example_signed_def example_truth_def)

lemma example_request_authenticated:
  "example.authenticated_request example_context (example_request 17)"
  using example_certificate_accepted
  by (simp add: example.authenticated_request_def example_request_def example_certificate_def
      example_statement_def example_binding_def example_context_def current_use_allowed_def)

lemma example_new_credit:
  "example.receive_credit Validated_Route example_context (example_request 17) empty_message_state =
    (record_credit (example_binding 17) empty_message_state, New_Credit (example_binding 17))"
  using example_request_authenticated
  by (simp add: example.receive_credit_def example.credit_admissible_def example_request_def
      example_binding_def empty_message_state_def)

lemma example_replay_is_duplicate:
  "example.receive_credit Bypass_Route example_context (example_request 17)
     (record_credit (example_binding 17) empty_message_state) =
    (record_credit (example_binding 17) empty_message_state, Duplicate_Credit (example_binding 17))"
  using example_request_authenticated
  by (simp add: example.receive_credit_def example.credit_admissible_def example_request_def
      example_binding_def record_credit_def empty_message_state_def)

lemma example_current_authority_rejects:
  "example.receive_credit Bypass_Route example_context
    ((example_request 17)\<lparr>request_authority_epoch := 7\<rparr>) empty_message_state =
      (empty_message_state, Message_Rejected)"
  by (simp add: example.receive_credit_def example.credit_admissible_def example.authenticated_request_def
      current_use_allowed_def example_context_def)

lemma example_missing_binding_rejects:
  "example.receive_credit Validated_Route example_context
    ((example_request 17)\<lparr>request_binding := (example_binding 17)\<lparr>binding_recipient :=
      4\<rparr>\<rparr>)
     empty_message_state = (empty_message_state, Message_Rejected)"
  by (simp add: example.receive_credit_def example.credit_admissible_def example.authenticated_request_def
      example_request_def example_certificate_def example_statement_def example_binding_def)

lemma example_duplicate_signers_rejected:
  "\<not> example.certificate_ok ((example_certificate 17)\<lparr>certificate_signers := [1,1,2]\<rparr>)"
  by (simp add: example.certificate_ok_def)

lemma example_provisional_is_not_final:
  "example.certificate_ok ((example_certificate 17)\<lparr>certificate_statement :=
    example_observation\<rparr>) \<and>
   \<not> example.authenticated_request example_context
      ((example_request 17)\<lparr>request_certificate :=
        (example_certificate 17)\<lparr>certificate_statement := example_observation\<rparr>\<rparr>)"
  by (simp add: example.certificate_ok_def example.authenticated_request_def
      example_certificate_def example_roster_def example_threshold_def example_verifies_def
      example_signed_def example_truth_def example_observation_def)

lemma example_reversal_is_not_destination_finality:
  "example.certificate_ok (example_certificate 22) \<and>
   \<not> example.authenticated_request example_context (example_request 22)"
  by (simp add: example.certificate_ok_def example.authenticated_request_def
      example_certificate_def example_request_def example_statement_def example_roster_def
      example_threshold_def example_verifies_def example_signed_def example_truth_def)

lemmas example_all_traces_at_most_once = example.family_wide_at_most_once
lemmas example_all_traces_authenticated = example.every_executed_credit_has_authenticated_source

text \<open>The finite source and signature table is a concrete model of the
  stated assumptions. It is not an implementation of a cryptographic scheme
  or a finality protocol. Its nonempty positive and rejection branches are
  checked by the logic kernel.\<close>

end
