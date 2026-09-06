(* SPDX-License-Identifier: BSD-3-Clause *)
theory Message_Boundaries
  imports Message_Mutations
begin

section \<open>The Destination Boundary in the Actual Mutated Admission\<close>

definition weak_destination_gate :: "execution_context \<Rightarrow> execution_request \<Rightarrow> bool"
  where
  "weak_destination_gate c r \<longleftrightarrow> example.weakened_binding_auth Destination_Field c r
    \<and>
     binding_operation (request_binding r) = Destination_Credit \<and> 0 < binding_amount (request_binding
       r)"

lemma weak_destination_pair_is_admitted:
  "weak_destination_gate example_context (example_request 17) \<and>
   weak_destination_gate (changed_context Destination_Field) (changed_request Destination_Field)"
  unfolding weak_destination_gate_def example.weakened_binding_auth_def example.certificate_ok_def
    current_use_allowed_def
  by (simp add: example_context_def example_request_def example_certificate_def example_statement_def
      example_binding_def example_roster_def example_threshold_def example_verifies_def example_signed_def
      example_truth_def changed_context_def changed_request_def)

lemma actual_destination_mutation_breaks_kernel_once:
  "count_list (map binding_key (credit_history
    (run_once weak_destination_gate
      [(Validated_Route,example_context,example_request 17),
       (Bypass_Route,changed_context Destination_Field,changed_request Destination_Field)]
      empty_message_state))) (0,17) = 2"
proof -
  have a: "weak_destination_gate example_context (example_request 17)"
    and b: "weak_destination_gate (changed_context Destination_Field) (changed_request Destination_Field)"
    using weak_destination_pair_is_admitted by auto
  have key: "binding_key (request_binding (example_request 17)) =
    binding_key (request_binding (changed_request Destination_Field))"
    by (simp add: example_request_def changed_request_def example_binding_def)
  have different: "binding_destination (request_binding (example_request 17)) \<noteq>
    binding_destination (request_binding (changed_request Destination_Field))"
    by (simp add: example_request_def changed_request_def example_binding_def)
  show ?thesis using two_destinations_generate_two_credits[OF a b key different]
    by (simp add: example_request_def example_binding_def)
qed

section \<open>Different Valid Certificates Share One Checked Summary\<close>

definition alternative_envelope :: normal_envelope where
  "alternative_envelope = (example_envelope 101 17)
    \<lparr>envelope_request := (example_request 17)\<lparr>request_certificate :=
      (example_certificate 17)\<lparr>certificate_signers := [2,3]\<rparr>\<rparr>\<rparr>"

lemma different_certificates_same_checked_summary:
  "request_certificate (envelope_request (example_envelope 100 17)) \<noteq>
     request_certificate (envelope_request alternative_envelope) \<and>
   example.checked_summary (example_envelope 100 17) = example.checked_summary alternative_envelope \<and>
   example.checked_summary alternative_envelope \<noteq> None"
  unfolding example.checked_summary_def example.intrinsic_credit_ok_def example.certificate_ok_def
  by (simp add: alternative_envelope_def example_envelope_def example_request_def example_certificate_def
      example_statement_def example_binding_def example_roster_def example_threshold_def
        example_verifies_def
      example_signed_def example_truth_def request_descriptor_def)

lemma different_certificates_same_receiver_observations:
  "\<forall>c s. example.receive_normal c (example_envelope 100 17) s =
    example.receive_normal c alternative_envelope s"
  using example.checked_summary_is_exact_information different_certificates_same_checked_summary by blast

definition discard_claimed_epoch :: "checked_descriptor option \<Rightarrow>
    (transfer_binding \<times> nat \<times> nat \<times> nat) option" where
  "discard_claimed_epoch summary = map_option (\<lambda>(b,relay,caller,epoch,version).
    (b,relay,caller,version)) summary"

lemma discarding_summary_epoch_loses_a_decision:
  "discard_claimed_epoch (example.checked_summary (example_envelope 100 17)) =
     discard_claimed_epoch (example.checked_summary (refresh_envelope 7 4 (example_envelope 100 17))) \<and>
   example.checked_summary (example_envelope 100 17) \<noteq>
     example.checked_summary (refresh_envelope 7 4 (example_envelope 100 17))"
  unfolding example.checked_summary_def example.intrinsic_credit_ok_def example.certificate_ok_def
  by (simp add: discard_claimed_epoch_def refresh_envelope_def example_envelope_def
      example_request_def example_certificate_def example_statement_def example_binding_def
      example_roster_def example_threshold_def example_verifies_def example_signed_def
      example_truth_def request_descriptor_def)

section \<open>State Preservation Does Not Supply Missing Authorization\<close>

context source_attestation
begin

definition authentication_without_current_epoch :: "execution_context \<Rightarrow> execution_request
  \<Rightarrow> bool" where
  "authentication_without_current_epoch c r \<longleftrightarrow>
     certificate_ok (request_certificate r) \<and>
     certificate_epoch (request_certificate r) = context_relay_epoch c \<and>
     statement_binding (certificate_statement (request_certificate r)) = request_binding r \<and>
     statement_status (certificate_statement (request_certificate r)) = Finalized \<and>
     binding_destination (request_binding r) = context_endpoint c \<and>
     request_version r = context_version c \<and>
     (request_caller r,request_binding r) \<in> context_permissions c"

definition regulatory_apply_without_current_epoch :: "execution_context \<Rightarrow> execution_request
  \<Rightarrow>
    regulatory_receiver \<Rightarrow> regulatory_receiver option" where
  "regulatory_apply_without_current_epoch c r s =
    (if \<not> authentication_without_current_epoch c r \<or> binding_key (request_binding r) \<in>
      receiver_applied s
     then None
     else case binding_operation (request_binding r) of
       Regulatory_State_Effect action \<Rightarrow>
         (case sync (fst (binding_key (request_binding r))) action
           (binding_asset (request_binding r)) (receiver_snapshot s) of
           None \<Rightarrow> None
         | Some snapshot \<Rightarrow> Some (s\<lparr>receiver_snapshot := snapshot,
             receiver_applied := insert (binding_key (request_binding r)) (receiver_applied s)\<rparr>))
     | _ \<Rightarrow> None)"

end

lemma stale_freeze_is_rejected:
  "example.apply_regulatory_message example_context
    ((example_request 20)\<lparr>request_authority_epoch := 7\<rparr>)
    \<lparr>receiver_snapshot = example_snapshot ACTIVE, receiver_applied = {}\<rparr> = None"
  by (simp add: example.apply_regulatory_message_def example.authenticated_request_def
      current_use_allowed_def example_context_def)

lemma removed_epoch_check_executes_stale_freeze:
  "example.regulatory_apply_without_current_epoch example_context
    ((example_request 20)\<lparr>request_authority_epoch := 7\<rparr>)
    \<lparr>receiver_snapshot = example_snapshot ACTIVE, receiver_applied = {}\<rparr> =
      Some \<lparr>receiver_snapshot = example_snapshot FROZEN, receiver_applied = {(0,20)}\<rparr>"
  unfolding example.regulatory_apply_without_current_epoch_def
    example.authentication_without_current_epoch_def
    example.certificate_ok_def
  by (simp add: example_request_def example_certificate_def example_statement_def example_binding_def
      example_context_def example_roster_def example_threshold_def example_verifies_def example_signed_def
      example_truth_def sync_def example_snapshot_def get_reg_state_def get_asset_state_def
      acquire_lock_def is_locked_def connected_chains_def asset_exists_def update_all_chains_def
      release_lock_def Let_def fun_eq_iff)

lemma stale_freeze_can_still_preserve_cdsp_validity:
  "valid_state (example_snapshot FROZEN) \<and>
   \<not> current_use_allowed example_context ((example_request 20)\<lparr>request_authority_epoch :=
     7\<rparr>)"
  by (simp add: example_snapshot_valid current_use_allowed_def example_context_def)

section \<open>Historical Records Cannot Determine Current Permission\<close>

definition revoked_context :: execution_context where
  "revoked_context = example_context\<lparr>context_permissions := {}\<rparr>"

lemma revoked_permission_rejects_same_certificate:
  "example.receive_credit Validated_Route revoked_context (example_request 17) empty_message_state =
    (empty_message_state,Message_Rejected)"
  by (simp add: example.receive_credit_def example.credit_admissible_def example.authenticated_request_def
      current_use_allowed_def revoked_context_def)

theorem history_only_current_permission_decoder_impossible:
  "\<not> (\<exists>decoder. \<forall>c. decoder ([] :: transfer_binding list) (example_request 17) =
    snd (example.receive_credit Validated_Route c (example_request 17) empty_message_state))"
proof
  assume "\<exists>decoder. \<forall>c. decoder ([] :: transfer_binding list) (example_request 17) =
    snd (example.receive_credit Validated_Route c (example_request 17) empty_message_state)"
  then obtain decoder where all_contexts: "\<forall>c. decoder ([] :: transfer_binding list)
    (example_request 17) =
    snd (example.receive_credit Validated_Route c (example_request 17) empty_message_state)" by blast
  have allowed: "decoder [] (example_request 17) = New_Credit (example_binding 17)"
    using all_contexts[rule_format, of example_context] example_new_credit by simp
  have rejected: "decoder [] (example_request 17) = Message_Rejected"
    using all_contexts[rule_format, of revoked_context] revoked_permission_rejects_same_certificate by simp
  show False using allowed rejected by simp
qed

section \<open>Independent Admission Branches\<close>

lemma invalid_signature_is_rejected_without_state_change:
  "example.receive_credit Validated_Route example_context
    ((example_request 17)\<lparr>request_certificate :=
      (example_certificate 17)\<lparr>certificate_signature := 0\<rparr>\<rparr>) empty_message_state =
    (empty_message_state,Message_Rejected)"
  by (simp add: example.receive_credit_def example.credit_admissible_def
      example.authenticated_request_def example.certificate_ok_def example_verifies_def)

lemma empty_signer_input_is_rejected:
  "\<not> example.certificate_ok ((example_certificate 17)\<lparr>certificate_signers := []\<rparr>)"
  by (simp add: example.certificate_ok_def example_certificate_def example_threshold_def)

lemma unregistered_signer_is_not_a_trusted_vote:
  "example_verifies ((example_certificate 17)\<lparr>certificate_signers := [1,99]\<rparr>) \<and>
   \<not> example.certificate_ok ((example_certificate 17)\<lparr>certificate_signers := [1,99]\<rparr>)"
  by (simp add: example.certificate_ok_def example_certificate_def example_roster_def
      example_verifies_def example_signed_def example_truth_def)

lemma stale_relay_configuration_rejects:
  "example.receive_credit Bypass_Route (example_context\<lparr>context_relay_epoch := 9\<rparr>)
    (example_request 17) empty_message_state = (empty_message_state,Message_Rejected)"
  by (simp add: example.receive_credit_def example.credit_admissible_def example.authenticated_request_def
      example_context_def example_request_def example_certificate_def)

lemma stale_current_version_rejects:
  "example.receive_credit Bypass_Route (example_context\<lparr>context_version := 5\<rparr>)
    (example_request 17) empty_message_state = (empty_message_state,Message_Rejected)"
  by (simp add: example.receive_credit_def example.credit_admissible_def example.authenticated_request_def
      current_use_allowed_def example_context_def example_request_def)

lemma envelope_identity_cannot_reset_source_consumption:
  "example.normal_trace [(example_context,example_envelope 100 17),
     (example_context,example_envelope 101 17)] empty_message_state =
    (record_credit (example_binding 17) empty_message_state,
     [New_Credit (example_binding 17),Duplicate_Credit (example_binding 17)])"
  using example_request_authenticated
  by (simp add: example.receive_normal_def example_envelope_def example.receive_credit_def
      example.credit_admissible_def example_request_def example_binding_def
      record_credit_def empty_message_state_def Let_def)

end
