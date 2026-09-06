(* SPDX-License-Identifier: BSD-3-Clause *)
theory Message_Mutations
  imports Message_Consumers
begin

section \<open>Authenticated Binding Removal Witnesses\<close>

datatype binding_field = Key_Field | Asset_Field | Amount_Field | Destination_Field
  | Recipient_Field | Source_Epoch_Field | Operation_Field | Separator_Field

fun erase_field :: "binding_field \<Rightarrow> transfer_binding \<Rightarrow> transfer_binding" where
  "erase_field Key_Field b = b\<lparr>binding_key := (0,0)\<rparr>"
| "erase_field Asset_Field b = b\<lparr>binding_asset := 0\<rparr>"
| "erase_field Amount_Field b = b\<lparr>binding_amount := 0\<rparr>"
| "erase_field Destination_Field b = b\<lparr>binding_destination := 0\<rparr>"
| "erase_field Recipient_Field b = b\<lparr>binding_recipient := 0\<rparr>"
| "erase_field Source_Epoch_Field b = b\<lparr>binding_source_epoch := 0\<rparr>"
| "erase_field Operation_Field b = b\<lparr>binding_operation := Destination_Credit\<rparr>"
| "erase_field Separator_Field b = b\<lparr>binding_separator := 0\<rparr>"

context source_attestation
begin

definition weakened_binding_auth :: "binding_field \<Rightarrow> execution_context \<Rightarrow>
  execution_request \<Rightarrow> bool" where
  "weakened_binding_auth field c r \<longleftrightarrow>
     certificate_ok (request_certificate r) \<and>
     certificate_epoch (request_certificate r) = context_relay_epoch c \<and>
     erase_field field (statement_binding (certificate_statement (request_certificate r))) =
       erase_field field (request_binding r) \<and>
     statement_status (certificate_statement (request_certificate r)) = Finalized \<and>
     binding_destination (request_binding r) = context_endpoint c \<and>
     current_use_allowed c r"

definition weakened_binding_receive :: "binding_field \<Rightarrow> execution_context \<Rightarrow>
  execution_request \<Rightarrow> message_state \<Rightarrow> message_state \<times> message_reply" where
  "weakened_binding_receive field c r s =
    (if weakened_binding_auth field c r \<and>
       binding_operation (request_binding r) = Destination_Credit \<and>
       0 < binding_amount (request_binding r)
     then if credit_marker (request_binding r) \<in> consumed_at s
       then (s, Duplicate_Credit (request_binding r))
       else (record_credit (request_binding r) s, New_Credit (request_binding r))
     else (s, Message_Rejected))"

definition receive_without_once :: "execution_context \<Rightarrow> execution_request \<Rightarrow>
  message_state \<Rightarrow> message_state \<times> message_reply" where
  "receive_without_once c r s =
    (if credit_admissible c r
     then (record_credit (request_binding r) s, New_Credit (request_binding r))
     else (s, Message_Rejected))"

end

fun changed_binding :: "binding_field \<Rightarrow> transfer_binding" where
  "changed_binding Key_Field = (example_binding 17)\<lparr>binding_key := (1,17)\<rparr>"
| "changed_binding Asset_Field = (example_binding 17)\<lparr>binding_asset := 18\<rparr>"
| "changed_binding Amount_Field = (example_binding 17)\<lparr>binding_amount := 6\<rparr>"
| "changed_binding Destination_Field = (example_binding 17)\<lparr>binding_destination := 3\<rparr>"
| "changed_binding Recipient_Field = (example_binding 17)\<lparr>binding_recipient := 4\<rparr>"
| "changed_binding Source_Epoch_Field = (example_binding 17)\<lparr>binding_source_epoch := 8\<rparr>"
| "changed_binding Operation_Field = (example_binding 18)\<lparr>binding_operation :=
  Destination_Credit\<rparr>"
| "changed_binding Separator_Field = (example_binding 17)\<lparr>binding_separator := 12\<rparr>"

definition changed_request :: "binding_field \<Rightarrow> execution_request" where
  "changed_request field =
    (example_request (if field = Operation_Field then 18 else 17))
      \<lparr>request_binding := changed_binding field\<rparr>"

definition changed_context :: "binding_field \<Rightarrow> execution_context" where
  "changed_context field = example_context
    \<lparr>context_endpoint := binding_destination (changed_binding field)\<rparr>"

lemma all_binding_changes_rejected:
  "example.receive_credit Validated_Route (changed_context field) (changed_request field)
     empty_message_state = (empty_message_state, Message_Rejected)"
  unfolding example.receive_credit_def example.credit_admissible_def example.authenticated_request_def
  by (cases field)
     (simp_all add: changed_context_def changed_request_def example_request_def example_certificate_def
       example_statement_def example_binding_def)

lemma all_binding_removals_execute:
  "example.weakened_binding_receive field (changed_context field) (changed_request field)
    empty_message_state =
    (record_credit (changed_binding field) empty_message_state, New_Credit (changed_binding field))"
  unfolding example.weakened_binding_receive_def example.weakened_binding_auth_def
    example.certificate_ok_def current_use_allowed_def
  by (cases field)
     (simp_all add: changed_context_def changed_request_def example_request_def example_certificate_def
       example_statement_def example_binding_def example_context_def example_roster_def
       example_threshold_def example_verifies_def example_signed_def example_truth_def
         empty_message_state_def)

lemma all_binding_removals_violate_source:
  "example_source (binding_key (changed_binding field)) \<noteq>
    Some \<lparr>statement_binding = changed_binding field, statement_status = Finalized\<rparr>"
  by (cases field)
     (simp_all add: example_source_def example_statement_def example_binding_def)

lemma missing_destination_allows_second_credit:
  "example.weakened_binding_receive Destination_Field (changed_context Destination_Field)
      (changed_request Destination_Field) (record_credit (example_binding 17) empty_message_state) =
    (record_credit (changed_binding Destination_Field)
      (record_credit (example_binding 17) empty_message_state), New_Credit (changed_binding
        Destination_Field))"
  unfolding example.weakened_binding_receive_def example.weakened_binding_auth_def
    example.certificate_ok_def current_use_allowed_def
  by (simp add: changed_context_def changed_request_def example_request_def example_certificate_def
      example_statement_def example_binding_def example_context_def example_roster_def example_threshold_def
      example_verifies_def example_signed_def example_truth_def record_credit_def credit_marker_def
        empty_message_state_def)

lemma dual_destination_occurrences_are_two:
  "count_list (map binding_key (credit_history
      (record_credit (changed_binding Destination_Field)
       (record_credit (example_binding 17) empty_message_state)))) (0,17) = 2"
  by (simp add: record_credit_def changed_request_def example_binding_def empty_message_state_def)

lemma once_removal_reexecutes:
  "example.receive_without_once example_context (example_request 17)
     (record_credit (example_binding 17) empty_message_state) =
    (record_credit (example_binding 17) (record_credit (example_binding 17) empty_message_state),
      New_Credit (example_binding 17))"
  using example_request_authenticated
  by (simp add: example.receive_without_once_def example.credit_admissible_def example_request_def
    example_binding_def)

lemma equal_value_credit_occurrences_are_two:
  "count_list (map binding_key (credit_history
    (record_credit (example_binding 17) (record_credit (example_binding 17) empty_message_state)))) (0,17) =
      2"
  by (simp add: record_credit_def example_binding_def empty_message_state_def)

definition erase_once_markers :: "message_state \<Rightarrow> message_state" where
  "erase_once_markers s = s\<lparr>consumed_at := {}\<rparr>"

lemma epoch_rotation_does_not_reset_history:
  "example.receive_credit Bypass_Route
      (example_context\<lparr>context_authority_epoch := 10\<rparr>)
      ((example_request 17)\<lparr>request_authority_epoch := 10\<rparr>)
      (record_credit (example_binding 17) empty_message_state) =
    (record_credit (example_binding 17) empty_message_state, Duplicate_Credit (example_binding 17))"
  unfolding example.receive_credit_def example.credit_admissible_def example.authenticated_request_def
    example.certificate_ok_def current_use_allowed_def
  by (simp add: example_context_def example_request_def example_binding_def example_certificate_def
      example_statement_def example_roster_def example_threshold_def example_verifies_def
      example_signed_def example_truth_def record_credit_def)

lemma erased_marker_reexecutes_after_rotation:
  "example.receive_credit Bypass_Route
      (example_context\<lparr>context_authority_epoch := 10\<rparr>)
      ((example_request 17)\<lparr>request_authority_epoch := 10\<rparr>)
      (erase_once_markers (record_credit (example_binding 17) empty_message_state)) =
    (record_credit (example_binding 17)
      (erase_once_markers (record_credit (example_binding 17) empty_message_state)), New_Credit
        (example_binding 17))"
  unfolding example.receive_credit_def example.credit_admissible_def example.authenticated_request_def
    example.certificate_ok_def current_use_allowed_def
  by (simp add: example_context_def example_request_def example_binding_def example_certificate_def
      example_statement_def example_roster_def example_threshold_def example_verifies_def
      example_signed_def example_truth_def erase_once_markers_def)

section \<open>Threshold and Decision Boundaries\<close>

definition header_certificate_ok :: "nat \<Rightarrow> source_certificate \<Rightarrow> bool" where
  "header_certificate_ok header cert \<longleftrightarrow>
    example_verifies cert \<and> distinct (certificate_signers cert) \<and>
    set (certificate_signers cert) \<subseteq> example_roster (certificate_epoch cert) \<and>
    header \<le> length (certificate_signers cert)"

definition false_certificate :: source_certificate where
  "false_certificate = (example_certificate 17)
    \<lparr>certificate_statement := \<lparr>statement_binding = changed_binding Amount_Field,
      statement_status = Finalized\<rparr>, certificate_signers := [0]\<rparr>"

lemma untrusted_threshold_certifies_false_source:
  "header_certificate_ok 1 false_certificate \<and>
   \<not> example.certificate_ok false_certificate \<and>
   \<not> example_truth (certificate_statement false_certificate)"
  unfolding header_certificate_ok_def example.certificate_ok_def
  by (simp add: false_certificate_def example_certificate_def example_roster_def example_threshold_def
      example_verifies_def example_signed_def example_truth_def example_observation_def
      example_statement_def example_binding_def)

definition counted_list_certificate_ok :: "source_certificate \<Rightarrow> bool" where
  "counted_list_certificate_ok cert \<longleftrightarrow> example_verifies cert \<and>
    set (certificate_signers cert) \<subseteq> example_roster (certificate_epoch cert) \<and>
    example_threshold (certificate_epoch cert) \<le> length (certificate_signers cert)"

lemma duplicated_byzantine_signer_cannot_form_quorum:
  "counted_list_certificate_ok (false_certificate\<lparr>certificate_signers := [0,0]\<rparr>) \<and>
   \<not> example.certificate_ok (false_certificate\<lparr>certificate_signers := [0,0]\<rparr>)"
  unfolding counted_list_certificate_ok_def example.certificate_ok_def
  by (simp add: false_certificate_def example_certificate_def example_roster_def example_threshold_def
      example_verifies_def example_signed_def)

lemma quorum_above_faults_does_not_select_one_decision:
  "card ({0,1} :: nat set) = 2 \<and> card ({0,2} :: nat set) = 2 \<and>
   ({0,1} :: nat set) \<inter> {0,2} = {0} \<and> (1::nat) < 2"
  by simp

theorem decision_quorums_have_honest_intersection:
  assumes fin: "finite population" and a: "a \<subseteq> population" and b: "b \<subseteq> population"
    and faults: "bad \<subseteq> population" "card bad \<le> f"
    and sizes: "q \<le> card a" "q \<le> card b" "card population + f < 2*q"
  shows "\<exists>signer \<in> a \<inter> b. signer \<notin> bad"
proof -
  have fa: "finite a" using finite_subset[OF a fin] .
  have fb: "finite b" using finite_subset[OF b fin] .
  have fbad: "finite bad" using finite_subset[OF faults(1) fin] .
  have union_subset: "a \<union> b \<subseteq> population" using a b by blast
  have un: "card (a \<union> b) \<le> card population"
    by (rule card_mono[OF fin union_subset])
  have counts: "card a + card b = card (a \<union> b) + card (a \<inter> b)"
    using card_Un_Int[OF fa fb] by arith
  have "\<not> a \<inter> b \<subseteq> bad"
  proof
    assume intersection_subset: "a \<inter> b \<subseteq> bad"
    have "card (a \<inter> b) \<le> card bad" by (rule card_mono[OF fbad intersection_subset])
    with counts un faults(2) sizes show False by linarith
  qed
  then show ?thesis by blast
qed

section \<open>Compression Must Preserve Raw Rejection\<close>

definition blind_encode :: "normal_envelope \<Rightarrow> bypass_packet option" where
  "blind_encode m = (let r = envelope_request m in
    Some \<lparr>bypass_certificate = request_certificate r, bypass_caller = request_caller r,
      bypass_authority_epoch = request_authority_epoch r, bypass_version = request_version r\<rparr>)"

definition malformed_envelope :: normal_envelope where
  "malformed_envelope = \<lparr>envelope_id = 100,
    envelope_request = changed_request Recipient_Field\<rparr>"

lemma blind_compression_launders_rejected_input:
  "encode_bypass malformed_envelope = None \<and>
   example.receive_normal example_context malformed_envelope empty_message_state =
     (empty_message_state, Message_Rejected) \<and>
   example.receive_bypass example_context (blind_encode malformed_envelope) empty_message_state =
     (record_credit (example_binding 17) empty_message_state, New_Credit (example_binding 17))"
  using example_new_credit example_missing_binding_rejects
  by (simp add: encode_bypass_def blind_encode_def decode_bypass_def example.receive_normal_def
      example.receive_bypass_def example.receive_credit_def Let_def malformed_envelope_def
      changed_request_def example_request_def example_certificate_def example_statement_def
        example_binding_def)

definition certificate_only :: "normal_envelope \<Rightarrow> source_certificate" where
  "certificate_only m = request_certificate (envelope_request m)"

lemma certificate_only_cannot_preserve_current_permissions:
  "\<not> (\<exists>receiver. \<forall>m. receiver (certificate_only m) = example.normal_semantics m)"
proof -
  let ?fresh = "example_envelope 100 17"
  let ?stale = "refresh_envelope 7 4 ?fresh"
  have same: "certificate_only ?fresh = certificate_only ?stale"
    by (simp add: certificate_only_def refresh_envelope_def)
  have separates: "example.receive_normal example_context ?fresh empty_message_state \<noteq>
    example.receive_normal example_context ?stale empty_message_state"
    using example_new_credit example_current_authority_rejects
    by (simp add: example.receive_normal_def example_envelope_def refresh_envelope_def
        example.receive_credit_def example.credit_admissible_def example.authenticated_request_def
        current_use_allowed_def example_context_def)
  show ?thesis using example.separating_requests_prevent_exact_translation[OF same separates] .
qed

end
