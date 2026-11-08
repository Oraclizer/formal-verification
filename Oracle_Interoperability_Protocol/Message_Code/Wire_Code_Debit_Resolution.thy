theory Wire_Code_Debit_Resolution
  imports Wire_Code_Resolution_Control
begin

record code_source_receipt_reservation =
  source_reservation_binding :: code_source_binding
  source_reservation_holder :: nat
  source_reservation_generation :: nat
  source_reservation_deadline :: nat
  source_reservation_active :: bool
  source_reservation_versions :: "(nat \<times> nat) list"

definition code_source_debit_receipt_credential ::
  "nat \<Rightarrow> nat \<Rightarrow> code_source_call_payload \<Rightarrow> code_source_receipt_reservation option \<Rightarrow> bool" where
  "code_source_debit_receipt_credential actor epoch payload reservation =
    (case source_payload_command payload of Wire_Debit signed_generation \<Rightarrow>
      (case (source_payload_credential payload,reservation) of (Some credential,Some stored) \<Rightarrow>
        let token = credential_token credential; binding = source_payload_binding payload in
        token_asset token = source_binding_asset binding \<and>
        credential_origin credential = source_binding_origin binding \<and>
        source_reservation_binding stored = binding \<and>
        token_owner token = source_reservation_holder stored \<and>
        source_reservation_holder stored = actor \<and>
        token_generation token = source_reservation_generation stored \<and>
        signed_generation = source_reservation_generation stored \<and>
        credential_epoch credential = epoch
       | _ \<Rightarrow> False)
     | _ \<Rightarrow> False)"

datatype code_source_resolution_tail =
    Code_Source_Resolved code_source_resolution
  | Code_Source_Resolve_Error code_source_wire_error

definition code_source_finish_resolution_observation ::
  "code_source_control_observation \<Rightarrow> (nat \<times> wire_bytes) option \<Rightarrow> code_source_resolution \<Rightarrow>
    (code_source_resolution_tail \<times> code_source_debit_request option)" where
  "code_source_finish_resolution_observation observed current_value result =
    (case code_source_resolution_observation_fence observed current_value of
       Some reason \<Rightarrow> (Code_Source_Resolve_Error reason,None)
     | None \<Rightarrow> (Code_Source_Resolved result,None))"

definition code_source_close_resolution ::
  "code_source_control_observation \<Rightarrow> code_source_debit_request \<Rightarrow> registered_identity option \<Rightarrow>
    bool \<Rightarrow> bool option \<Rightarrow> (code_source_resolution_tail \<times> code_source_debit_request option)" where
  "code_source_close_resolution observed request execute_identity may_close_unseen replacement =
    (if execute_identity = None then (Code_Source_Resolve_Error Code_Source_Wire_Product_Rejected,None)
     else if code_source_resolution_disposition observed request = Inr None \<and> \<not> may_close_unseen
     then (Code_Source_Resolve_Error Code_Source_Wire_Product_Rejected,None)
     else case code_source_reject_debit_step observed request of
       Code_Source_Close_Refused reason \<Rightarrow> (Code_Source_Resolve_Error reason,None)
     | Code_Source_Close_Already_Rejected \<Rightarrow> (Code_Source_Resolved Code_Source_Resolution_Rejected,None)
     | Code_Source_Close_Replace \<Rightarrow>
         (case replacement of Some True \<Rightarrow>
            (Code_Source_Resolved Code_Source_Resolution_Rejected,Some request)
          | _ \<Rightarrow>
            (Code_Source_Resolve_Error (Code_Source_Wire_Recovery Code_Source_Recovery_Hold),Some request)))"

definition code_source_resolve_debit_tail ::
  "code_source_control_observation \<Rightarrow> code_source_debit_request \<Rightarrow> authenticated_message_id \<Rightarrow>
    wire_bytes \<Rightarrow> wire_bytes option \<Rightarrow> code_source_receipt option \<Rightarrow> bool \<Rightarrow>
    registered_identity option \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> code_source_call_payload \<Rightarrow>
    code_source_receipt_reservation option \<Rightarrow> (nat \<times> wire_bytes) option \<Rightarrow> bool option \<Rightarrow>
    (code_source_resolution_tail \<times> code_source_debit_request option)" where
  "code_source_resolve_debit_tail observed request transport exact prior receipt close execute_identity actor epoch payload reservation current_value replacement =
    (case code_source_resolution_principal_refusal observed actor of Some reason \<Rightarrow> (Code_Source_Resolve_Error reason,None)
     | None \<Rightarrow> (case code_source_resolution_disposition observed request of
       Inl reason \<Rightarrow> (Code_Source_Resolve_Error reason,None)
     | Inr disposition \<Rightarrow>
       (case code_source_pending_transport_refusal transport (source_debit_packet request) (source_control_decisions observed) of
          Some reason \<Rightarrow> (Code_Source_Resolve_Error reason,None)
        | None \<Rightarrow> (case code_compare_binding prior exact of
            Code_Replay_Conflict \<Rightarrow> (Code_Source_Resolve_Error (Code_Source_Wire_Validation Conflicting_Wire_Replay),None)
          | arrival \<Rightarrow>
            (case receipt of
               Some (Code_Source_Ordinary_Receipt (Code_Source_Collected outcome)) \<Rightarrow>
                 if disposition = Some Ref_Explicit_Rejection \<or> arrival \<noteq> Code_Identical
                 then (Code_Source_Resolve_Error (Code_Source_Wire_Validation Conflicting_Wire_Replay),None)
                 else code_source_finish_resolution_observation observed current_value
                   (Code_Source_Resolution_Published (Code_Source_Ordinary_Receipt (Code_Source_Collected outcome)))
             | Some (Code_Source_Ordinary_Receipt Code_Source_Collection_Waiting) \<Rightarrow>
                 if disposition \<in> {Some Ref_Applied,Some Ref_Retained_Refusal}
                 then (Code_Source_Resolve_Error (Code_Source_Wire_Recovery Code_Source_Recovery_Hold),None)
                 else if disposition = Some Ref_Explicit_Rejection then
                   code_source_finish_resolution_observation observed current_value Code_Source_Resolution_Rejected
                 else if close then
                   code_source_close_resolution observed request execute_identity
                     (code_source_debit_receipt_credential actor epoch payload reservation) replacement
                 else code_source_finish_resolution_observation observed current_value Code_Source_Resolution_Unresolved
             | _ \<Rightarrow> (Code_Source_Resolve_Error (Code_Source_Wire_Validation Conflicting_Wire_Replay),None))))))"

theorem receipt_credential_lookup_does_not_reconsume_deadline_active_or_version_state:
  "code_source_debit_receipt_credential actor epoch payload
      (Some (stored\<lparr>source_reservation_deadline := deadline,source_reservation_active := active,
        source_reservation_versions := versions\<rparr>)) =
    code_source_debit_receipt_credential actor epoch payload (Some stored)"
  by (auto simp: code_source_debit_receipt_credential_def Let_def
    split: ordinary_wire_command.splits option.splits)

lemma a_missing_debit_credential_cannot_close_unseen_work:
  assumes "source_payload_command payload = Wire_Debit generation"
    "source_payload_credential payload = None"
  shows "\<not> code_source_debit_receipt_credential actor epoch payload reservation"
  using assms by (simp add: code_source_debit_receipt_credential_def split: option.splits)

lemma a_close_requires_current_execute_authorization:
  "code_source_close_resolution observed request None may_close_unseen replacement =
    (Code_Source_Resolve_Error Code_Source_Wire_Product_Rejected,None)"
  by (simp add: code_source_close_resolution_def)

lemma a_failed_control_replacement_is_not_reported_as_an_explicit_rejection:
  assumes "execute_identity \<noteq> None"
    "code_source_resolution_disposition observed request \<noteq> Inr None \<or> may_close_unseen"
    "code_source_reject_debit_step observed request = Code_Source_Close_Replace"
    "replacement \<noteq> Some True"
  shows "code_source_close_resolution observed request execute_identity may_close_unseen replacement =
    (Code_Source_Resolve_Error (Code_Source_Wire_Recovery Code_Source_Recovery_Hold),Some request)"
  using assms by (auto simp: code_source_close_resolution_def split: option.splits bool.splits if_splits)

lemma a_completed_nonclosing_resolution_keeps_the_exact_observation:
  assumes "code_source_finish_resolution_observation observed current_value result = (Code_Source_Resolved returned,None)"
  shows "current_value = Some (source_control_stored observed)" "returned = result"
proof -
  have checked: "code_source_resolution_observation_fence observed current_value = None \<and> returned = result"
    using assms by (auto simp: code_source_finish_resolution_observation_def split: option.splits)
  show "current_value = Some (source_control_stored observed)"
    by (rule a_successful_resolution_fence_compares_the_actual_revision_and_exact_bytes) (use checked in simp)
  show "returned = result" using checked by simp
qed

theorem an_identical_published_source_debit_returns_the_actual_collected_receipt:
  assumes principal: "code_source_resolution_principal_refusal observed actor = None"
    and status: "code_source_resolution_disposition observed request = Inr (Some Ref_Applied)"
    and pending: "code_source_pending_transport_refusal transport (source_debit_packet request) (source_control_decisions observed) = None"
    and original: "prior = Some exact"
    and receipt: "stored = Some (Code_Source_Ordinary_Receipt (Code_Source_Collected outcome))"
    and current: "current_value = Some (source_control_stored observed)"
  shows "code_source_resolve_debit_tail observed request transport exact prior stored close execute_identity actor epoch payload reservation current_value replacement =
    (Code_Source_Resolved (Code_Source_Resolution_Published (Code_Source_Ordinary_Receipt (Code_Source_Collected outcome))),None)"
  using assms by (simp add: code_source_resolve_debit_tail_def code_compare_binding_def
    code_source_finish_resolution_observation_def code_source_resolution_observation_fence_def)

lemma a_waiting_receipt_cannot_report_an_already_published_control_as_unresolved:
  assumes principal: "code_source_resolution_principal_refusal observed actor = None"
    and status: "code_source_resolution_disposition observed request = Inr (Some Ref_Applied)"
    and pending: "code_source_pending_transport_refusal transport (source_debit_packet request) (source_control_decisions observed) = None"
    and original: "prior = Some exact"
  shows "code_source_resolve_debit_tail observed request transport exact prior
      (Some (Code_Source_Ordinary_Receipt Code_Source_Collection_Waiting)) close execute_identity actor epoch payload reservation current_value replacement =
    (Code_Source_Resolve_Error (Code_Source_Wire_Recovery Code_Source_Recovery_Hold),None)"
  using assms by (simp add: code_source_resolve_debit_tail_def code_compare_binding_def)

lemma a_rejected_original_with_a_waiting_receipt_still_fences_the_exact_observation:
  assumes principal: "code_source_resolution_principal_refusal observed actor = None"
    and status: "code_source_resolution_disposition observed request = Inr (Some Ref_Explicit_Rejection)"
    and pending: "code_source_pending_transport_refusal transport (source_debit_packet request) (source_control_decisions observed) = None"
    and original: "prior = Some exact"
    and current: "current_value = Some (source_control_stored observed)"
  shows "code_source_resolve_debit_tail observed request transport exact prior
      (Some (Code_Source_Ordinary_Receipt Code_Source_Collection_Waiting)) close execute_identity actor epoch payload reservation current_value replacement =
    (Code_Source_Resolved Code_Source_Resolution_Rejected,None)"
  using assms by (simp add: code_source_resolve_debit_tail_def code_compare_binding_def
    code_source_finish_resolution_observation_def code_source_resolution_observation_fence_def)

text \<open>
  Source: wire.rs resolve_wire_debit after current receipt authorization and
  typed original materialization; ordered.rs unchanged/reject_debit; and
  lock_finality.rs receipt_credential_matches/bound_credential for Debit.
  All four control dispositions plus absence and every receipt class are
  classified. A closing CAS attempt is returned separately as Some request:
  an error/ambiguous replacement must not be mislabelled as no control effect.
  execute_identity, receipt, current_value and replacement are typed results
  of the actual fixed current product/store operations. Their request,
  selected-state, serialization and commit provenance must be established by
  the surrounding resolver, not assumed from this tail classifier.
  This does not stand for the complete original resolver: storage/attachment
  selection, exact preflight, current Receipt authorization and source result
  conversion still need their explicit composition and actual execution.
\<close>

end
