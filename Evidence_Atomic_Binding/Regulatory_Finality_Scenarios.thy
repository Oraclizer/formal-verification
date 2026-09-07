(* SPDX-License-Identifier: BSD-3-Clause *)
theory Regulatory_Finality_Scenarios
  imports Source_Finality_Link Finality_Refinement
begin

section \<open>A Produced Monetary Receipt and a Separate Regulatory Input\<close>

definition regulation_money_binding :: transfer_binding where
  "regulation_money_binding=(example_binding 17)\<lparr>binding_asset:=20\<rparr>"

definition regulation_money_statement :: source_statement where
  "regulation_money_statement=\<lparr>statement_binding=regulation_money_binding,statement_status=Finalized\<rparr>"

definition regulation_balances :: "source_account \<Rightarrow> nat" where
  "regulation_balances account=(if account=(0,20) then 10 else 0)"

definition regulation_source_commands :: "controlled_source_command list" where
  "regulation_source_commands=[Controlled_Boundary(Boundary_Apply regulation_money_binding),
    Controlled_Finalize regulation_money_binding]"

definition regulation_source :: controlled_source_state where
  "regulation_source=run_controlled_source regulation_source_commands(initial_controlled_source regulation_balances)"

definition regulation_money_certificate :: source_certificate where
  "regulation_money_certificate=\<lparr>certificate_statement=regulation_money_statement,
    certificate_epoch=8,certificate_signers=[0,1],certificate_signature=17\<rparr>"

definition regulation_money_receipts :: "source_certificate list" where
  "regulation_money_receipts=generated_source_receipts regulation_balances regulation_source_commands
    [regulation_money_certificate]"

lemmas regulation_source_definitions = regulation_money_binding_def regulation_money_statement_def
  regulation_balances_def regulation_source_commands_def regulation_source_def
  initial_controlled_source_def initial_source_boundary_def controlled_boundary_def
  controlled_finalize_def controlled_record_finalized_def controlled_source_fact_def
  boundary_apply_def boundary_record_effect_def boundary_has_effect_def boundary_valid_binding_def
  source_account_of_def example_binding_def

theorem monetary_source_really_debits_and_finalizes_the_shared_asset:
  "boundary_effects(controlled_endpoint regulation_source)=[regulation_money_binding] \<and>
    boundary_units(controlled_endpoint regulation_source)(0,20)=5 \<and>
    controlled_source_fact regulation_source(0,17)=Some regulation_money_statement"
  by (simp add: regulation_source_definitions Let_def)

theorem monetary_receipt_is_issued_by_the_actual_source:
  "regulation_money_receipts=[regulation_money_certificate]"
  by (simp add: regulation_money_receipts_def generated_source_receipts_def
      issue_source_receipt_def source_receipt_slot_available_def regulation_money_certificate_def
      regulation_source_definitions Let_def)

theorem monetary_receipt_has_the_generated_source_fact:
  "controlled_produced_fact regulation_balances regulation_source_commands regulation_money_statement"
proof -
  have sound: "receipt_log_sound regulation_balances regulation_source_commands regulation_money_receipts"
    unfolding regulation_money_receipts_def by (rule every_generated_receipt_has_a_produced_source_fact)
  show ?thesis using sound
    by (simp add: receipt_log_sound_def monetary_receipt_is_issued_by_the_actual_source
        regulation_money_certificate_def)
qed

definition regulation_receipts :: "source_certificate list" where
  "regulation_receipts=regulation_money_receipts@[example_certificate 20]"

definition regulation_receipt_truth :: "source_statement \<Rightarrow> bool" where
  "regulation_receipt_truth statement \<longleftrightarrow>
    statement\<in>set(map certificate_statement regulation_receipts)"

definition regulation_stable_source :: "source_key \<Rightarrow> source_statement option" where
  "regulation_stable_source key=(if key=(0,17) then Some regulation_money_statement
    else if key=(0,20) then Some(example_statement 20) else None)"

lemma regulation_receipts_exact:
  "regulation_receipts=[regulation_money_certificate,example_certificate 20]"
  by (simp add: regulation_receipts_def monetary_receipt_is_issued_by_the_actual_source)

lemma regulation_receipt_members:
  "set regulation_receipts={regulation_money_certificate,example_certificate 20}"
  by (simp add: regulation_receipts_exact)

lemma supplied_regulatory_fact_is_the_existing_parent_input:
  "example.certificate_ok(example_certificate 20) \<and>
    example_truth(example_statement 20) \<and>
    example_source(0,20)=Some(example_statement 20)"
  by (simp add: example.certificate_ok_def example_verifies_def example_signed_def
      example_truth_def example_source_def example_statement_def example_certificate_def
      example_roster_def example_threshold_def)

theorem every_combined_fact_has_its_stated_origin:
  assumes "regulation_receipt_truth statement"
  shows "controlled_produced_fact regulation_balances regulation_source_commands statement \<or>
    (statement=example_statement 20 \<and> example_truth statement)"
  using assms monetary_receipt_has_the_generated_source_fact
  by (auto simp: regulation_receipt_truth_def regulation_receipts_exact
      regulation_money_certificate_def example_certificate_def example_truth_def)

interpretation regulation_case: source_attestation example_roster example_faulty example_bound example_threshold
  "source_receipt_verifies regulation_receipts" "source_receipt_signed regulation_receipts"
  regulation_receipt_truth regulation_stable_source
proof unfold_locales
  fix epoch
  show "finite(example_roster epoch)" by (simp add: example_roster_def)
  show "example_faulty epoch\<subseteq>example_roster epoch"
    by (simp add: example_faulty_def example_roster_def)
  show "card(example_faulty epoch)\<le>example_bound epoch"
    by (simp add: example_faulty_def example_bound_def)
  show "example_bound epoch<example_threshold epoch"
    by (simp add: example_bound_def example_threshold_def)
next
  fix cert signer
  assume "source_receipt_verifies regulation_receipts cert" "signer\<in>set(certificate_signers cert)"
  then show "source_receipt_signed regulation_receipts signer(certificate_epoch cert)(certificate_statement cert)"
    by (auto simp: source_receipt_verifies_def source_receipt_signed_def)
next
  fix signer epoch statement
  assume "signer\<in>example_roster epoch" "signer\<notin>example_faulty epoch"
    "source_receipt_signed regulation_receipts signer epoch statement"
  then show "regulation_receipt_truth statement"
    by (auto simp: source_receipt_signed_def regulation_receipt_truth_def example_faulty_def)
next
  fix statement
  assume "regulation_receipt_truth statement" "statement_status statement\<noteq>Observed"
  then show "regulation_stable_source(binding_key(statement_binding statement))=Some statement"
    by (auto simp: regulation_receipt_truth_def regulation_receipts_exact regulation_stable_source_def
        regulation_money_certificate_def regulation_money_statement_def regulation_money_binding_def
        example_certificate_def example_statement_def example_binding_def)
qed

lemma both_receipts_pass_the_actual_parent_checker:
  "regulation_case.certificate_ok regulation_money_certificate \<and>
    regulation_case.certificate_ok(example_certificate 20)"
  unfolding regulation_case.certificate_ok_def
  by (simp add: source_receipt_verifies_def regulation_receipts_exact
      regulation_money_certificate_def example_certificate_def example_roster_def example_threshold_def)

text \<open>The monetary receipt is produced by the controlled source's actual
  Apply and Finalize operations. The regulatory receipt is the separately
  provided regulatory example input of the existing message model. Its
  physical source production and transport remain UNVERIFIED. The two keys
  are distinct while their asset is shared. This finite combination does not
  establish a new consensus protocol or a physical regulatory authority.\<close>

section \<open>Actual Child Credit and Primary Publication\<close>

definition regulation_context :: "nat \<Rightarrow> lock_context" where
  "regulation_context endpoint=\<lparr>
    lock_authority=example_context\<lparr>context_endpoint:=endpoint\<rparr>,
    lock_metadata=example_snapshot ACTIVE,lock_restrictions=(\<lambda>_.True),lock_dependencies=(\<lambda>_.[]),
    lock_write_permissions={},lock_spend_permissions=UNIV\<rparr>"

definition regulation_money_request :: execution_request where
  "regulation_money_request=\<lparr>request_binding=regulation_money_binding,
    request_certificate=regulation_money_certificate,request_caller=7,request_authority_epoch=9,request_version=4\<rparr>"

definition regulation_genesis :: finality_core where
  "regulation_genesis=initial_finality_core regulation_balances(example_snapshot ACTIVE)regulation_context"

definition regulation_credit_trace :: "finality_operation list" where
  "regulation_credit_trace=[
    Invoke_Protocol 0 0 0(Reserve_Intent regulation_money_request [] 10),
    Invoke_Protocol 0 1 0(Dispatch_Intent regulation_money_request 0 []),
    Invoke_Protocol 0 2 0(Source_Intent regulation_money_request 0 []),
    Record_Terminal regulation_money_certificate,
    Invoke_Protocol 0 4 0(Certificate_Intent regulation_money_certificate),
    Invoke_Protocol 2 5 0(Deliver_Intent Bypass_Route regulation_money_request),
    Publish_Primary(0,17)]"

definition regulation_root_ready :: finality_core where
  "regulation_root_ready=regulation_case.run_finality regulation_credit_trace regulation_genesis"

definition regulation_pending_reservation :: asset_reservation where
  "regulation_pending_reservation=\<lparr>reservation_binding=regulation_money_binding,
    reservation_footprint=[20],reservation_worker=7,reservation_generation=0,
    reservation_deadline=10,reservation_phase=Source_Pending\<rparr>"

definition regulation_root_record :: terminal_record where
  "regulation_root_record=\<lparr>terminal_binding=regulation_money_binding,terminal_kind=Confirmed_Decision,
    terminal_evidence=[regulation_money_certificate]\<rparr>"

lemmas regulation_payload_definitions = regulation_money_binding_def regulation_money_statement_def
  regulation_money_certificate_def regulation_money_request_def regulation_context_def regulation_balances_def
  regulation_root_record_def regulation_pending_reservation_def
  example_binding_def example_statement_def example_certificate_def example_request_def example_context_def

lemmas regulation_authentication_definitions = regulation_case.certificate_ok_def
  regulation_case.credit_admissible_def regulation_case.authenticated_request_def
  source_receipt_verifies_def regulation_receipt_members example_roster_def example_threshold_def
  current_use_allowed_def

lemmas regulation_parent_definitions = acquire_reservation_def dispatch_source_def execute_source_effect_def
  current_use_allowed_def required_footprint_def owns_current_reservation_def owns_recorded_reservation_def
  phase_at_def set_phase_def finish_reservation_def binding_is_registered_def source_was_debited_def
  source_account_of_def destination_account_of_def holder_account_def metadata_permission_def
  get_reg_state_def get_asset_state_def ordinary_transfer_allowed_def
  record_observation_def commit_reservation_event_def record_credit_def credit_marker_def
  empty_message_state_def initial_reservation_state_def initial_reservation_machine_def

lemmas regulation_core_definitions = regulation_case.run_finality.simps regulation_case.finality_step_def
  regulation_case.core_result.simps regulation_case.invoke_protocol_def regulation_case.record_terminal_def
  regulation_case.publish_primary_def regulation_case.intent_result.simps source_origin_present_def
  terminal_effect_completed_def current_lock_view_def lift_protocol_result_def vector_lookup_def
  exact_record_reference_def record_reference_def initial_finality_core_def

lemma regulation_root_ready_financial_state:
  "machine_state(core_parent regulation_root_ready)=(initial_reservation_state regulation_balances)\<lparr>
    asset_owner:=(\<lambda>_.None)(20:=Some(0,17)),
    reservation_at:=(\<lambda>_.None)((0,17):=Some regulation_pending_reservation),
    source_units:=regulation_balances((0,20):=5),source_effects:=[regulation_money_binding],
    issued_certificates:=[regulation_money_certificate],
    received_messages:=record_credit regulation_money_binding empty_message_state,
    destination_units:=(\<lambda>_.0)((2,20,3):=5),funded_units:=(\<lambda>_.0)(((0,17),(2,20,3)):=5)\<rparr>"
proof -
  have receipt_members: "set regulation_receipts={regulation_money_certificate,example_certificate 20}"
    by (simp add: regulation_receipts_exact)
  show ?thesis
    unfolding regulation_root_ready_def regulation_credit_trace_def regulation_case.run_finality.simps
    by (simp add: regulation_genesis_def regulation_core_definitions regulation_payload_definitions
        regulation_case.certificate_ok_def regulation_case.credit_admissible_def
        regulation_case.authenticated_request_def source_receipt_verifies_def receipt_members
        example_roster_def example_threshold_def regulation_parent_definitions
        regulation_case.publish_source_certificate_def regulation_case.deliver_reserved_credit_def
        regulation_case.published_receive_expansion example_snapshot_def Let_def fun_eq_iff)
qed

lemma regulation_root_ready_core_fields:
  "core_epoch regulation_root_ready=7 \<and>
    core_contexts regulation_root_ready=regulation_context \<and>
    core_regulatory regulation_root_ready=\<lparr>receiver_snapshot=example_snapshot ACTIVE,receiver_applied={}\<rparr> \<and>
    core_records regulation_root_ready=(\<lambda>_.None)((0,17):=Some regulation_root_record) \<and>
    core_published regulation_root_ready={(0,17)}"
proof -
  have receipt_members: "set regulation_receipts={regulation_money_certificate,example_certificate 20}"
    by (simp add: regulation_receipts_exact)
  show ?thesis
    unfolding regulation_root_ready_def regulation_credit_trace_def regulation_case.run_finality.simps
    by (simp add: regulation_genesis_def regulation_core_definitions regulation_payload_definitions
        regulation_case.certificate_ok_def regulation_case.credit_admissible_def
        regulation_case.authenticated_request_def source_receipt_verifies_def receipt_members
        example_roster_def example_threshold_def regulation_parent_definitions
        regulation_case.publish_source_certificate_def regulation_case.deliver_reserved_credit_def
        regulation_case.published_receive_expansion example_snapshot_def Let_def fun_eq_iff)
qed

theorem produced_money_reaches_actual_child_primary:
  "binding_key regulation_money_binding=(0,17) \<and>
    binding_asset regulation_money_binding=20 \<and>
    source_effects(machine_state(core_parent regulation_root_ready))=[regulation_money_binding] \<and>
    credit_history(received_messages(machine_state(core_parent regulation_root_ready)))=[regulation_money_binding] \<and>
    destination_units(machine_state(core_parent regulation_root_ready))(2,20,3)=5 \<and>
    (0,17)\<in>core_published regulation_root_ready"
  by (simp add: regulation_root_ready_financial_state regulation_root_ready_core_fields
      regulation_money_binding_def example_binding_def record_credit_def empty_message_state_def)

section \<open>Freeze Is Applied by the Existing Regulatory Receiver\<close>

definition regulation_freeze_record :: terminal_record where
  "regulation_freeze_record=\<lparr>terminal_binding=example_binding 20,terminal_kind=Confirmed_Decision,
    terminal_evidence=[example_certificate 20]\<rparr>"

definition regulation_recorded :: finality_core where
  "regulation_recorded=regulation_case.finality_step(Record_Terminal(example_certificate 20))regulation_root_ready"

lemma regulation_recorded_shape:
  "regulation_recorded=regulation_root_ready\<lparr>
    core_records:=(core_records regulation_root_ready)((0,20):=Some regulation_freeze_record),core_epoch:=8\<rparr>"
  unfolding regulation_recorded_def regulation_case.finality_step_def regulation_case.core_result.simps
    regulation_case.record_terminal_def
  by (simp add: regulation_root_ready_core_fields regulation_freeze_record_def source_origin_present_def
      regulation_authentication_definitions regulation_payload_definitions Let_def)

lemma regulation_recorded_current_context:
  "current_lock_view regulation_recorded 2=regulation_context 2 \<and>
    lock_authority(current_lock_view regulation_recorded 2)=example_context"
  by (simp add: regulation_recorded_shape regulation_root_ready_core_fields current_lock_view_def
      regulation_context_def example_context_def)

lemma regulation_request_is_authenticated_by_the_combined_profile:
  "regulation_case.authenticated_request example_context(example_request 20)"
  unfolding regulation_case.authenticated_request_def regulation_case.certificate_ok_def
  by (simp add: regulation_authentication_definitions regulation_payload_definitions)

theorem combined_regulatory_receiver_really_executes_sync:
  "regulation_case.apply_regulatory_message example_context(example_request 20)
      \<lparr>receiver_snapshot=example_snapshot ACTIVE,receiver_applied={}\<rparr> =
    Some \<lparr>receiver_snapshot=example_snapshot FROZEN,receiver_applied={(0,20)}\<rparr>"
  using regulation_request_is_authenticated_by_the_combined_profile
  unfolding regulation_case.apply_regulatory_message_def
  by (simp add: example_request_def example_binding_def sync_def example_snapshot_def
      get_reg_state_def get_asset_state_def acquire_lock_def is_locked_def
      connected_chains_def asset_exists_def update_all_chains_def release_lock_def Let_def fun_eq_iff)

definition regulation_frozen :: finality_core where
  "regulation_frozen=regulation_case.finality_step(Invoke_Regulatory 2 8 0(example_request 20))regulation_recorded"

theorem actual_child_freeze_succeeds:
  "regulation_case.invoke_regulatory 2 8 0(example_request 20)regulation_recorded =
    (regulation_recorded\<lparr>core_regulatory:=
      \<lparr>receiver_snapshot=example_snapshot FROZEN,receiver_applied={(0,20)}\<rparr>\<rparr>,Regulatory_Applied)"
proof -
  have at_epoch: "core_epoch regulation_recorded=8"
    by (simp add: regulation_recorded_shape)
  have reference: "exact_record_reference regulation_recorded 0(request_binding(example_request 20))
    Confirmed_Decision(request_certificate(example_request 20))"
    by (simp add: regulation_recorded_shape regulation_root_ready_core_fields regulation_freeze_record_def
        exact_record_reference_def record_reference_def example_request_def example_binding_def)
  have authority: "lock_authority(current_lock_view regulation_recorded 2)=example_context"
    using regulation_recorded_current_context by blast
  have receiver: "core_regulatory regulation_recorded=
    \<lparr>receiver_snapshot=example_snapshot ACTIVE,receiver_applied={}\<rparr>"
    by (simp add: regulation_recorded_shape regulation_root_ready_core_fields)
  show ?thesis
    by (simp add: regulation_case.invoke_regulatory_def at_epoch reference authority receiver
        combined_regulatory_receiver_really_executes_sync)
qed

lemma regulation_frozen_shape:
  "regulation_frozen=regulation_recorded\<lparr>core_regulatory:=
    \<lparr>receiver_snapshot=example_snapshot FROZEN,receiver_applied={(0,20)}\<rparr>,core_epoch:=9\<rparr>"
proof -
  have at_epoch: "core_epoch regulation_recorded=8"
    by (simp add: regulation_recorded_shape)
  show ?thesis
    by (simp add: regulation_frozen_def regulation_case.finality_step_def actual_child_freeze_succeeds at_epoch)
qed

definition regulation_published :: finality_core where
  "regulation_published=regulation_case.finality_step(Publish_Primary(0,20))regulation_frozen"

lemma regulation_published_shape:
  "regulation_published=regulation_frozen\<lparr>core_published:={(0,20),(0,17)},core_epoch:=10\<rparr>"
  by (simp add: regulation_published_def regulation_case.finality_step_def regulation_case.publish_primary_def
      regulation_frozen_shape regulation_recorded_shape regulation_root_ready_core_fields
      regulation_freeze_record_def terminal_effect_completed_def example_binding_def Let_def)

theorem actual_freeze_preserves_the_earlier_financial_effects:
  "transfer_projection(core_parent regulation_published)=transfer_projection(core_parent regulation_root_ready) \<and>
    get_reg_state(receiver_snapshot(core_regulatory regulation_published))0 20=Some FROZEN \<and>
    get_reg_state(receiver_snapshot(core_regulatory regulation_published))2 20=Some FROZEN"
  by (simp add: regulation_published_shape regulation_frozen_shape regulation_recorded_shape
      example_snapshot_def get_reg_state_def get_asset_state_def)

section \<open>Ordinary and Authorized Enforcement Consumers\<close>

definition regulation_spend_request :: "message_operation \<Rightarrow> execution_request" where
  "regulation_spend_request operation=regulation_money_request\<lparr>
    request_binding:=descendant_binding regulation_money_binding 4 1 operation\<rparr>"

definition regulation_ordinary_intent :: protocol_intent where
  "regulation_ordinary_intent=Descendant_Intent(regulation_spend_request Ordinary_Transfer_Effect)
    regulation_money_binding 3 4 1"

definition regulation_enforcement_intent :: protocol_intent where
  "regulation_enforcement_intent=Descendant_Intent
    (regulation_spend_request(Enforcement_Transfer_Effect Legal_Recover))regulation_money_binding 3 4 1"

lemmas regulation_spend_definitions = regulation_spend_request_def regulation_ordinary_intent_def
  regulation_enforcement_intent_def execute_descendant_def descendant_binding_def metadata_permission_def
  current_use_allowed_def ordinary_transfer_allowed_def transfer_allowed_def holder_account_def
  record_observation_def commit_reservation_event_def get_reg_state_def get_asset_state_def current_lock_view_def

lemma regulation_published_current_context:
  "current_lock_view regulation_published endpoint=
    (regulation_context endpoint)\<lparr>lock_metadata:=example_snapshot FROZEN\<rparr>"
  by (simp add: regulation_published_shape regulation_frozen_shape regulation_recorded_shape
      regulation_root_ready_core_fields current_lock_view_def regulation_context_def)

theorem ordinary_descendant_is_rejected_after_actual_freeze:
  "snd(regulation_case.invoke_protocol 2 10 0 regulation_ordinary_intent regulation_published)=
    Protocol_Response Request_Rejected"
  by (simp add: regulation_case.invoke_protocol_def regulation_published_current_context
      regulation_published_shape regulation_frozen_shape regulation_recorded_shape regulation_root_ready_core_fields
      regulation_root_ready_financial_state regulation_root_record_def record_reference_def
      lift_protocol_result_def regulation_spend_definitions regulation_payload_definitions example_snapshot_def Let_def)

definition regulation_denied :: finality_core where
  "regulation_denied=regulation_case.finality_step(Invoke_Protocol 2 10 0 regulation_ordinary_intent)regulation_published"

lemma regulation_denied_state:
  "machine_state(core_parent regulation_denied)=machine_state(core_parent regulation_root_ready) \<and>
    core_epoch regulation_denied=11 \<and>
    core_contexts regulation_denied=regulation_context \<and>
    core_records regulation_denied=core_records regulation_published \<and>
    core_published regulation_denied=core_published regulation_published \<and>
    core_regulatory regulation_denied=core_regulatory regulation_published"
  by (simp add: regulation_denied_def regulation_case.finality_step_def regulation_case.invoke_protocol_def
      regulation_published_current_context regulation_published_shape regulation_frozen_shape regulation_recorded_shape
      regulation_root_ready_core_fields regulation_root_ready_financial_state regulation_root_record_def record_reference_def
      lift_protocol_result_def regulation_spend_definitions regulation_payload_definitions example_snapshot_def Let_def)

lemma regulation_denied_current_context:
  "current_lock_view regulation_denied endpoint=
    (regulation_context endpoint)\<lparr>lock_metadata:=example_snapshot FROZEN\<rparr>"
  by (simp add: current_lock_view_def regulation_denied_state regulation_published_shape
      regulation_frozen_shape regulation_context_def)

theorem authorized_enforcement_descendant_succeeds_after_actual_freeze:
  "snd(regulation_case.invoke_protocol 2 11 0 regulation_enforcement_intent regulation_denied)=
    Protocol_Response Descendant_Executed"
  by (simp add: regulation_case.invoke_protocol_def regulation_denied_state regulation_denied_current_context
      regulation_published_shape regulation_frozen_shape regulation_recorded_shape regulation_root_ready_core_fields
      regulation_root_ready_financial_state regulation_root_record_def record_reference_def lift_protocol_result_def
      regulation_spend_definitions regulation_payload_definitions example_snapshot_def Let_def)

definition regulation_enforced :: finality_core where
  "regulation_enforced=regulation_case.finality_step
    (Invoke_Protocol 2 11 0 regulation_enforcement_intent)regulation_denied"

theorem enforcement_changes_only_lawful_funding_and_keeps_freeze:
  "destination_units(machine_state(core_parent regulation_enforced))(2,20,3)=4 \<and>
    destination_units(machine_state(core_parent regulation_enforced))(2,20,4)=1 \<and>
    funded_units(machine_state(core_parent regulation_enforced))((0,17),(2,20,3))=4 \<and>
    funded_units(machine_state(core_parent regulation_enforced))((0,17),(2,20,4))=1 \<and>
    source_effects(machine_state(core_parent regulation_enforced))=[regulation_money_binding] \<and>
    credit_history(received_messages(machine_state(core_parent regulation_enforced)))=[regulation_money_binding] \<and>
    length(lawful_descendants(machine_state(core_parent regulation_enforced)))=1 \<and>
    core_regulatory regulation_enforced=core_regulatory regulation_published \<and>
    core_epoch regulation_enforced=12"
  by (simp add: regulation_enforced_def regulation_case.finality_step_def regulation_case.invoke_protocol_def
      regulation_denied_state regulation_denied_current_context regulation_published_shape regulation_frozen_shape
      regulation_recorded_shape regulation_root_ready_core_fields regulation_root_ready_financial_state
      regulation_root_record_def record_reference_def lift_protocol_result_def regulation_spend_definitions
      regulation_payload_definitions example_snapshot_def record_credit_def
      empty_message_state_def initial_reservation_state_def Let_def)

lemma regulation_enforced_control_state:
  "reservation_at(machine_state(core_parent regulation_enforced))(0,17)=Some regulation_pending_reservation \<and>
    asset_owner(machine_state(core_parent regulation_enforced))20=Some(0,17) \<and>
    asset_version(machine_state(core_parent regulation_enforced))20=0 \<and>
    reservation_clock(machine_state(core_parent regulation_enforced))=0 \<and>
    core_contexts regulation_enforced=regulation_context \<and>
    core_records regulation_enforced=core_records regulation_published"
  by (simp add: regulation_enforced_def regulation_case.finality_step_def regulation_case.invoke_protocol_def
      regulation_denied_state regulation_denied_current_context regulation_published_shape regulation_frozen_shape
      regulation_recorded_shape regulation_root_ready_core_fields regulation_root_ready_financial_state
      regulation_root_record_def record_reference_def lift_protocol_result_def regulation_spend_definitions
      regulation_payload_definitions example_snapshot_def initial_reservation_state_def Let_def)

theorem actual_reconciliation_succeeds_after_freeze_and_enforcement:
  "snd(regulation_case.invoke_protocol 0 12 0(Reconcile_Intent regulation_money_request 0 [])regulation_enforced)=
    Protocol_Response Reservation_Released"
  by (simp add: regulation_case.invoke_protocol_def regulation_case.reconcile_recorded_credit_def
      regulation_enforced_control_state enforcement_changes_only_lawful_funding_and_keeps_freeze
      regulation_published_shape regulation_frozen_shape regulation_recorded_shape regulation_root_ready_core_fields
      current_lock_view_def record_reference_def exact_record_reference_def lift_protocol_result_def
      owns_recorded_reservation_def current_use_allowed_def phase_at_def vector_lookup_def
      regulation_payload_definitions record_observation_def Let_def)

definition regulation_settled :: finality_core where
  "regulation_settled=regulation_case.finality_step
    (Invoke_Protocol 0 12 0(Reconcile_Intent regulation_money_request 0 []))regulation_enforced"

theorem actual_reconciliation_preserves_financial_lineage_and_freeze:
  "transfer_projection(core_parent regulation_settled)=transfer_projection(core_parent regulation_enforced) \<and>
    core_regulatory regulation_settled=core_regulatory regulation_enforced"
  by (simp add: regulation_settled_def regulation_case.finality_step_def regulation_case.invoke_protocol_def
      reject_protocol_intent_def regulation_case.reconcile_recorded_credit_def transfer_projection_def lift_protocol_result_def
      record_observation_def commit_reservation_event_def finish_reservation_def set_phase_def Let_def
      split: option.splits)

theorem full_regulatory_scenario_is_an_actual_child_execution:
  "regulation_settled=regulation_case.run_finality
    (regulation_credit_trace@[
      Record_Terminal(example_certificate 20),Invoke_Regulatory 2 8 0(example_request 20),
      Publish_Primary(0,20),Invoke_Protocol 2 10 0 regulation_ordinary_intent,
      Invoke_Protocol 2 11 0 regulation_enforcement_intent,
      Invoke_Protocol 0 12 0(Reconcile_Intent regulation_money_request 0 [])])regulation_genesis"
  by (simp add: regulation_settled_def regulation_enforced_def regulation_denied_def
      regulation_published_def regulation_frozen_def regulation_recorded_def regulation_root_ready_def
      regulation_case.finality_run_append)

theorem full_regulatory_scenario_supplies_parent_and_cdsp_contracts:
  "regulation_case.reservation_contract regulation_balances(core_parent regulation_settled) \<and>
    valid_state(receiver_snapshot(core_regulatory regulation_settled))"
  unfolding full_regulatory_scenario_is_an_actual_child_execution regulation_genesis_def
  by (intro conjI)
     (rule regulation_case.finality_supplies_actual_reservation_contract,
      rule regulation_case.generated_finality_has_cdsp, rule example_snapshot_valid)

section \<open>Removing the Terminal Reference Changes Real Regulatory Metadata\<close>

definition regulatory_apply_without_terminal_record :: "nat \<Rightarrow> nat \<Rightarrow> execution_request \<Rightarrow>
  finality_core \<Rightarrow> finality_core \<times> finality_reply" where
  "regulatory_apply_without_terminal_record endpoint epoch r s=
    (if epoch\<noteq>core_epoch s then (s,Finality_Rejected)
     else case regulation_case.apply_regulatory_message(lock_authority(current_lock_view s endpoint))r(core_regulatory s) of
       None \<Rightarrow> (s,Finality_Rejected)
     | Some receiver \<Rightarrow> (s\<lparr>core_regulatory:=receiver\<rparr>,Regulatory_Applied))"

theorem terminal_record_removal_applies_freeze_without_its_protocol_record:
  "snd(regulation_case.invoke_regulatory 2 7 0(example_request 20)regulation_root_ready)=Finality_Rejected \<and>
    snd(regulatory_apply_without_terminal_record 2 7(example_request 20)regulation_root_ready)=Regulatory_Applied \<and>
    get_reg_state(receiver_snapshot(core_regulatory(fst(regulatory_apply_without_terminal_record
      2 7(example_request 20)regulation_root_ready))))2 20=Some FROZEN \<and>
    core_records(fst(regulatory_apply_without_terminal_record
      2 7(example_request 20)regulation_root_ready))(0,20)=None"
proof -
  have at_epoch: "core_epoch regulation_root_ready=7"
    using regulation_root_ready_core_fields by blast
  have no_slot: "core_records regulation_root_ready(0,20)=None"
    by (simp add: regulation_root_ready_core_fields)
  have no_reference: "\<not>exact_record_reference regulation_root_ready 0
    (request_binding(example_request 20))Confirmed_Decision(request_certificate(example_request 20))"
    by (simp add: exact_record_reference_def record_reference_def example_request_def example_binding_def no_slot)
  have baseline: "snd(regulation_case.invoke_regulatory 2 7 0(example_request 20)regulation_root_ready)=Finality_Rejected"
    by (simp add: regulation_case.invoke_regulatory_def no_reference)
  have authority: "lock_authority(current_lock_view regulation_root_ready 2)=example_context"
    by (simp add: current_lock_view_def regulation_root_ready_core_fields regulation_context_def example_context_def)
  have receiver: "core_regulatory regulation_root_ready=
    \<lparr>receiver_snapshot=example_snapshot ACTIVE,receiver_applied={}\<rparr>"
    using regulation_root_ready_core_fields by blast
  have mutation_result: "regulatory_apply_without_terminal_record 2 7(example_request 20)regulation_root_ready =
    (regulation_root_ready\<lparr>core_regulatory:=
      \<lparr>receiver_snapshot=example_snapshot FROZEN,receiver_applied={(0,20)}\<rparr>\<rparr>,Regulatory_Applied)"
    by (simp add: regulatory_apply_without_terminal_record_def at_epoch authority receiver
        combined_regulatory_receiver_really_executes_sync)
  show ?thesis
    by (simp add: baseline mutation_result no_slot example_snapshot_def get_reg_state_def get_asset_state_def)
qed

text \<open>Every scenario state above is defined by actual child operations.
  The initial metadata is Active; Frozen metadata is produced only by the
  existing regulatory receiver's completed synchronization. Ordinary spending
  and authorized recovery then use that actual current metadata. Source
  reconciliation retains the existing credit, onward funding and regulatory
  effect. The monetary allocation and regulatory holding support remain
  different state components.

  The mutation starts from the generated monetary-primary state. It retains
  the current epoch and existing certificate, permission and synchronization
  checks, but omits the terminal-record reference. Its actual Freeze effect
  lacks the required protocol record. This is a provenance failure, not a
  claim that the supplied regulatory source fact itself is false.\<close>

end
