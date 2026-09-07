(* SPDX-License-Identifier: BSD-3-Clause *)
theory Source_Finality_Link
  imports Controlled_Source_Outcomes Finality_Calls
    "Preemptive_Lock_Correctness.Reservation_Examples"
begin

section \<open>Source-Issued Receipts and Their Consumer\<close>

text \<open>This is a monetary source profile. Receipt issuance reads a generated
  controlled-source state; receipt verification reads only the resulting
  immutable issuance log. It does not query source truth. The log is a logical
  authenticated-source API, not a cryptographic signature implementation.
  Its physical authenticity, access control and persistence are UNVERIFIED.
  The concrete relay roster below witnesses a nonzero fault bound; it does
  not establish a distributed terminal agreement protocol.

  The existing reservation examples supply only payloads, current contexts
  and an actual Acquire/Dispatch/Source execution. Their example truth and
  verifier predicates are not used to authenticate the receipts here.
  Regulatory-source production remains outside this monetary profile.\<close>

definition source_receipt_slot_available :: "source_certificate \<Rightarrow>
  source_certificate list \<Rightarrow> bool" where
  "source_receipt_slot_available cert issued \<longleftrightarrow>
    (\<forall>old\<in>set issued. certificate_signature old=certificate_signature cert \<longrightarrow> old=cert)"

definition issue_source_receipt :: "controlled_source_state \<Rightarrow> source_certificate
  \<Rightarrow> source_certificate list \<Rightarrow> source_certificate list" where
  "issue_source_receipt source cert issued =
    (if controlled_source_fact source
        (binding_key (statement_binding (certificate_statement cert)))=
        Some (certificate_statement cert) \<and> source_receipt_slot_available cert issued
     then if cert\<in>set issued then issued else issued@[cert]
     else issued)"

fun run_source_receipts :: "controlled_source_state \<Rightarrow> source_certificate list
  \<Rightarrow> source_certificate list \<Rightarrow> source_certificate list" where
  "run_source_receipts source [] issued=issued"
| "run_source_receipts source (cert#rest) issued=
    run_source_receipts source rest (issue_source_receipt source cert issued)"

definition generated_source_receipts :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  controlled_source_command list \<Rightarrow> source_certificate list \<Rightarrow> source_certificate list"
  where
  "generated_source_receipts balances commands candidates=
    run_source_receipts (run_controlled_source commands (initial_controlled_source balances))
      candidates []"

definition receipt_log_sound :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  controlled_source_command list \<Rightarrow> source_certificate list \<Rightarrow> bool" where
  "receipt_log_sound balances commands issued \<longleftrightarrow>
    (\<forall>cert\<in>set issued.
      controlled_produced_fact balances commands (certificate_statement cert))"

lemma receipt_issuance_preserves_soundness:
  assumes "receipt_log_sound balances commands issued"
  shows "receipt_log_sound balances commands
    (issue_source_receipt (run_controlled_source commands (initial_controlled_source balances))
      cert issued)"
  using assms controlled_current_fact_is_produced
  by (auto simp: issue_source_receipt_def receipt_log_sound_def)

lemma receipt_run_preserves_soundness:
  "receipt_log_sound balances commands issued \<Longrightarrow>
    receipt_log_sound balances commands
      (run_source_receipts
        (run_controlled_source commands (initial_controlled_source balances)) candidates issued)"
  by (induction candidates arbitrary:issued)
     (auto intro: receipt_issuance_preserves_soundness)

theorem every_generated_receipt_has_a_produced_source_fact:
  "receipt_log_sound balances commands (generated_source_receipts balances commands candidates)"
  unfolding generated_source_receipts_def
  by (rule receipt_run_preserves_soundness) (simp add: receipt_log_sound_def)

definition source_receipt_verifies :: "source_certificate list \<Rightarrow> source_certificate \<Rightarrow>
  bool" where
  "source_receipt_verifies issued cert \<longleftrightarrow> cert\<in>set issued"

definition source_receipt_signed :: "source_certificate list \<Rightarrow> nat \<Rightarrow> nat
  \<Rightarrow> source_statement \<Rightarrow> bool" where
  "source_receipt_signed issued signer epoch statement \<longleftrightarrow>
    signer=0 \<or> (\<exists>cert\<in>set issued. signer\<in>set (certificate_signers cert) \<and>
      certificate_epoch cert=epoch \<and> certificate_statement cert=statement)"

theorem source_receipts_interpret_source_attestation:
  "source_attestation example_roster example_faulty example_bound example_threshold
    (source_receipt_verifies (generated_source_receipts balances commands candidates))
    (source_receipt_signed (generated_source_receipts balances commands candidates))
    (controlled_produced_fact balances commands)
    (controlled_stable_source balances commands)"
proof unfold_locales
  fix epoch
  show "finite (example_roster epoch)" by (simp add: example_roster_def)
  show "example_faulty epoch\<subseteq>example_roster epoch"
    by (simp add: example_faulty_def example_roster_def)
  show "card (example_faulty epoch)\<le>example_bound epoch"
    by (simp add: example_faulty_def example_bound_def)
  show "example_bound epoch<example_threshold epoch"
    by (simp add: example_bound_def example_threshold_def)
next
  fix cert signer
  assume "source_receipt_verifies (generated_source_receipts balances commands candidates) cert"
    "signer\<in>set (certificate_signers cert)"
  then show "source_receipt_signed (generated_source_receipts balances commands candidates)
    signer (certificate_epoch cert) (certificate_statement cert)"
    by (auto simp: source_receipt_verifies_def source_receipt_signed_def)
next
  fix signer epoch statement
  assume member: "signer\<in>example_roster epoch"
    and honest: "signer\<notin>example_faulty epoch"
    and signed: "source_receipt_signed (generated_source_receipts balances commands candidates)
      signer epoch statement"
  have sound: "receipt_log_sound balances commands
    (generated_source_receipts balances commands candidates)"
    by (rule every_generated_receipt_has_a_produced_source_fact)
  show "controlled_produced_fact balances commands statement"
    using honest signed sound
    unfolding example_faulty_def source_receipt_signed_def receipt_log_sound_def by auto
next
  fix statement
  assume fact: "controlled_produced_fact balances commands statement"
    and terminal: "statement_status statement\<noteq>Observed"
  show "controlled_stable_source balances commands
    (binding_key (statement_binding statement))=Some statement"
    by (rule controlled_producer_supplies_stable_fact[where balances=balances and commands=commands])
       (rule fact)
qed

theorem a_conflicting_signature_slot_is_not_reissued:
  assumes "old\<in>set issued" "certificate_signature old=certificate_signature cert" "old\<noteq>cert"
  shows "issue_source_receipt source cert issued=issued"
  using assms by (auto simp: issue_source_receipt_def source_receipt_slot_available_def)

theorem absent_source_fact_produces_no_receipt:
  assumes "controlled_source_fact source
    (binding_key (statement_binding (certificate_statement cert)))\<noteq>Some (certificate_statement cert)"
  shows "issue_source_receipt source cert issued=issued"
  using assms by (simp add: issue_source_receipt_def)

section \<open>One Actual Source History and Two Terminal Consumers\<close>

definition linked_source_commands :: "controlled_source_command list" where
  "linked_source_commands=[
    Controlled_Boundary (Boundary_Apply (sample_binding 17)),
    Controlled_Finalize (sample_binding 17),
    Controlled_Boundary (Boundary_Apply (sample_binding 22)),
    Controlled_Reverse (sample_binding 22)]"

definition linked_source_state :: controlled_source_state where
  "linked_source_state=
    run_controlled_source linked_source_commands (initial_controlled_source sample_balances)"

definition linked_certificate :: "nat \<Rightarrow> source_certificate" where
  "linked_certificate event=
    \<lparr>certificate_statement=sample_statement event,certificate_epoch=8,
      certificate_signers=[0,1],certificate_signature=event\<rparr>"

definition linked_receipts :: "source_certificate list" where
  "linked_receipts=generated_source_receipts sample_balances linked_source_commands
    [linked_certificate 17,linked_certificate 22]"

interpretation linked: source_attestation example_roster example_faulty example_bound example_threshold
  "source_receipt_verifies linked_receipts" "source_receipt_signed linked_receipts"
  "controlled_produced_fact sample_balances linked_source_commands"
  "controlled_stable_source sample_balances linked_source_commands"
  unfolding linked_receipts_def by (rule source_receipts_interpret_source_attestation)

lemmas linked_source_data = linked_source_commands_def linked_source_state_def
  initial_controlled_source_def initial_source_boundary_def controlled_boundary_def
  controlled_finalize_def controlled_reverse_def controlled_record_finalized_def
  controlled_record_reversed_def controlled_source_fact_def boundary_apply_def
  boundary_record_effect_def boundary_has_effect_def boundary_valid_binding_def
  sample_binding_def example_binding_def sample_balances_def source_account_of_def

theorem linked_source_really_produces_both_facts:
  "controlled_source_fact linked_source_state (0,17)=Some (sample_statement 17) \<and>
    controlled_source_fact linked_source_state (0,22)=Some (sample_statement 22)"
  by (simp add: linked_source_data sample_statement_def Let_def)

lemma linked_source_financial_projection:
  "boundary_effects (controlled_endpoint linked_source_state)=[sample_binding 17,sample_binding 22] \<and>
    controlled_returns linked_source_state=[sample_binding 22] \<and>
    boundary_units (controlled_endpoint linked_source_state) (0,22)=5"
  by (simp add: linked_source_data Let_def)

theorem linked_receipts_are_actually_issued:
  "linked_receipts=[linked_certificate 17,linked_certificate 22]"
  by (simp add: linked_receipts_def generated_source_receipts_def
    issue_source_receipt_def source_receipt_slot_available_def linked_certificate_def
    linked_source_data sample_statement_def Let_def)

theorem linked_certificates_pass_the_parent_checker:
  "event\<in>{17,22} \<Longrightarrow> linked.certificate_ok (linked_certificate event)"
  unfolding linked.certificate_ok_def
  by (auto simp: source_receipt_verifies_def
    linked_receipts_are_actually_issued linked_certificate_def example_roster_def example_threshold_def)

definition linked_parent_commands :: "reservation_action list" where
  "linked_parent_commands=sample_prefix 17@sample_prefix 22"

definition linked_parent_pending :: reservation_machine where
  "linked_parent_pending=
    linked.run_reservations sample_balances linked_parent_commands sample_initial"

theorem linked_parent_is_an_actual_protocol_execution:
  "linked.reservation_contract sample_balances linked_parent_pending"
  unfolding linked_parent_pending_def sample_initial_def
  by (rule linked.all_finite_executions_supply_the_reservation_contract)

theorem linked_parent_really_records_both_source_effects:
  "source_effects (machine_state linked_parent_pending)=[sample_binding 17,sample_binding 22]"
  by (simp add: linked_parent_pending_def linked_parent_commands_def sample_data_defs
    linked.run_reservations.simps linked.reservation_step.simps
    acquire_reservation_def dispatch_source_def execute_source_effect_def
    record_observation_def commit_reservation_event_def Let_def)

definition linked_child_source_commands :: "finality_operation list" where
  "linked_child_source_commands=[
    Invoke_Protocol 0 0 0 (Reserve_Intent (sample_request 17) [] 10),
    Invoke_Protocol 0 1 0 (Dispatch_Intent (sample_request 17) 0 []),
    Invoke_Protocol 0 2 0 (Source_Intent (sample_request 17) 0 []),
    Invoke_Protocol 0 3 0 (Reserve_Intent (sample_request 22) [] 10),
    Invoke_Protocol 0 4 0 (Dispatch_Intent (sample_request 22) 0 []),
    Invoke_Protocol 0 5 0 (Source_Intent (sample_request 22) 0 [])]"

definition linked_genesis_core :: finality_core where
  "linked_genesis_core=initial_finality_core sample_balances (sample_metadata ACTIVE)
    (\<lambda>_.sample_source_context ACTIVE)"

definition linked_initial_core :: finality_core where
  "linked_initial_core=linked.run_finality linked_child_source_commands linked_genesis_core"

lemma source_link_current_view_updates [simp]:
  "current_lock_view (core\<lparr>core_parent:=parent\<rparr>) endpoint=current_lock_view core endpoint"
  "current_lock_view (core\<lparr>core_records:=records\<rparr>) endpoint=current_lock_view core endpoint"
  "current_lock_view (core\<lparr>core_epoch:=epoch\<rparr>) endpoint=current_lock_view core endpoint"
  by (simp_all add: current_lock_view_def)

lemma source_link_zero_versions:
  "vector_lookup []=(\<lambda>_.0)"
  by (rule ext) (simp add: vector_lookup_def)

theorem linked_child_source_trace_has_the_actual_parent_projection:
  "core_parent linked_initial_core=linked_parent_pending \<and>
    core_epoch linked_initial_core=6 \<and>
    core_records linked_initial_core=(\<lambda>_.None) \<and>
    current_lock_view linked_initial_core 0=sample_source_context ACTIVE"
  by (simp add: linked_initial_core_def linked_child_source_commands_def linked_genesis_core_def
    linked_parent_pending_def linked_parent_commands_def sample_prefix_def sample_initial_def
    linked.run_finality.simps linked.finality_step_def linked.core_result.simps linked.invoke_protocol_def
    linked.intent_result.simps linked.run_reservations.simps linked.reservation_step.simps
    initial_finality_core_def current_lock_view_def lift_protocol_result_def source_link_zero_versions
    sample_source_context_def sample_context_def Let_def)

definition linked_confirm_core :: finality_core where
  "linked_confirm_core=fst (linked.execute_finality_client
    (Client_Terminal (linked_certificate 17)) linked_initial_core)"

definition linked_terminal_core :: finality_core where
  "linked_terminal_core=fst (linked.execute_finality_client
    (Client_Terminal (linked_certificate 22)) linked_confirm_core)"

theorem linked_confirm_uses_the_actual_terminal_consumer:
  "linked.record_terminal (linked_certificate 17) linked_initial_core=
    (linked_initial_core\<lparr>core_records:=(core_records linked_initial_core)((0,17):=Some
      \<lparr>terminal_binding=sample_binding 17,terminal_kind=Confirmed_Decision,
        terminal_evidence=[linked_certificate 17]\<rparr>)\<rparr>,Terminal_Recorded)"
  using linked_certificates_pass_the_parent_checker[of 17]
  by (simp add: linked.record_terminal_def source_origin_present_def
    linked_child_source_trace_has_the_actual_parent_projection
    linked_parent_really_records_both_source_effects
    linked_certificate_def sample_statement_def sample_binding_def example_binding_def Let_def)

lemma linked_confirm_core_projections:
  "core_parent linked_confirm_core=linked_parent_pending \<and>
    core_records linked_confirm_core (0,22)=None \<and>
    core_epoch linked_confirm_core=7 \<and>
    current_lock_view linked_confirm_core 0=sample_source_context ACTIVE"
  by (simp add: linked_confirm_core_def linked.execute_finality_client_def linked.finality_step_def
    linked.core_result.simps
    linked_confirm_uses_the_actual_terminal_consumer
    linked_child_source_trace_has_the_actual_parent_projection)

theorem linked_reverse_uses_the_actual_terminal_consumer:
  "snd (linked.record_terminal (linked_certificate 22) linked_confirm_core)=Terminal_Recorded \<and>
    core_records linked_terminal_core (0,22)=Some
      \<lparr>terminal_binding=sample_binding 22,terminal_kind=Reversed_Decision,
        terminal_evidence=[linked_certificate 22]\<rparr>"
  using linked_certificates_pass_the_parent_checker[of 22]
  by (simp add: linked_terminal_core_def linked.execute_finality_client_def linked.finality_step_def
    linked.core_result.simps
    linked_confirm_core_projections
    linked.record_terminal_def source_origin_present_def linked_parent_really_records_both_source_effects
    linked_certificate_def sample_statement_def sample_binding_def example_binding_def Let_def)

lemma linked_terminal_core_projections:
  "core_parent linked_terminal_core=linked_parent_pending \<and>
    core_epoch linked_terminal_core=8 \<and>
    current_lock_view linked_terminal_core 0=sample_source_context ACTIVE"
  using linked_certificates_pass_the_parent_checker[of 22]
  by (simp add: linked_terminal_core_def linked.execute_finality_client_def linked.finality_step_def
    linked.core_result.simps
    linked.record_terminal_def source_origin_present_def linked_confirm_core_projections
    linked_parent_really_records_both_source_effects
    linked_certificate_def sample_statement_def sample_binding_def example_binding_def
    Let_def)

theorem linked_terminal_core_is_reached_by_actual_child_operations:
  "linked_terminal_core=linked.run_finality
    (linked_child_source_commands@[Record_Terminal (linked_certificate 17),
      Record_Terminal (linked_certificate 22)]) linked_genesis_core"
  by (simp add: linked_terminal_core_def linked_confirm_core_def linked_initial_core_def
    linked.execute_finality_client_def linked.finality_run_append)

theorem lost_local_origin_cannot_record_a_terminal_decision:
  assumes "binding_operation (statement_binding (certificate_statement cert))=Destination_Credit"
    "statement_binding (certificate_statement cert)\<notin>set
      (source_effects (machine_state (core_parent core)))"
  shows "linked.record_terminal cert core=(core,Finality_Rejected)"
  using assms by (simp add: linked.record_terminal_def source_origin_present_def Let_def)

section \<open>One Restoration and Two Accounting Views\<close>

definition source_mirror_provenance :: "controlled_source_state \<Rightarrow> reservation_machine \<Rightarrow>
  bool" where
  "source_mirror_provenance source parent \<longleftrightarrow>
    set (source_effects (machine_state parent))\<subseteq>
      set (boundary_effects (controlled_endpoint source)) \<and>
    set (returned_bindings (machine_journal parent))\<subseteq>set (controlled_returns source)"

definition source_debit_gap :: "controlled_source_state \<Rightarrow> reservation_machine \<Rightarrow>
  source_account \<Rightarrow> int" where
  "source_debit_gap source parent account=
    int (boundary_debited account (controlled_endpoint source))-source_debits (machine_state parent) account"

definition source_return_gap :: "controlled_source_state \<Rightarrow> reservation_machine \<Rightarrow>
  source_account \<Rightarrow> int" where
  "source_return_gap source parent account=
    int (controlled_returned account source)-
      sum_list (map (returned_amount account) (machine_journal parent))"

theorem source_and_parent_are_two_views_of_one_allocation:
  assumes source: "controlled_source_invariant balances source"
    and parent: "financial_history_agreement balances parent"
  shows "int (boundary_units (controlled_endpoint source) account)=
    int (source_units (machine_state parent) account)-
      source_debit_gap source parent account+source_return_gap source parent account"
proof -
  have remote_nat: "boundary_units (controlled_endpoint source) account+
    boundary_debited account (controlled_endpoint source)=
    balances account+controlled_returned account source"
    by (rule controlled_net_resource_equation[OF source])
  have remote_int: "int (boundary_units (controlled_endpoint source) account)+
    int (boundary_debited account (controlled_endpoint source))=
    int (balances account)+int (controlled_returned account source)"
    using arg_cong[OF remote_nat, where f="\<lambda>n. int n"] by simp
  have local: "int (source_units (machine_state parent) account)+
    source_debits (machine_state parent) account=
    int (balances account)+sum_list (map (returned_amount account) (machine_journal parent))"
    using parent unfolding financial_history_agreement_def by blast
  show ?thesis using remote_int local
    unfolding source_debit_gap_def source_return_gap_def by linarith
qed

theorem synchronized_views_have_equal_available_units:
  assumes "controlled_source_invariant balances source"
    "financial_history_agreement balances parent"
    "source_debit_gap source parent account=0" "source_return_gap source parent account=0"
  shows "boundary_units (controlled_endpoint source) account=source_units (machine_state parent) account"
  using source_and_parent_are_two_views_of_one_allocation[where account=account, OF assms(1,2)]
    assms(3,4) by simp

context source_attestation
begin

definition mirror_source_return :: "controlled_source_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
  \<Rightarrow> execution_request \<Rightarrow> nat \<Rightarrow> version_vector \<Rightarrow> finality_core
  \<Rightarrow> controlled_source_state \<times> (finality_core \<times> finality_reply)" where
  "mirror_source_return source endpoint epoch index r generation versions core=
    (source,if controlled_source_fact source (binding_key (request_binding r))=
        Some \<lparr>statement_binding=request_binding r,statement_status=Reversed\<rparr> \<and>
        epoch=core_epoch core
      then execute_finality_client
        (Client_Protocol endpoint index (Return_Intent r generation versions)) core
      else (core,Finality_Rejected))"

theorem mirror_return_never_executes_a_second_source_restoration:
  "fst (mirror_source_return source endpoint epoch index r generation versions core)=source"
  by (simp add: mirror_source_return_def)

theorem successful_mirror_return_consumes_the_source_outcome:
  assumes "snd (snd (mirror_source_return source endpoint epoch index r generation versions core))=
    Protocol_Response Reservation_Released"
  shows "controlled_source_fact source (binding_key (request_binding r))=
    Some \<lparr>statement_binding=request_binding r,statement_status=Reversed\<rparr>"
  using assms by (auto simp: mirror_source_return_def split: if_splits)

theorem mirror_return_preserves_the_parent_contract:
  assumes "reservation_contract balances (core_parent core)"
  shows "reservation_contract balances (core_parent
    (fst (snd (mirror_source_return source endpoint epoch index r generation versions core))))"
  using assms finality_step_preserves_parent_contract
  by (auto simp: mirror_source_return_def execute_finality_client_def)

end

definition linked_return_request :: execution_request where
  "linked_return_request=(sample_request 22)\<lparr>request_certificate:=linked_certificate 22\<rparr>"

lemma linked_return_request_projection:
  "request_binding linked_return_request=sample_binding 22 \<and>
    request_certificate linked_return_request=linked_certificate 22 \<and>
    binding_key (request_binding linked_return_request)=(0,22) \<and>
    source_account_of (request_binding linked_return_request)=(0,22) \<and>
    binding_amount (request_binding linked_return_request)=5"
  by (simp add: linked_return_request_def sample_request_def sample_binding_def
    example_binding_def source_account_of_def)

lemma linked_parent_pending_return_guards:
  "owns_recorded_reservation (sample_source_context ACTIVE) linked_return_request 0
      (vector_lookup []) (machine_state linked_parent_pending) \<and>
    phase_at (machine_state linked_parent_pending) (0,22)=Some Source_Pending \<and>
    source_units (machine_state linked_parent_pending) (0,22)=0 \<and>
    returned_bindings (machine_journal linked_parent_pending)=[]"
  by (simp add: linked_parent_pending_def linked_parent_commands_def linked_return_request_def
    linked_certificate_def sample_data_defs vector_lookup_def
    linked.run_reservations.simps linked.reservation_step.simps
    acquire_reservation_def dispatch_source_def execute_source_effect_def
    record_observation_def commit_reservation_event_def returned_bindings_def Let_def)

lemma source_link_certificate_event_frames:
  "owns_recorded_reservation c r generation versions
      (machine_state (commit_reservation_event (Certificate_Event cert) parent))=
    owns_recorded_reservation c r generation versions (machine_state parent)"
  "phase_at (machine_state (commit_reservation_event (Certificate_Event cert) parent)) key=
    phase_at (machine_state parent) key"
  "source_units (machine_state (commit_reservation_event (Certificate_Event cert) parent))=
    source_units (machine_state parent)"
  "source_effects (machine_state (commit_reservation_event (Certificate_Event cert) parent))=
    source_effects (machine_state parent)"
  "returned_bindings (machine_journal (commit_reservation_event (Certificate_Event cert) parent))=
    returned_bindings (machine_journal parent)"
  by (simp_all add: commit_reservation_event_def owns_recorded_reservation_def phase_at_def)

definition linked_published_reverse_core :: finality_core where
  "linked_published_reverse_core=fst (linked.execute_finality_client
    (Client_Protocol 0 0 (Certificate_Intent (linked_certificate 22))) linked_terminal_core)"

lemma linked_reverse_certificate_publication:
  "linked.publish_source_certificate (linked_certificate 22) linked_parent_pending=
    commit_reservation_event (Certificate_Event (linked_certificate 22)) linked_parent_pending"
  using linked_certificates_pass_the_parent_checker[of 22]
  by (simp add: linked.publish_source_certificate_def linked_certificate_def sample_statement_def
    linked_parent_really_records_both_source_effects Let_def)

lemma linked_published_reverse_core_projection:
  "core_parent linked_published_reverse_core=
      commit_reservation_event (Certificate_Event (linked_certificate 22)) linked_parent_pending \<and>
    core_epoch linked_published_reverse_core=9 \<and>
    current_lock_view linked_published_reverse_core 0=sample_source_context ACTIVE \<and>
    core_records linked_published_reverse_core (0,22)=Some
      \<lparr>terminal_binding=sample_binding 22,terminal_kind=Reversed_Decision,
        terminal_evidence=[linked_certificate 22]\<rparr>"
proof -
  note publication = linked_reverse_certificate_publication
    [unfolded linked_certificate_def sample_statement_def sample_binding_def example_binding_def]
  show ?thesis using publication
    by (simp add: linked_published_reverse_core_def linked.execute_finality_client_def
      linked.finality_step_def linked.core_result.simps linked.invoke_protocol_def linked.intent_result.simps
      linked_terminal_core_projections linked_reverse_uses_the_actual_terminal_consumer
      exact_record_reference_def record_reference_def
      linked_certificate_def sample_statement_def sample_binding_def example_binding_def Let_def)
qed

lemma linked_parent_release_has_exact_evidence:
  "linked.reversed_source_evidence (lock_authority (sample_source_context ACTIVE))
    linked_return_request (machine_state (core_parent linked_published_reverse_core))"
  using linked_certificates_pass_the_parent_checker[of 22]
  by (simp add: linked.reversed_source_evidence_def linked_return_request_projection
    linked_published_reverse_core_projection commit_reservation_event_def
    linked_certificate_def sample_statement_def sample_source_context_def
    sample_context_def example_context_def)

lemma source_link_issued_certificate_update_frames:
  "owns_recorded_reservation c r generation versions (state\<lparr>issued_certificates:=certificates\<rparr>)=
    owns_recorded_reservation c r generation versions state"
  "phase_at (state\<lparr>issued_certificates:=certificates\<rparr>) key=phase_at state key"
  "source_units (state\<lparr>issued_certificates:=certificates\<rparr>)=source_units state"
  "source_effects (state\<lparr>issued_certificates:=certificates\<rparr>)=source_effects state"
  by (simp_all add: owns_recorded_reservation_def phase_at_def)

lemma source_link_sample_binding_key:
  "binding_key (sample_binding event)=(0,event)"
  by (simp add: sample_binding_def example_binding_def)

lemma source_link_sample_source_account:
  "source_account_of (sample_binding event)=(0,if event=23 then 17 else event)"
  by (simp add: source_account_of_def sample_binding_def example_binding_def)

lemma source_link_sample_amount:
  "binding_amount (sample_binding event)=5"
  by (simp add: sample_binding_def example_binding_def)

lemmas source_link_sample_projections =
  source_link_sample_binding_key source_link_sample_source_account source_link_sample_amount

lemma linked_parent_release_succeeds:
  "snd (linked.release_to_source (sample_source_context ACTIVE) linked_return_request 0
    (vector_lookup []) (core_parent linked_published_reverse_core))=Reservation_Released"
  by (simp only: linked.evidence_release_exact_guard)
     (use linked_parent_pending_return_guards linked_parent_release_has_exact_evidence
        in \<open>simp add: linked_published_reverse_core_projection
          linked_return_request_projection source_link_certificate_event_frames
          source_link_issued_certificate_update_frames source_link_sample_binding_key\<close>)

lemma linked_parent_release_available_units:
  "source_units (machine_state (fst (linked.release_to_source (sample_source_context ACTIVE)
    linked_return_request 0 (vector_lookup []) (core_parent linked_published_reverse_core)))) (0,22)=5"
proof -
  have amount: "source_units (machine_state (fst (linked.release_to_source (sample_source_context ACTIVE)
      linked_return_request 0 (vector_lookup []) (core_parent linked_published_reverse_core))))
      (source_account_of (request_binding linked_return_request))=
    source_units (machine_state (core_parent linked_published_reverse_core))
      (source_account_of (request_binding linked_return_request))+
        binding_amount (request_binding linked_return_request)"
    using linked.successful_release_restores_exact_amount_and_closes
      [OF linked_parent_release_succeeds] by blast
  show ?thesis using amount linked_parent_pending_return_guards
    by (simp add: linked_return_request_projection linked_published_reverse_core_projection
      source_link_certificate_event_frames source_link_issued_certificate_update_frames source_link_sample_projections)
qed

lemma source_link_certificate_return_projection:
  "returned_bindings [Certificate_Event cert,Return_Event b]=[b]"
  by (simp add: returned_bindings_def)

lemma linked_parent_release_histories:
  "source_effects (machine_state (fst (linked.release_to_source (sample_source_context ACTIVE)
      linked_return_request 0 (vector_lookup []) (core_parent linked_published_reverse_core))))=
      [sample_binding 17,sample_binding 22] \<and>
    returned_bindings (machine_journal (fst (linked.release_to_source (sample_source_context ACTIVE)
      linked_return_request 0 (vector_lookup []) (core_parent linked_published_reverse_core))))=
      [sample_binding 22]"
  using linked_parent_release_succeeds
  by (auto simp: linked.release_to_source_def record_observation_def commit_reservation_event_def
    linked_return_request_projection linked_published_reverse_core_projection
    linked_parent_really_records_both_source_effects linked_parent_pending_return_guards
    source_link_issued_certificate_update_frames source_link_sample_projections
    finish_reservation_def set_phase_def source_link_certificate_return_projection split: if_splits)

lemma linked_return_client_result:
  "linked.execute_finality_client
      (Client_Protocol 0 0 (Return_Intent linked_return_request 0 [])) linked_published_reverse_core=
    ((linked_published_reverse_core\<lparr>core_parent:=fst (linked.release_to_source
      (sample_source_context ACTIVE) linked_return_request 0 (vector_lookup [])
      (core_parent linked_published_reverse_core))\<rparr>)\<lparr>core_epoch:=10\<rparr>,
      Protocol_Response Reservation_Released)"
  using linked_parent_release_succeeds
  by (simp add: linked.execute_finality_client_def linked.finality_step_def linked.core_result.simps
    linked.invoke_protocol_def linked.intent_result.simps
    linked_published_reverse_core_projection linked_return_request_projection
    source_link_sample_projections exact_record_reference_def record_reference_def lift_protocol_result_def Let_def)

definition linked_return_result :: "controlled_source_state \<times> (finality_core \<times> finality_reply)"
  where
  "linked_return_result=linked.mirror_source_return linked_source_state 0
    (core_epoch linked_published_reverse_core) 0
    linked_return_request 0 [] linked_published_reverse_core"

lemma linked_exact_reversed_source_fact:
  "controlled_source_fact linked_source_state (binding_key (request_binding linked_return_request))=
    Some \<lparr>statement_binding=request_binding linked_return_request,statement_status=Reversed\<rparr>"
  using linked_source_really_produces_both_facts
  by (simp add: linked_return_request_projection source_link_sample_projections sample_statement_def)

theorem linked_return_is_one_source_restoration_and_one_parent_mirror_update:
  "fst linked_return_result=linked_source_state \<and>
    snd (snd linked_return_result)=Protocol_Response Reservation_Released \<and>
    boundary_units (controlled_endpoint (fst linked_return_result)) (0,22)=5 \<and>
    source_units (machine_state (core_parent (fst (snd linked_return_result)))) (0,22)=5"
  by (simp add: linked_return_result_def linked.mirror_source_return_def
    linked_exact_reversed_source_fact linked_return_client_result
    linked_source_financial_projection linked_parent_release_available_units)

theorem linked_return_has_exact_source_mirror_provenance:
  "source_mirror_provenance linked_source_state
    (core_parent (fst (snd linked_return_result)))"
  by (simp add: source_mirror_provenance_def linked_return_result_def linked.mirror_source_return_def
    linked_exact_reversed_source_fact linked_return_client_result
    linked_source_financial_projection linked_parent_release_histories)

theorem linked_final_return_is_an_actual_child_continuation:
  "fst (snd linked_return_result)=
    linked.finality_step
      (Invoke_Protocol 0 (core_epoch linked_published_reverse_core) 0
        (Return_Intent linked_return_request 0 [])) linked_published_reverse_core \<and>
    core_epoch (fst (snd linked_return_result))=10"
  by (simp add: linked_return_result_def linked.mirror_source_return_def
    linked_exact_reversed_source_fact linked.execute_finality_client_def
    linked_published_reverse_core_projection linked.finality_epoch_advances)

text \<open>The authoritative endpoint owns the actual source units. The parent
  source_units field is an accounting view of that same allocation, not a
  second holding to add to it. During lost acknowledgments the debit and return
  gaps can be nonzero. Current observation needs the corresponding freshness
  checks; local absence is not evidence that the source did nothing.

  A controlled Reverse restores the physical-model source allocation once.
  The mirror operation consumes its exact Reversed fact and calls the existing
  parent return function, while framing the entire authoritative source state.
  Thus applying both model updates must be implemented as one source effect
  and its accounting acknowledgment, not as two resource-return API calls.
  The two-view equation is conditional on the same genesis and the proved
  accounting invariants. Physical source control, authenticated receipts,
  mirror completeness and production implementation refinement remain explicit
  obligations. No regulatory producer or runtime crypto is certified here.\<close>

end
