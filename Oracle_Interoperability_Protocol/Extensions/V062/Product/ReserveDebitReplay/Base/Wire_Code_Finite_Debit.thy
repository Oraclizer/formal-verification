theory Wire_Code_Finite_Debit
  imports Wire_Code_Finite_Reservation_Queries
begin

definition code_finite_execute_source_effect :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow> code_finite_reservation_machine \<Rightarrow> (code_finite_reservation_machine \<times> reservation_reply)" where
  "code_finite_execute_source_effect authority_view request generation versions machine =
    (let financial = finite_machine_state machine; binding = request_binding request
     in if \<not> current_use_allowed (lock_authority authority_view) request \<or>
           \<not> code_finite_binding_registered financial binding
        then code_finite_record_observation request Request_Rejected machine
        else if binding_key binding \<in> set (map binding_key (finite_source_effects financial))
        then code_finite_record_observation request Source_Already_Debited machine
        else if code_finite_owns_current authority_view request generation versions financial \<and>
             map_option reservation_phase (map_of (finite_reservations financial) (binding_key binding))
               \<in> {Some Source_Submitted,Some Source_Pending} \<and>
             binding_operation binding = Destination_Credit \<and> 0 < binding_amount binding \<and>
             binding_amount binding \<le> code_finite_nat_default (finite_source_units financial) (source_account_of binding) \<and>
             context_endpoint (lock_authority authority_view) = fst (binding_key binding) \<and>
             metadata_permission authority_view request (fst (binding_key binding))
        then code_finite_record_observation request Source_Debited (code_finite_commit_source_effect binding machine)
        else code_finite_record_observation request Request_Rejected machine)"

theorem the_finite_debit_and_frozen_debit_are_exactly_the_same_operation:
  "map_prod code_interpret_finite_machine id
      (code_finite_execute_source_effect authority_view request generation versions machine) =
    execute_source_effect authority_view request generation versions (code_interpret_finite_machine machine)"
proof -
  let ?financial = "finite_machine_state machine"
  let ?interpreted = "code_interpret_finite_machine machine"
  let ?binding = "request_binding request"
  have registered: "code_finite_binding_registered ?financial ?binding = binding_is_registered (machine_state ?interpreted) ?binding"
    by (simp add: code_interpret_finite_machine_def finite_registration_query_is_the_exact_existing_registered_binding_test)
  have ownership: "code_finite_owns_current authority_view request generation versions ?financial =
      owns_current_reservation authority_view request generation versions (machine_state ?interpreted)"
    by (simp add: code_interpret_finite_machine_def finite_current_ownership_is_the_exact_existing_current_footprint_test)
  have debited: "(binding_key ?binding \<in> set (map binding_key (finite_source_effects ?financial))) =
      source_was_debited (machine_state ?interpreted) (binding_key ?binding)"
    by (simp add: code_interpret_finite_machine_def code_interpret_finite_financial_def source_was_debited_def)
  have phase: "map_option reservation_phase (map_of (finite_reservations ?financial) (binding_key ?binding)) =
      phase_at (machine_state ?interpreted) (binding_key ?binding)"
    by (simp add: code_interpret_finite_machine_def code_interpret_finite_financial_def phase_at_def)
  have balance: "code_finite_nat_default (finite_source_units ?financial) (source_account_of ?binding) =
      source_units (machine_state ?interpreted) (source_account_of ?binding)"
    by (simp add: code_interpret_finite_machine_def code_interpret_finite_financial_def)
  show ?thesis
    unfolding code_finite_execute_source_effect_def execute_source_effect_def Let_def
    by (simp only: registered ownership debited phase balance;
        auto simp: finite_observation_interprets_the_same_complete_existing_observation
          finite_source_commit_interprets_the_same_state_and_appended_journal_event split: if_splits)
qed

corollary a_finite_debit_returns_the_same_existing_reply:
  "snd (code_finite_execute_source_effect authority_view request generation versions machine) =
    snd (execute_source_effect authority_view request generation versions (code_interpret_finite_machine machine))"
  using arg_cong[OF the_finite_debit_and_frozen_debit_are_exactly_the_same_operation,
    where f=snd] by simp

text \<open>
  This is a finite representation of the frozen financial function, with
  an exact interpretation equality as its proof obligation. It is not
  justified merely as a second independently written oracle. No source
  identity/product/retained commit/fullconsume/resolver is inferred from
  this equality. Current service and the source owner extension must be
  composed separately, and the raw executable producer still needs native
  codegen/export/runtime reception. No export failure has been observed.
\<close>

end
