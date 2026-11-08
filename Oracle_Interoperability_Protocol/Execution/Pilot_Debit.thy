theory Pilot_Debit
  imports "OIP_Product.Checked_Execution"
begin

record pilot_debit_account =
  debit_total :: nat
  debit_funded :: nat
  debit_clock :: nat
  debit_deadline :: nat
  debit_phase :: reservation_phase

definition pilot_debit_enabled where
  "pilot_debit_enabled account amount \<longleftrightarrow>
    debit_phase account = Source_Submitted \<and> debit_clock account < debit_deadline account \<and>
    0 < amount \<and> amount \<le> debit_total account - debit_funded account"

definition native_debit_transition where
  "native_debit_transition account amount =
    (if pilot_debit_enabled account amount
     then (account\<lparr>debit_total := debit_total account - amount, debit_phase := Source_Pending\<rparr>, Source_Debited)
     else (account, Request_Rejected))"

definition reference_debit_transition where
  "reference_debit_transition cfg request generation versions owner_total owner_funded machine =
    (let state = machine_state machine; binding = request_binding request;
         amount = binding_amount binding
     in case reservation_at state (binding_key binding) of
          None \<Rightarrow> record_observation request Request_Rejected machine
        | Some reservation \<Rightarrow>
            if reservation_phase reservation = Source_Submitted \<and>
               reservation_clock state < reservation_deadline reservation \<and>
               0 < amount \<and> amount \<le> owner_total - owner_funded
            then execute_source_effect cfg request generation versions machine
            else record_observation request Request_Rejected machine)"

theorem the_native_payer_and_the_model_pool_move_by_the_same_debit:
  fixes account machine request reservation binding cfg generation versions native_result model_result
  defines "binding \<equiv> request_binding request"
    and "native_result \<equiv> native_debit_transition account (binding_amount binding)"
    and "model_result \<equiv> reference_debit_transition cfg request generation versions
      (debit_total account) (debit_funded account) machine"
  assumes retained: "reservation_at (machine_state machine) (binding_key binding) = Some reservation"
    and phase: "debit_phase account = reservation_phase reservation"
    and clock: "debit_clock account = reservation_clock (machine_state machine)"
    and deadline: "debit_deadline account = reservation_deadline reservation"
    and funding: "debit_funded account \<le> debit_total account"
    and pool: "source_units (machine_state machine) (source_account_of binding) =
      debit_total account - debit_funded account + other"
    and admitted: "current_use_allowed (lock_authority cfg) request"
    and registered: "binding_is_registered (machine_state machine) binding"
    and first: "pilot_debit_enabled account (binding_amount binding) \<Longrightarrow>
      \<not> source_was_debited (machine_state machine) (binding_key binding)"
    and owns: "pilot_debit_enabled account (binding_amount binding) \<Longrightarrow>
      owns_current_reservation cfg request generation versions (machine_state machine)"
    and operation: "binding_operation binding = Destination_Credit"
    and endpoint: "context_endpoint (lock_authority cfg) = fst (binding_key binding)"
    and metadata: "metadata_permission cfg request (fst (binding_key binding))"
  shows "snd native_result = snd model_result \<and>
    source_units (machine_state (fst model_result)) (source_account_of binding) =
      debit_total (fst native_result) - debit_funded (fst native_result) + other"
proof -
  have matches: "pilot_debit_enabled account (binding_amount binding) \<longleftrightarrow>
    reservation_phase reservation = Source_Submitted \<and>
    reservation_clock (machine_state machine) < reservation_deadline reservation \<and>
    0 < binding_amount binding \<and> binding_amount binding \<le> debit_total account - debit_funded account"
    by (simp add: pilot_debit_enabled_def phase clock deadline)
  have body: "reference_debit_transition cfg request generation versions (debit_total account)
      (debit_funded account) machine =
     (if pilot_debit_enabled account (binding_amount binding)
      then execute_source_effect cfg request generation versions machine
      else record_observation request Request_Rejected machine)"
    using retained matches by (simp add: reference_debit_transition_def binding_def Let_def)
  show ?thesis
  proof (cases "pilot_debit_enabled account (binding_amount binding)")
    case True
    then have submitted: "phase_at (machine_state machine) (binding_key binding) = Some Source_Submitted"
      and enough: "binding_amount binding \<le> debit_total account - debit_funded account"
      and positive: "0 < binding_amount binding"
      using matches retained by (auto simp: phase_at_def)
    have pool_enough: "binding_amount binding \<le> source_units (machine_state machine) (source_account_of binding)"
      using pool enough by arith
    have public: "execute_source_effect cfg request generation versions machine =
       record_observation request Source_Debited (commit_reservation_event (Source_Effect_Event binding) machine)"
      using admitted registered first[OF True] owns[OF True] submitted enough positive pool_enough operation endpoint metadata
      by (simp add: execute_source_effect_def binding_def Let_def)
    have subtract: "debit_total account - debit_funded account + other - binding_amount binding =
      debit_total account - binding_amount binding - debit_funded account + other"
      using enough funding by arith
    show ?thesis
      using True pool subtract
      by (simp add: native_result_def model_result_def native_debit_transition_def body public
          commit_reservation_event_def record_observation_def set_phase_def)
  next
    case False
    then show ?thesis
      using pool by (simp add: native_result_def model_result_def native_debit_transition_def body record_observation_def)
  qed
qed

lemma the_same_aggregate_cannot_replace_the_exact_payer_check:
  assumes "debit_total a - debit_funded a < amount"
  shows "native_debit_transition a amount = (a, Request_Rejected)"
  using assms by (simp add: native_debit_transition_def pilot_debit_enabled_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_native_payer_and_the_model_pool_move_by_the_same_debit
      the_same_aggregate_cannot_replace_the_exact_payer_check})
  then () else error "Unexpected oracle in the pilot debit"
\<close>

end
