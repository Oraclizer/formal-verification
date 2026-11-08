theory Reference_Trusted_Time
  imports "OIP_Product.Central_Product_Closure" "Reference_Ordered_Control"
begin

datatype reference_time_input = Signed_Clock_Observation nat | Caller_Elapsed nat

context source_attestation
begin

definition ordered_reference_time_operation where
  "ordered_reference_time_operation input observed live actor available expected actual session_bound clock_granted
      time_verified revision_room endpoint core =
    (if observed \<noteq> live \<or> actor \<in> control_revoked live then None else
     case input of Caller_Elapsed _ \<Rightarrow> None
       | Signed_Clock_Observation now \<Rightarrow>
         clock_observation_operation available expected actual session_bound clock_granted time_verified
           revision_room endpoint now core)"

lemma an_unverified_elapsed_value_cannot_advance_the_reference_legal_clock:
  "ordered_reference_time_operation (Caller_Elapsed elapsed) observed live actor available expected actual
      session_bound clock_granted time_verified revision_room endpoint core = None"
  by (simp add: ordered_reference_time_operation_def)

lemma an_old_cut_or_revoked_observer_cannot_advance_the_reference_legal_clock:
  assumes "observed \<noteq> live \<or> actor \<in> control_revoked live"
  shows "ordered_reference_time_operation input observed live actor available expected actual
      session_bound clock_granted time_verified revision_room endpoint core = None"
  using assms by (simp add: ordered_reference_time_operation_def)

theorem a_selected_trusted_observation_advances_time_without_resolving_pending_money:
  assumes admitted: "ordered_reference_time_operation (Signed_Clock_Observation now) observed live actor
      available expected actual session_bound clock_granted time_verified revision_room endpoint core = Some operation"
  shows "reservation_clock (machine_state (core_parent (finality_step operation core))) = now"
    "unresolved_source_obligations (machine_state (core_parent (finality_step operation core))) =
       unresolved_source_obligations (machine_state (core_parent core))"
    "source_units (machine_state (core_parent (finality_step operation core))) =
       source_units (machine_state (core_parent core))"
    "destination_units (machine_state (core_parent (finality_step operation core))) =
       destination_units (machine_state (core_parent core))"
proof -
  have "clock_observation_operation available expected actual session_bound clock_granted
      time_verified revision_room endpoint now core = Some operation"
    using admitted by (auto simp: ordered_reference_time_operation_def split: if_splits)
  then show "reservation_clock (machine_state (core_parent (finality_step operation core))) = now"
    "unresolved_source_obligations (machine_state (core_parent (finality_step operation core))) =
       unresolved_source_obligations (machine_state (core_parent core))"
    "source_units (machine_state (core_parent (finality_step operation core))) =
       source_units (machine_state (core_parent core))"
    "destination_units (machine_state (core_parent (finality_step operation core))) =
       destination_units (machine_state (core_parent core))"
    by (rule an_admitted_clock_observation_is_the_exact_public_time_operation)+
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.an_unverified_elapsed_value_cannot_advance_the_reference_legal_clock
      source_attestation.an_old_cut_or_revoked_observer_cannot_advance_the_reference_legal_clock
      source_attestation.a_selected_trusted_observation_advances_time_without_resolving_pending_money})
  then () else error "Unexpected oracle in reference trusted time"
\<close>

end
