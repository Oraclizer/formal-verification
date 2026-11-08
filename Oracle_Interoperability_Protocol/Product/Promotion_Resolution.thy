theory Promotion_Resolution
  imports Wire_Amounts "OIP_Product_Base.Lock_Accounting"
begin

section \<open>Resolution by the kind of authenticated evidence\<close>

datatype resolution_side = Resolve_Credit | Resolve_Return

definition bound_resolution where
  "bound_resolution authenticate classify expected evidence =
    (if authenticate evidence then (case classify evidence of
       Some (actual, side) \<Rightarrow> if actual = expected then Some side else None
        | None \<Rightarrow> None)
     else None)"

record 'binding pending_resolution_state =
  unresolved_binding :: "'binding option"
  unresolved_units :: nat
  active_origin_units :: nat
  active_destination_units :: nat

definition resolve_pending where
  "resolve_pending authenticate classify evidence state =
    (case unresolved_binding state of None \<Rightarrow> state | Some binding \<Rightarrow>
       case bound_resolution authenticate classify binding evidence of None \<Rightarrow> state
        | Some Resolve_Credit \<Rightarrow> state\<lparr>unresolved_binding := None, unresolved_units := 0,
            active_destination_units := active_destination_units state + unresolved_units state\<rparr>
        | Some Resolve_Return \<Rightarrow> state\<lparr>unresolved_binding := None, unresolved_units := 0,
            active_origin_units := active_origin_units state + unresolved_units state\<rparr>)"

definition resolution_mass where
  "resolution_mass state = active_origin_units state + active_destination_units state + unresolved_units state"

theorem evidence_resolution_conserves_the_active_and_pending_amount:
  "resolution_mass (resolve_pending authenticate classify evidence state) = resolution_mass state"
  by (auto simp: resolution_mass_def resolve_pending_def split: option.splits resolution_side.splits)

lemma unresolved_without_exact_authentic_evidence_does_not_move:
  assumes "unresolved_binding state = Some binding" "bound_resolution authenticate classify binding evidence = None"
  shows "resolve_pending authenticate classify evidence state = state"
  using assms by (simp add: resolve_pending_def)

lemma changed_binding_or_unauthenticated_evidence_cannot_resolve:
  assumes "unresolved_binding state = Some expected"
    "classify evidence = Some (actual, side)"
    "actual \<noteq> expected \<or> \<not> authenticate evidence"
  shows "resolve_pending authenticate classify evidence state = state"
  using assms by (auto simp: resolve_pending_def bound_resolution_def)

lemma an_exact_certified_resolution_cannot_execute_a_second_time:
  assumes "unresolved_binding state = Some binding" "bound_resolution authenticate classify binding first = Some side"
  shows "resolve_pending authenticate classify second (resolve_pending authenticate classify first state) =
    resolve_pending authenticate classify first state"
  using assms by (cases side) (simp_all add: resolve_pending_def)

definition eab_resolution_kind where
  "eab_resolution_kind authority index binding cert =
    (if exact_record_reference authority index binding Confirmed_Decision cert then Some (binding, Resolve_Credit)
     else if exact_record_reference authority index binding Reversed_Decision cert then Some (binding, Resolve_Return)
     else None)"

lemma same_current_eab_record_cannot_confirm_and_reverse:
  assumes "exact_record_reference authority index binding Confirmed_Decision cert"
  shows "\<not> exact_record_reference authority index binding Reversed_Decision cert"
  using assms by (auto simp: exact_record_reference_def record_reference_def Let_def split: option.splits if_splits)

lemma the_current_eab_evidence_selects_the_exact_resolution_kind:
  "bound_resolution (\<lambda>_. True) (eab_resolution_kind authority index binding) binding cert = Some Resolve_Credit
    \<longleftrightarrow> exact_record_reference authority index binding Confirmed_Decision cert"
  "bound_resolution (\<lambda>_. True) (eab_resolution_kind authority index binding) binding cert = Some Resolve_Return
    \<longleftrightarrow> exact_record_reference authority index binding Reversed_Decision cert"
  using same_current_eab_record_cannot_confirm_and_reverse
  by (auto simp: bound_resolution_def eab_resolution_kind_def split: if_splits)

context source_attestation
begin

lemma the_actual_eab_consumers_cannot_resolve_with_the_wrong_kind:
  assumes "bound_resolution (\<lambda>_. True) (eab_resolution_kind authority index (request_binding request))
    (request_binding request) (request_certificate request) \<noteq> Some required"
  shows "let intent = (case required of Resolve_Credit \<Rightarrow> Deliver_Intent route request
           | Resolve_Return \<Rightarrow> Return_Intent request generation versions);
             result = invoke_protocol endpoint (core_epoch authority) index intent authority
         in snd result = Finality_Rejected \<and>
           machine_state (core_parent (fst result)) = machine_state (core_parent authority)"
  using assms actual_delivery_requires_exact_confirmed_evidence actual_return_requires_exact_reversal_evidence
  by (cases required) (simp_all add: Let_def the_current_eab_evidence_selects_the_exact_resolution_kind)

end

definition binding_guard_removed where
  "binding_guard_removed authenticate classify evidence =
    (if authenticate evidence then map_option snd (classify evidence) else None)"

lemma removing_the_exact_binding_allows_the_same_wrong_evidence:
  "bound_resolution (\<lambda>_. True) (\<lambda>_. Some (22::nat, Resolve_Return)) 17 evidence = None \<and>
   binding_guard_removed (\<lambda>_. True) (\<lambda>_. Some (22::nat, Resolve_Return)) evidence = Some Resolve_Return"
  by (simp add: bound_resolution_def binding_guard_removed_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      evidence_resolution_conserves_the_active_and_pending_amount
      source_attestation.the_actual_eab_consumers_cannot_resolve_with_the_wrong_kind
      removing_the_exact_binding_allows_the_same_wrong_evidence})
  then () else error "Unexpected oracle in evidence-typed resolution"
\<close>

end
