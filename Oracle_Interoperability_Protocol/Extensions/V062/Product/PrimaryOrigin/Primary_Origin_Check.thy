theory Primary_Origin_Check
  imports "OIP_Reference_Execution.Native_Original_Settlement"
begin

section \<open>Exact original-event selection and retention\<close>

text \<open>
  The observation takes the selected slot at the exact origin key. Its native
  funding owner is carried alongside the public transfer binding. Transport
  admission and the current caller/credential check are separate inputs.
\<close>

type_synonym po_binding = "transfer_binding \<times> nat"

record po_slot =
  po_retained_binding :: po_binding
  po_retained_epoch :: nat
  po_retained_debit :: nat
  po_retained_values :: native_origin_slot_value

datatype po_command = PO_Debit | PO_Terminal po_binding bool | PO_Confirm | PO_Reverse | PO_Publish | PO_Other

definition po_match where
  "po_match check_epoch po_requested po_epoch po_selected \<longleftrightarrow>
     po_retained_binding po_selected = po_requested \<and>
     (\<not> check_epoch \<or> po_retained_epoch po_selected = po_epoch)"

definition po_kind_selected where
  "po_kind_selected po_kind po_selected \<longleftrightarrow>
     map_option fst (slot_decision_value (po_retained_values po_selected)) = Some po_kind"

definition po_terminal_kind_allowed where
  "po_terminal_kind_allowed po_kind po_selected \<longleftrightarrow>
     slot_decision_value (po_retained_values po_selected) = None \<or> po_kind_selected po_kind po_selected"

fun po_origin_allowed where
  "po_origin_allowed check_epoch po_requested po_epoch po_cut PO_Debit None = (po_epoch = po_cut)"
| "po_origin_allowed check_epoch po_requested po_epoch po_cut PO_Debit (Some po_selected) =
     po_match check_epoch po_requested po_epoch po_selected"
| "po_origin_allowed check_epoch po_requested po_epoch po_cut (PO_Terminal po_evidence po_kind) po_row =
     (po_evidence = po_requested \<and> (case po_row of None \<Rightarrow> False | Some po_selected \<Rightarrow>
       po_match check_epoch po_requested po_epoch po_selected \<and> po_terminal_kind_allowed po_kind po_selected))"
| "po_origin_allowed check_epoch po_requested po_epoch po_cut PO_Confirm po_row =
     (case po_row of None \<Rightarrow> False | Some po_selected \<Rightarrow>
       po_match check_epoch po_requested po_epoch po_selected \<and> po_kind_selected True po_selected)"
| "po_origin_allowed check_epoch po_requested po_epoch po_cut PO_Reverse po_row =
     (case po_row of None \<Rightarrow> False | Some po_selected \<Rightarrow>
       po_match check_epoch po_requested po_epoch po_selected \<and> po_kind_selected False po_selected)"
| "po_origin_allowed check_epoch po_requested po_epoch po_cut PO_Publish po_row =
     (case po_row of None \<Rightarrow> False | Some po_selected \<Rightarrow>
       po_match check_epoch po_requested po_epoch po_selected \<and> slot_settlement_value (po_retained_values po_selected) \<noteq> None)"
| "po_origin_allowed check_epoch po_requested po_epoch po_cut PO_Other po_row = True"

definition po_public_decision where
  "po_public_decision po_selected = map_option (\<lambda>(po_kind,po_position).
     \<lparr>origin_binding = fst (po_retained_binding po_selected),
      origin_kind = (if po_kind then Confirmed_Decision else Reversed_Decision),
      origin_epoch = po_retained_epoch po_selected, origin_commit_position = po_position\<rparr>)
     (slot_decision_value (po_retained_values po_selected))"

lemma po_ordinary_credit_requires_the_same_public_decision_and_native_owner:
  assumes relation: "origin_decisions po_world (binding_key (fst po_requested)) = po_public_decision po_selected"
  shows "po_origin_allowed True po_requested po_epoch po_cut PO_Confirm (Some po_selected) =
      (snd (po_retained_binding po_selected) = snd po_requested \<and>
       existing_decision_matches po_world (fst po_requested) Confirmed_Decision po_epoch)"
  by (cases "slot_decision_value (po_retained_values po_selected)")
     (auto simp: po_match_def po_kind_selected_def po_public_decision_def existing_decision_matches_def
        decision_matches_def relation split: prod.splits if_splits intro: prod_eqI)

lemma po_ordinary_return_requires_the_same_public_decision_and_native_owner:
  assumes relation: "origin_decisions po_world (binding_key (fst po_requested)) = po_public_decision po_selected"
  shows "po_origin_allowed True po_requested po_epoch po_cut PO_Reverse (Some po_selected) =
      (snd (po_retained_binding po_selected) = snd po_requested \<and>
       existing_decision_matches po_world (fst po_requested) Reversed_Decision po_epoch)"
  by (cases "slot_decision_value (po_retained_values po_selected)")
     (auto simp: po_match_def po_kind_selected_def po_public_decision_def existing_decision_matches_def
        decision_matches_def relation split: prod.splits if_splits intro: prod_eqI)

definition po_keep_first_decision where
  "po_keep_first_decision po_kind po_commit po_selected =
     (let po_values = po_retained_values po_selected in
      if slot_decision_value po_values = None then
        po_selected\<lparr>po_retained_values := po_values\<lparr>slot_decision_value := Some (po_kind, po_commit)\<rparr>\<rparr>
      else po_selected)"

lemma po_retained_decision_and_commit_are_immutable:
  "slot_decision_value (po_retained_values po_selected) = Some (po_previous_kind, po_previous_commit) \<Longrightarrow>
    po_keep_first_decision po_kind po_commit po_selected = po_selected"
  by (simp add: po_keep_first_decision_def Let_def)

lemma po_first_decision_is_the_only_choice_for_the_same_origin:
  assumes "slot_decision_value (po_retained_values po_selected) = Some (po_previous_kind, po_previous_commit)"
    and "po_kind \<noteq> po_previous_kind"
  shows "\<not> po_origin_allowed check_epoch po_requested po_epoch po_cut
       (PO_Terminal po_requested po_kind) (Some po_selected)"
  using assms by (simp add: po_terminal_kind_allowed_def po_kind_selected_def)

lemma po_single_epoch_removal_exposes_the_same_terminal_request:
  assumes "po_retained_binding po_selected = po_requested"
    and "po_retained_epoch po_selected \<noteq> po_epoch"
    and "po_terminal_kind_allowed po_kind po_selected"
  shows "\<not> po_origin_allowed True po_requested po_epoch po_cut (PO_Terminal po_requested po_kind) (Some po_selected)"
    and "po_origin_allowed False po_requested po_epoch po_cut (PO_Terminal po_requested po_kind) (Some po_selected)"
  using assms by (simp_all add: po_match_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms po_ordinary_credit_requires_the_same_public_decision_and_native_owner
      po_ordinary_return_requires_the_same_public_decision_and_native_owner
      po_retained_decision_and_commit_are_immutable po_first_decision_is_the_only_choice_for_the_same_origin
      po_single_epoch_removal_exposes_the_same_terminal_request})
  then () else error "Unexpected oracle in exact primary origin selection"
\<close>

end
