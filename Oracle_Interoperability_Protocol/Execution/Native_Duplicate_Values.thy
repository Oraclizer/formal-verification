theory Native_Duplicate_Values
  imports "OIP_Product.Released_Credit_Receipt"
begin

type_synonym native_terminal_value = "transfer_binding \<times> bool \<times> nat"

datatype native_duplicate_command =
  Native_Other | Native_Record native_terminal_value | Native_Credit nat |
  Native_Refund nat | Native_Publish

datatype native_duplicate_outcome =
  Native_Decision nat | Native_Settlement bool nat | Native_Published nat

record native_origin_slot_value =
  slot_decision_value :: "(bool \<times> nat) option"
  slot_settlement_value :: "nat option"
  slot_publication_value :: "nat option"

record native_duplicate_input =
  duplicate_binding_value :: transfer_binding
  duplicate_command_value :: native_duplicate_command
  duplicate_origins_value :: "source_key \<Rightarrow> native_origin_slot_value option"
  duplicate_evidence_value :: "nat \<Rightarrow> native_terminal_value option"

record native_duplicate_registers =
  duplicate_pc :: nat
  observed_slot :: "native_origin_slot_value option"
  observed_decision :: "(bool \<times> nat) option"
  observed_commit :: "nat option"
  selected_kind :: bool
  selected_reference :: nat
  observed_evidence :: "native_terminal_value option"
  evidence_comparison :: bool
  staged_outcome :: "native_duplicate_outcome option"
  duplicate_return :: "native_duplicate_outcome option"

fun command_reference where
  "command_reference (Native_Record (_, _, reference)) = reference"
| "command_reference (Native_Credit reference) = reference"
| "command_reference (Native_Refund reference) = reference"
| "command_reference command = 0"

fun record_value where
  "record_value (Native_Record evidence) = Some evidence"
| "record_value command = None"

definition duplicate_initial_registers where
  "duplicate_initial_registers = \<lparr>duplicate_pc=0, observed_slot=None, observed_decision=None,
    observed_commit=None, selected_kind=False, selected_reference=0, observed_evidence=None,
    evidence_comparison=False, staged_outcome=None, duplicate_return=None\<rparr>"

definition native_duplicate_value_step where
  "native_duplicate_value_step input machine =
    (let pc = duplicate_pc machine;
         slot = the (observed_slot machine);
         command = duplicate_command_value input
     in if pc = 0 then machine\<lparr>duplicate_pc:=1,
          observed_slot:=duplicate_origins_value input (binding_key (duplicate_binding_value input))\<rparr>
     else if pc = 1 then machine\<lparr>duplicate_pc:=2\<rparr>
     else if pc = 2 then machine\<lparr>duplicate_pc:=(if observed_slot machine = None then 5 else 4)\<rparr>
     else if pc = 4 then machine\<lparr>duplicate_pc:=(case command of Native_Record _ \<Rightarrow> 10 |
          Native_Credit _ \<Rightarrow> 9 | Native_Refund _ \<Rightarrow> 8 | Native_Publish \<Rightarrow> 7 | Native_Other \<Rightarrow> 6)\<rparr>
     else if pc = 5 \<or> pc = 6 \<or> pc = 16 \<or> pc = 21 \<or> pc = 24 \<or> pc = 27 \<or> pc = 32
       then machine\<lparr>duplicate_pc:=34, duplicate_return:=None\<rparr>
     else if pc = 7 then machine\<lparr>duplicate_pc:=30, observed_commit:=slot_publication_value slot\<rparr>
     else if pc = 8 \<or> pc = 9 then machine\<lparr>duplicate_pc:=18, selected_reference:=command_reference command\<rparr>
     else if pc = 10 then machine\<lparr>duplicate_pc:=11,
          observed_evidence:=duplicate_evidence_value input (command_reference command)\<rparr>
     else if pc = 11 then machine\<lparr>duplicate_pc:=12,
          evidence_comparison:=(observed_evidence machine = record_value command)\<rparr>
     else if pc = 12 then machine\<lparr>duplicate_pc:=(if evidence_comparison machine then 13 else 6)\<rparr>
     else if pc = 13 then machine\<lparr>duplicate_pc:=14, observed_decision:=slot_decision_value slot\<rparr>
     else if pc = 14 then machine\<lparr>duplicate_pc:=(if observed_decision machine = None then 16 else 15)\<rparr>
     else if pc = 15 then machine\<lparr>duplicate_pc:=17,
          staged_outcome:=Some (Native_Decision (snd (the (observed_decision machine))))\<rparr>
     else if pc = 17 \<or> pc = 29 \<or> pc = 33 then machine\<lparr>duplicate_pc:=34, duplicate_return:=staged_outcome machine\<rparr>
     else if pc = 18 then machine\<lparr>duplicate_pc:=19, observed_decision:=slot_decision_value slot\<rparr>
     else if pc = 19 then machine\<lparr>duplicate_pc:=(if observed_decision machine = None then 21 else 20)\<rparr>
     else if pc = 20 then machine\<lparr>duplicate_pc:=22, selected_kind:=fst (the (observed_decision machine)),
          observed_commit:=slot_settlement_value slot\<rparr>
     else if pc = 22 then machine\<lparr>duplicate_pc:=(if observed_commit machine = None then 24 else 23)\<rparr>
     else if pc = 23 then machine\<lparr>duplicate_pc:=25,
          observed_evidence:=duplicate_evidence_value input (selected_reference machine)\<rparr>
     else if pc = 25 then machine\<lparr>duplicate_pc:=26, evidence_comparison:=(observed_evidence machine \<noteq>
          Some (duplicate_binding_value input, selected_kind machine, selected_reference machine))\<rparr>
     else if pc = 26 then machine\<lparr>duplicate_pc:=(if evidence_comparison machine then 27 else 28)\<rparr>
     else if pc = 28 then machine\<lparr>duplicate_pc:=29,
          staged_outcome:=Some (Native_Settlement (selected_kind machine) (the (observed_commit machine)))\<rparr>
     else if pc = 30 then machine\<lparr>duplicate_pc:=(if observed_commit machine = None then 32 else 31)\<rparr>
     else if pc = 31 then machine\<lparr>duplicate_pc:=33,
          staged_outcome:=Some (Native_Published (the (observed_commit machine)))\<rparr>
     else machine)"

fun native_duplicate_value_run where
  "native_duplicate_value_run input 0 machine = machine"
| "native_duplicate_value_run input (Suc fuel) machine =
    (if duplicate_pc machine = 34 then machine else native_duplicate_value_run input fuel (native_duplicate_value_step input machine))"

definition native_duplicate_selected_value where
  "native_duplicate_selected_value input =
    (case duplicate_origins_value input (binding_key (duplicate_binding_value input)) of None \<Rightarrow> None
     | Some slot \<Rightarrow> (case duplicate_command_value input of
         Native_Record evidence \<Rightarrow>
           (if duplicate_evidence_value input (command_reference (Native_Record evidence)) = Some evidence
           then map_option (\<lambda>decision. Native_Decision (snd decision)) (slot_decision_value slot) else None)
       | Native_Credit reference \<Rightarrow>
           (case (slot_decision_value slot, slot_settlement_value slot) of (Some (kind, decision_commit), Some commit) \<Rightarrow>
             if duplicate_evidence_value input reference = Some (duplicate_binding_value input, kind, reference)
             then Some (Native_Settlement kind commit) else None | _ \<Rightarrow> None)
       | Native_Refund reference \<Rightarrow>
           (case (slot_decision_value slot, slot_settlement_value slot) of (Some (kind, decision_commit), Some commit) \<Rightarrow>
             if duplicate_evidence_value input reference = Some (duplicate_binding_value input, kind, reference)
             then Some (Native_Settlement kind commit) else None | _ \<Rightarrow> None)
       | Native_Publish \<Rightarrow> map_option Native_Published (slot_publication_value slot)
       | Native_Other \<Rightarrow> None))"

lemma duplicate_value_interpretation:
  "duplicate_pc (native_duplicate_value_run input 20 duplicate_initial_registers) = 34 \<and>
   duplicate_return (native_duplicate_value_run input 20 duplicate_initial_registers) = native_duplicate_selected_value input"
proof (cases "duplicate_origins_value input (binding_key (duplicate_binding_value input))")
  case None
  then show ?thesis
    by (simp add: native_duplicate_value_step_def duplicate_initial_registers_def
        native_duplicate_selected_value_def Let_def numeral_eq_Suc)
next
  case (Some slot)
  then show ?thesis
    by (cases "duplicate_command_value input";
        cases "slot_decision_value slot";
        cases "slot_settlement_value slot";
        cases "slot_publication_value slot")
      (auto simp: native_duplicate_value_step_def duplicate_initial_registers_def
        native_duplicate_selected_value_def Let_def numeral_eq_Suc split: if_splits prod.splits)
qed

lemma settlement_value_uses_the_retained_commit_and_kind:
  assumes "duplicate_origins_value input (binding_key (duplicate_binding_value input)) = Some slot"
    "slot_decision_value slot = Some (kind, decision_commit)"
    "slot_settlement_value slot = Some original_commit"
    "duplicate_command_value input = Native_Credit reference \<or> duplicate_command_value input = Native_Refund reference"
    "duplicate_evidence_value input reference = Some (duplicate_binding_value input, kind, reference)"
  shows "duplicate_return (native_duplicate_value_run input 20 duplicate_initial_registers) =
    Some (Native_Settlement kind original_commit)"
  using duplicate_value_interpretation[of input] assms
  by (auto simp: native_duplicate_selected_value_def)

lemma wrong_evidence_cannot_create_a_settlement_value:
  assumes "duplicate_origins_value input (binding_key (duplicate_binding_value input)) = Some slot"
    "slot_decision_value slot = Some (kind, decision_commit)"
    "duplicate_command_value input = Native_Credit reference \<or> duplicate_command_value input = Native_Refund reference"
    "duplicate_evidence_value input reference \<noteq> Some (duplicate_binding_value input, kind, reference)"
  shows "duplicate_return (native_duplicate_value_run input 20 duplicate_initial_registers) = None"
  using duplicate_value_interpretation[of input] assms
  by (auto simp: native_duplicate_selected_value_def split: option.splits)

text \<open>This normal MIR value interpretation takes immutable origin/evidence
  lookup functions as inputs. It does not establish their implementation, the
  provenance of retained commits, current admission or receipt credentials, the
  complete native snapshot relation, serialization, or the enclosing mutation.
  True/False denotes Confirmed/Reversed, not an authorization predicate.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms duplicate_value_interpretation
      settlement_value_uses_the_retained_commit_and_kind wrong_evidence_cannot_create_a_settlement_value})
  then () else error "Unexpected oracle in native duplicate values"
\<close>

end
