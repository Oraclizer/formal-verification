(*
  Title:      Regulatory_Action_Composition/Regulatory_Action_Composition.thy
  Author:     Jinwook Kim (Jay) <jay@oraclizer.io>
  Maintainer: Jinwook Kim (Jay) <jay@oraclizer.io>
  License:    BSD

  Sequential composition of regulatory actions over the published
  five-state reference machine.  Invalid legal transitions are recorded as
  rejections, while operational failures remain a separate outcome class.
*)

theory Regulatory_Action_Composition
  imports "Cross_Domain_State_Preservation.Regulatory_Instance"
begin

section \<open>State Effects and Legal Outcomes\<close>

datatype legal_rejection_reason = Undefined_Transition

datatype operational_failure_reason =
    Missing_Asset
  | Lock_Unavailable
  | External_Failure

datatype command_outcome =
    Applied reg_state
  | Rejected legal_rejection_reason
  | Operational_Failure operational_failure_reason

fun state_after :: "reg_state \<Rightarrow> command_outcome \<Rightarrow> reg_state" where
  "state_after s (Applied s') = s'"
| "state_after s (Rejected r) = s"
| "state_after s (Operational_Failure r) = s"

definition legal_outcome :: "reg_state \<Rightarrow> reg_action \<Rightarrow> command_outcome" where
  "legal_outcome s a =
    (case reg_transition s a of
       Some s' \<Rightarrow> Applied s'
     | None \<Rightarrow> Rejected Undefined_Transition)"

definition state_effect :: "reg_state \<Rightarrow> reg_action \<Rightarrow> reg_state" where
  "state_effect s a = state_after s (legal_outcome s a)"

theorem action_state_idempotent:
  "state_effect (state_effect s a) a = state_effect s a"
  by (cases s; cases a; simp add: state_effect_def legal_outcome_def)

lemma successful_repeat_is_rejected:
  assumes "reg_transition s a = Some s'"
  shows "legal_outcome s a = Applied s' \<and>
         legal_outcome s' a = Rejected Undefined_Transition"
  using assms
  by (cases s; cases a; simp add: legal_outcome_def)

lemma rejected_repeat_stays_rejected:
  assumes "reg_transition s a = None"
  shows "legal_outcome s a = Rejected Undefined_Transition \<and>
         legal_outcome (state_effect s a) a = Rejected Undefined_Transition"
  using assms
  by (cases s; cases a; simp add: state_effect_def legal_outcome_def)

theorem concrete_rejected_repeat_stays_rejected:
  "legal_outcome FROZEN FREEZE = Rejected Undefined_Transition \<and>
   legal_outcome (state_effect FROZEN FREEZE) FREEZE =
     Rejected Undefined_Transition"
  by (simp add: state_effect_def legal_outcome_def)

fun run_word :: "reg_action list \<Rightarrow> reg_state \<Rightarrow> reg_state" where
  "run_word [] s = s"
| "run_word (a # as) s = run_word as (state_effect s a)"

fun action_outcome_queue ::
  "reg_action list \<Rightarrow> reg_state \<Rightarrow> reg_state \<times> command_outcome list"
where
  "action_outcome_queue [] s = (s, [])"
| "action_outcome_queue (a # as) s =
     (let out = legal_outcome s a;
          rest = action_outcome_queue as (state_after s out)
      in (fst rest, out # snd rest))"

lemma action_outcome_queue_state:
  "fst (action_outcome_queue as s) = run_word as s"
  by (induction as arbitrary: s) (simp_all add: Let_def state_effect_def)

lemma run_word_append:
  "run_word (xs @ ys) s = run_word ys (run_word xs s)"
  by (induction xs arbitrary: s) simp_all


section \<open>Complete Pair Classification\<close>

definition all_reg_states :: "reg_state list" where
  "all_reg_states = [ACTIVE, FROZEN, SEIZED, CONFISCATED, RESTRICTED]"

definition all_reg_actions :: "reg_action list" where
  "all_reg_actions =
    [FREEZE, SEIZE, CONFISCATE, RESTRICT, UNFREEZE, UNRESTRICT, RELEASE]"

definition commutes :: "reg_action \<Rightarrow> reg_action \<Rightarrow> bool" where
  "commutes a b \<longleftrightarrow>
    (\<forall>s. state_effect (state_effect s a) b =
         state_effect (state_effect s b) a)"

definition pair_commutes :: "reg_action \<times> reg_action \<Rightarrow> bool" where
  "pair_commutes p =
    (case p of (a, b) \<Rightarrow>
       list_all (\<lambda>s. state_effect (state_effect s a) b =
         state_effect (state_effect s b) a) all_reg_states)"

definition all_unordered_pairs :: "(reg_action \<times> reg_action) list" where
  "all_unordered_pairs =
    [(FREEZE, SEIZE), (FREEZE, CONFISCATE), (FREEZE, RESTRICT),
     (FREEZE, UNFREEZE), (FREEZE, UNRESTRICT), (FREEZE, RELEASE),
     (SEIZE, CONFISCATE), (SEIZE, RESTRICT), (SEIZE, UNFREEZE),
     (SEIZE, UNRESTRICT), (SEIZE, RELEASE),
     (CONFISCATE, RESTRICT), (CONFISCATE, UNFREEZE),
     (CONFISCATE, UNRESTRICT), (CONFISCATE, RELEASE),
     (RESTRICT, UNFREEZE), (RESTRICT, UNRESTRICT), (RESTRICT, RELEASE),
     (UNFREEZE, UNRESTRICT), (UNFREEZE, RELEASE),
     (UNRESTRICT, RELEASE)]"

theorem all_unordered_pairs_distinct:
  "distinct all_unordered_pairs"
  by (simp add: all_unordered_pairs_def)

theorem all_unordered_pairs_irreflexive:
  "(a, a) \<notin> set all_unordered_pairs"
  by (cases a) (simp_all add: all_unordered_pairs_def)

theorem all_unordered_pairs_complete:
  assumes "a \<noteq> b"
  shows "(a, b) \<in> set all_unordered_pairs \<or>
         (b, a) \<in> set all_unordered_pairs"
  using assms
  by (cases a; cases b; simp add: all_unordered_pairs_def)

definition commuting_pairs :: "(reg_action \<times> reg_action) list" where
  "commuting_pairs =
    [(FREEZE, CONFISCATE), (FREEZE, RESTRICT), (FREEZE, UNRESTRICT),
     (SEIZE, CONFISCATE), (SEIZE, UNFREEZE),
     (CONFISCATE, RESTRICT), (CONFISCATE, UNFREEZE),
     (CONFISCATE, UNRESTRICT), (CONFISCATE, RELEASE),
     (UNFREEZE, UNRESTRICT), (UNFREEZE, RELEASE),
     (UNRESTRICT, RELEASE)]"

definition noncommuting_pairs :: "(reg_action \<times> reg_action) list" where
  "noncommuting_pairs =
    [(FREEZE, SEIZE), (FREEZE, UNFREEZE), (FREEZE, RELEASE),
     (SEIZE, RESTRICT), (SEIZE, UNRESTRICT), (SEIZE, RELEASE),
     (RESTRICT, UNFREEZE), (RESTRICT, UNRESTRICT), (RESTRICT, RELEASE)]"

definition noncommuting_witnesses ::
  "((reg_action \<times> reg_action) \<times> reg_state) list"
where
  "noncommuting_witnesses =
    [((FREEZE, SEIZE), RESTRICTED),
     ((FREEZE, UNFREEZE), ACTIVE),
     ((FREEZE, RELEASE), SEIZED),
     ((SEIZE, RESTRICT), ACTIVE),
     ((SEIZE, UNRESTRICT), RESTRICTED),
     ((SEIZE, RELEASE), ACTIVE),
     ((RESTRICT, UNFREEZE), FROZEN),
     ((RESTRICT, UNRESTRICT), ACTIVE),
     ((RESTRICT, RELEASE), SEIZED)]"

definition witness_valid ::
  "((reg_action \<times> reg_action) \<times> reg_state) \<Rightarrow> bool"
where
  "witness_valid w =
    (case w of ((a, b), s) \<Rightarrow>
      state_effect (state_effect s a) b \<noteq>
      state_effect (state_effect s b) a)"

lemma pair_commutes_iff:
  "pair_commutes (a, b) \<longleftrightarrow> commutes a b"
  unfolding pair_commutes_def commutes_def all_reg_states_def
  by (auto, case_tac s; auto)

theorem commuting_pairs_complete:
  "filter pair_commutes all_unordered_pairs = commuting_pairs"
  by (simp add: pair_commutes_def all_unordered_pairs_def commuting_pairs_def
      all_reg_states_def state_effect_def legal_outcome_def)

theorem noncommuting_pairs_complete:
  "filter (Not \<circ> pair_commutes) all_unordered_pairs = noncommuting_pairs"
  by (simp add: pair_commutes_def all_unordered_pairs_def noncommuting_pairs_def
      all_reg_states_def state_effect_def legal_outcome_def)

theorem pair_classification_cardinality:
  "length commuting_pairs = 12 \<and>
   length noncommuting_pairs = 9 \<and>
   length all_unordered_pairs = 21"
  by (simp add: commuting_pairs_def noncommuting_pairs_def all_unordered_pairs_def)

theorem noncommuting_witnesses_sound:
  "list_all witness_valid noncommuting_witnesses"
  by (simp add: witness_valid_def noncommuting_witnesses_def
      state_effect_def legal_outcome_def)

theorem noncommuting_witnesses_complete:
  "map fst noncommuting_witnesses = noncommuting_pairs"
  by (simp add: noncommuting_witnesses_def noncommuting_pairs_def)

lemma commuting_pairs_sound:
  assumes "p \<in> set commuting_pairs"
  shows "case p of (a, b) \<Rightarrow> commutes a b"
proof -
  have "p \<in> set (filter pair_commutes all_unordered_pairs)"
    using assms commuting_pairs_complete by simp
  then have "pair_commutes p" by simp
  then show ?thesis
    by (cases p) (simp add: pair_commutes_iff)
qed


section \<open>Terminal Absorption and State Provenance\<close>

theorem confiscated_word_absorbing:
  "run_word as CONFISCATED = CONFISCATED"
proof (induction as)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case
    by (cases a) (simp_all add: state_effect_def legal_outcome_def)
qed

theorem confiscated_word_rejections:
  "snd (action_outcome_queue as CONFISCATED) =
   map (\<lambda>_. Rejected Undefined_Transition) as"
proof (induction as)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case
    by (cases a) (simp_all add: legal_outcome_def Let_def)
qed

theorem concrete_terminal_queue_is_rejected:
  "action_outcome_queue [FREEZE] CONFISCATED =
    (CONFISCATED, [Rejected Undefined_Transition])"
  by (simp add: legal_outcome_def)

lemma frozen_effect_origin:
  "state_effect s a = FROZEN \<Longrightarrow> s = FROZEN \<or> a = FREEZE"
  by (cases s; cases a; simp add: state_effect_def legal_outcome_def)

lemma seized_effect_origin:
  "state_effect s a = SEIZED \<Longrightarrow> s = SEIZED \<or> a = SEIZE"
  by (cases s; cases a; simp add: state_effect_def legal_outcome_def)

lemma confiscated_effect_origin:
  "state_effect s a = CONFISCATED \<Longrightarrow>
   s = CONFISCATED \<or> a = CONFISCATE"
  by (cases s; cases a; simp add: state_effect_def legal_outcome_def)

theorem concrete_provenance_witnesses:
  "state_effect ACTIVE FREEZE = FROZEN \<and>
   state_effect ACTIVE SEIZE = SEIZED \<and>
   state_effect ACTIVE CONFISCATE = CONFISCATED"
  by (simp add: state_effect_def legal_outcome_def)

theorem frozen_word_provenance:
  assumes "run_word as s = FROZEN" and "s \<noteq> FROZEN"
  shows "FREEZE \<in> set as"
  using assms
proof (induction as arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  show ?case
  proof (cases "state_effect s a = FROZEN")
    case True
    have "a = FREEZE"
      using frozen_effect_origin[OF True] Cons.prems(2) by blast
    then show ?thesis by simp
  next
    case False
    have final: "run_word as (state_effect s a) = FROZEN"
      using Cons.prems(1) by simp
    have "FREEZE \<in> set as"
      using Cons.IH[OF final False] .
    then show ?thesis by simp
  qed
qed

theorem seized_word_provenance:
  assumes "run_word as s = SEIZED" and "s \<noteq> SEIZED"
  shows "SEIZE \<in> set as"
  using assms
proof (induction as arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  show ?case
  proof (cases "state_effect s a = SEIZED")
    case True
    have "a = SEIZE"
      using seized_effect_origin[OF True] Cons.prems(2) by blast
    then show ?thesis by simp
  next
    case False
    have final: "run_word as (state_effect s a) = SEIZED"
      using Cons.prems(1) by simp
    have "SEIZE \<in> set as"
      using Cons.IH[OF final False] .
    then show ?thesis by simp
  qed
qed

theorem confiscated_word_provenance:
  assumes "run_word as s = CONFISCATED" and "s \<noteq> CONFISCATED"
  shows "CONFISCATE \<in> set as"
  using assms
proof (induction as arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  show ?case
  proof (cases "state_effect s a = CONFISCATED")
    case True
    have "a = CONFISCATE"
      using confiscated_effect_origin[OF True] Cons.prems(2) by blast
    then show ?thesis by simp
  next
    case False
    have final: "run_word as (state_effect s a) = CONFISCATED"
      using Cons.prems(1) by simp
    have "CONFISCATE \<in> set as"
      using Cons.IH[OF final False] .
    then show ?thesis by simp
  qed
qed


section \<open>Typed Legal-Effect Descriptors\<close>

datatype legal_action_kind =
    Legal_Freeze
  | Legal_Seize
  | Legal_Confiscate
  | Legal_Restrict
  | Legal_Recover
  | Legal_Liquidate

datatype reversibility =
    Reversible
  | Conditional
  | Irreversible
  | Configurable
  | One_Time

datatype ownership_effect =
    Retained
  | Transferred
  | Terminated
  | Restored

datatype finality_effect =
    Provisional
  | Interim_Custodial
  | Final
  | Conditional_Finality
  | Restorative

record legal_effect_descriptor =
  descriptor_reversibility :: reversibility
  descriptor_ownership     :: ownership_effect
  descriptor_finality      :: finality_effect

fun legal_descriptor :: "legal_action_kind \<Rightarrow> legal_effect_descriptor" where
  "legal_descriptor Legal_Freeze =
    \<lparr>descriptor_reversibility = Reversible,
     descriptor_ownership = Retained,
     descriptor_finality = Provisional\<rparr>"
| "legal_descriptor Legal_Seize =
    \<lparr>descriptor_reversibility = Conditional,
     descriptor_ownership = Retained,
     descriptor_finality = Interim_Custodial\<rparr>"
| "legal_descriptor Legal_Confiscate =
    \<lparr>descriptor_reversibility = Irreversible,
     descriptor_ownership = Transferred,
     descriptor_finality = Final\<rparr>"
| "legal_descriptor Legal_Restrict =
    \<lparr>descriptor_reversibility = Configurable,
     descriptor_ownership = Retained,
     descriptor_finality = Conditional_Finality\<rparr>"
| "legal_descriptor Legal_Recover =
    \<lparr>descriptor_reversibility = One_Time,
     descriptor_ownership = Restored,
     descriptor_finality = Restorative\<rparr>"
| "legal_descriptor Legal_Liquidate =
    \<lparr>descriptor_reversibility = Irreversible,
     descriptor_ownership = Terminated,
     descriptor_finality = Final\<rparr>"

fun transition_label_of :: "legal_action_kind \<Rightarrow> reg_action option" where
  "transition_label_of Legal_Freeze = Some FREEZE"
| "transition_label_of Legal_Seize = Some SEIZE"
| "transition_label_of Legal_Confiscate = Some CONFISCATE"
| "transition_label_of Legal_Restrict = Some RESTRICT"
| "transition_label_of Legal_Recover = None"
| "transition_label_of Legal_Liquidate = None"

fun descriptor_target :: "legal_action_kind \<Rightarrow> reg_state option" where
  "descriptor_target Legal_Freeze = Some FROZEN"
| "descriptor_target Legal_Seize = Some SEIZED"
| "descriptor_target Legal_Confiscate = Some CONFISCATED"
| "descriptor_target Legal_Restrict = Some RESTRICTED"
| "descriptor_target Legal_Recover = None"
| "descriptor_target Legal_Liquidate = None"

definition all_legal_actions :: "legal_action_kind list" where
  "all_legal_actions =
    [Legal_Freeze, Legal_Seize, Legal_Confiscate, Legal_Restrict,
     Legal_Recover, Legal_Liquidate]"

theorem legal_action_descriptor_inventory:
  "set all_legal_actions = UNIV \<and>
   length all_legal_actions = 6 \<and>
   inj legal_descriptor"
proof -
  have full: "set all_legal_actions = UNIV"
  proof (rule set_eqI)
    fix x
    show "x \<in> set all_legal_actions \<longleftrightarrow> x \<in> UNIV"
      by (cases x) (simp_all add: all_legal_actions_def)
  qed
  have count: "length all_legal_actions = 6"
    by (simp add: all_legal_actions_def)
  have injection: "inj legal_descriptor"
  proof (rule injI)
    fix x y
    assume "legal_descriptor x = legal_descriptor y"
    then show "x = y" by (cases x; cases y; simp_all)
  qed
  show ?thesis using full count injection by simp
qed

theorem descriptor_transition_compatibility:
  assumes "transition_label_of k = Some a"
      and "reg_transition s a = Some s'"
  shows "descriptor_target k = Some s'"
  using assms
  by (cases k; cases s; auto)

theorem recover_and_liquidate_are_not_state_transitions:
  "transition_label_of Legal_Recover = None \<and>
   transition_label_of Legal_Liquidate = None"
  by simp


section \<open>Ordinary and Enforcement Transfer Gates\<close>

datatype transfer_path =
    Ordinary_Transfer
  | Authorized_Enforcement legal_action_kind

record transfer_request =
  transfer_path_value  :: transfer_path
  baseline_clear       :: bool
  restriction_clear    :: bool
  enforcement_approved :: bool

fun regulatory_state_gate :: "reg_state \<Rightarrow> bool \<Rightarrow> bool" where
  "regulatory_state_gate ACTIVE restriction = True"
| "regulatory_state_gate FROZEN restriction = False"
| "regulatory_state_gate SEIZED restriction = False"
| "regulatory_state_gate CONFISCATED restriction = False"
| "regulatory_state_gate RESTRICTED restriction = restriction"

fun enforcement_transfer_action :: "legal_action_kind \<Rightarrow> bool" where
  "enforcement_transfer_action Legal_Seize = True"
| "enforcement_transfer_action Legal_Confiscate = True"
| "enforcement_transfer_action Legal_Recover = True"
| "enforcement_transfer_action Legal_Liquidate = True"
| "enforcement_transfer_action Legal_Freeze = False"
| "enforcement_transfer_action Legal_Restrict = False"

definition ordinary_transfer_allowed ::
  "bool \<Rightarrow> bool \<Rightarrow> reg_state \<Rightarrow> bool"
where
  "ordinary_transfer_allowed baseline restriction s \<longleftrightarrow>
    baseline \<and> regulatory_state_gate s restriction"

definition transfer_allowed :: "reg_state \<Rightarrow> transfer_request \<Rightarrow> bool" where
  "transfer_allowed s req \<longleftrightarrow>
    (case transfer_path_value req of
       Ordinary_Transfer \<Rightarrow>
         ordinary_transfer_allowed
           (baseline_clear req) (restriction_clear req) s
     | Authorized_Enforcement k \<Rightarrow>
         enforcement_approved req \<and> enforcement_transfer_action k)"

theorem ordinary_transfer_uses_both_gates:
  "transfer_allowed s
      \<lparr>transfer_path_value = Ordinary_Transfer,
       baseline_clear = baseline,
       restriction_clear = restriction,
       enforcement_approved = authorization\<rparr>
   \<longleftrightarrow>
     baseline \<and> regulatory_state_gate s restriction"
  by (simp add: transfer_allowed_def ordinary_transfer_allowed_def)

theorem restricted_transfer_uses_current_condition:
  "transfer_allowed RESTRICTED
     \<lparr>transfer_path_value = Ordinary_Transfer,
      baseline_clear = baseline,
      restriction_clear = restriction,
      enforcement_approved = authorization\<rparr>
   \<longleftrightarrow> baseline \<and> restriction"
  by (simp add: transfer_allowed_def ordinary_transfer_allowed_def)

theorem enforcement_transfer_is_a_separate_path:
  "transfer_allowed s
      \<lparr>transfer_path_value = Authorized_Enforcement k,
       baseline_clear = baseline,
       restriction_clear = restriction,
       enforcement_approved = authorization\<rparr>
   \<longleftrightarrow> authorization \<and> enforcement_transfer_action k"
  by (simp add: transfer_allowed_def)

definition concrete_ordinary_request :: transfer_request where
  "concrete_ordinary_request =
    \<lparr>transfer_path_value = Ordinary_Transfer,
     baseline_clear = True,
     restriction_clear = True,
     enforcement_approved = False\<rparr>"

definition concrete_restricted_request_blocked :: transfer_request where
  "concrete_restricted_request_blocked =
    concrete_ordinary_request\<lparr>restriction_clear := False\<rparr>"

definition concrete_enforcement_request :: transfer_request where
  "concrete_enforcement_request =
    \<lparr>transfer_path_value = Authorized_Enforcement Legal_Recover,
     baseline_clear = False,
     restriction_clear = False,
     enforcement_approved = True\<rparr>"

theorem concrete_gate_premises_activate:
  "transfer_allowed ACTIVE concrete_ordinary_request \<and>
   transfer_allowed RESTRICTED concrete_ordinary_request \<and>
   \<not> transfer_allowed RESTRICTED concrete_restricted_request_blocked \<and>
   \<not> transfer_allowed FROZEN concrete_ordinary_request \<and>
   transfer_allowed FROZEN concrete_enforcement_request"
  by (simp add: concrete_ordinary_request_def
      concrete_restricted_request_blocked_def concrete_enforcement_request_def
      transfer_allowed_def ordinary_transfer_allowed_def)


section \<open>Reference Roundtrips and Information Loss\<close>

theorem freeze_roundtrip:
  "run_word [FREEZE, UNFREEZE] ACTIVE = ACTIVE"
  by (simp add: state_effect_def legal_outcome_def)

theorem seizure_roundtrip:
  "run_word [SEIZE, RELEASE] ACTIVE = ACTIVE"
  by (simp add: state_effect_def legal_outcome_def)

theorem restriction_roundtrip:
  "run_word [RESTRICT, UNRESTRICT] ACTIVE = ACTIVE"
  by (simp add: state_effect_def legal_outcome_def)

theorem restricted_freeze_unfreeze_loses_history:
  "run_word [FREEZE, UNFREEZE] RESTRICTED = ACTIVE \<and>
   run_word [FREEZE, UNFREEZE] RESTRICTED \<noteq> RESTRICTED"
  by (simp add: state_effect_def legal_outcome_def)


section \<open>Commands, Trace, and Frame Properties\<close>

datatype execution_status =
    Ready
  | Failed operational_failure_reason

record regulatory_command =
  command_identity :: nat
  command_asset    :: asset_id
  command_actor    :: nat
  command_source   :: chain_id
  command_action   :: reg_action
  command_status   :: execution_status

record trace_event =
  event_identity       :: nat
  event_asset          :: asset_id
  event_actor          :: nat
  event_source         :: chain_id
  event_action         :: reg_action
  event_previous_state :: "reg_state option"
  event_outcome        :: command_outcome

definition event_for ::
  "regulatory_command \<Rightarrow> reg_state option \<Rightarrow> command_outcome \<Rightarrow> trace_event"
where
  "event_for cmd previous out =
    \<lparr>event_identity = command_identity cmd,
     event_asset = command_asset cmd,
     event_actor = command_actor cmd,
     event_source = command_source cmd,
     event_action = command_action cmd,
     event_previous_state = previous,
     event_outcome = out\<rparr>"

definition execute_command ::
  "reg_state \<Rightarrow> regulatory_command \<Rightarrow> reg_state \<times> trace_event"
where
  "execute_command s cmd =
    (case command_status cmd of
       Failed reason \<Rightarrow>
         (s, event_for cmd (Some s) (Operational_Failure reason))
     | Ready \<Rightarrow>
         (let out = legal_outcome s (command_action cmd)
          in (state_after s out, event_for cmd (Some s) out)))"

(* This fold models one regulatory-state cell.  Its public theorem below uses
   only trace order and length; asset-indexed effects are handled separately. *)
fun run_command_queue ::
  "regulatory_command list \<Rightarrow> reg_state \<Rightarrow> reg_state \<times> trace_event list"
where
  "run_command_queue [] s = (s, [])"
| "run_command_queue (cmd # cmds) s =
     (let first = execute_command s cmd;
          rest = run_command_queue cmds (fst first)
      in (fst rest, snd first # snd rest))"

theorem command_queue_preserves_order_and_length:
  "map event_identity (snd (run_command_queue cmds s)) =
     map command_identity cmds \<and>
   length (snd (run_command_queue cmds s)) = length cmds"
proof (induction cmds arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons cmd cmds)
  then show ?case
    by (cases "command_status cmd")
       (simp_all add: execute_command_def event_for_def Let_def)
qed

theorem command_trace_preserves_input:
  "event_identity (snd (execute_command s cmd)) = command_identity cmd \<and>
   event_asset (snd (execute_command s cmd)) = command_asset cmd \<and>
   event_actor (snd (execute_command s cmd)) = command_actor cmd \<and>
   event_source (snd (execute_command s cmd)) = command_source cmd \<and>
   event_action (snd (execute_command s cmd)) = command_action cmd"
  by (cases "command_status cmd")
     (simp_all add: execute_command_def event_for_def Let_def)

theorem command_trace_records_execution_outcome:
  "event_outcome (snd (execute_command s cmd)) =
    (case command_status cmd of
       Failed reason \<Rightarrow> Operational_Failure reason
     | Ready \<Rightarrow> legal_outcome s (command_action cmd))"
  by (cases "command_status cmd")
     (simp_all add: execute_command_def event_for_def Let_def)

type_synonym asset_store = "asset_id \<Rightarrow> reg_state"

definition execute_on_store ::
  "regulatory_command \<Rightarrow> asset_store \<Rightarrow> asset_store \<times> trace_event"
where
  "execute_on_store cmd store =
    (let result = execute_command (store (command_asset cmd)) cmd
     in (store(command_asset cmd := fst result), snd result))"

theorem other_asset_unchanged:
  assumes "other \<noteq> command_asset cmd"
  shows "fst (execute_on_store cmd store) other = store other"
  using assms by (simp add: execute_on_store_def Let_def)

definition concrete_message :: regulatory_command where
  "concrete_message =
    \<lparr>command_identity = 1001,
     command_asset = 7,
     command_actor = 42,
     command_source = 3,
     command_action = FREEZE,
     command_status = Ready\<rparr>"

definition repeated_message :: regulatory_command where
  "repeated_message = concrete_message\<lparr>command_identity := 1002\<rparr>"

theorem concrete_message_premises_activate:
  "command_status concrete_message = Ready \<and>
   reg_transition ACTIVE (command_action concrete_message) = Some FROZEN \<and>
   execute_command ACTIVE concrete_message =
     (FROZEN, event_for concrete_message (Some ACTIVE) (Applied FROZEN))"
  by (simp add: concrete_message_def execute_command_def legal_outcome_def Let_def)

theorem repeated_message_has_idempotent_state_and_distinct_trace:
  "fst (execute_command FROZEN repeated_message) = FROZEN \<and>
   event_outcome (snd (execute_command FROZEN repeated_message)) =
     Rejected Undefined_Transition \<and>
   snd (execute_command ACTIVE concrete_message) \<noteq>
     snd (execute_command FROZEN repeated_message)"
  by (simp add: concrete_message_def repeated_message_def execute_command_def
      event_for_def legal_outcome_def Let_def)


section \<open>Atomic Synchronization Queues\<close>

definition execute_sync_command ::
  "regulatory_command \<Rightarrow> global_state \<Rightarrow> global_state \<times> trace_event"
where
  "execute_sync_command cmd gs =
    (case command_status cmd of
       Failed reason \<Rightarrow>
         (gs, event_for cmd
           (get_reg_state gs (command_source cmd) (command_asset cmd))
           (Operational_Failure reason))
     | Ready \<Rightarrow>
         (case get_reg_state gs (command_source cmd) (command_asset cmd) of
            None \<Rightarrow>
              (gs, event_for cmd None (Operational_Failure Missing_Asset))
          | Some s \<Rightarrow>
              (case reg_transition s (command_action cmd) of
                 None \<Rightarrow>
                   (gs, event_for cmd (Some s)
                     (Rejected Undefined_Transition))
               | Some s' \<Rightarrow>
                   (case sync (command_source cmd) (command_action cmd)
                     (command_asset cmd) gs of
                      None \<Rightarrow>
                        (gs, event_for cmd (Some s)
                          (Operational_Failure Lock_Unavailable))
                    | Some gs' \<Rightarrow>
                        (gs', event_for cmd (Some s) (Applied s'))))))"

lemma sync_command_preserves_valid_state:
  assumes "valid_state gs"
  shows "valid_state (fst (execute_sync_command cmd gs))"
proof (cases "command_status cmd")
  case (Failed reason)
  then show ?thesis
    using assms by (simp add: execute_sync_command_def)
next
  case Ready
  show ?thesis
  proof (cases "get_reg_state gs (command_source cmd) (command_asset cmd)")
    case None
    note current = None
    with Ready assms show ?thesis
      by (simp add: execute_sync_command_def)
  next
    case (Some s)
    note current = Some
    show ?thesis
    proof (cases "reg_transition s (command_action cmd)")
      case None
      note transition = None
      with Ready current assms show ?thesis
        by (simp add: execute_sync_command_def)
    next
      case (Some s')
      note transition = Some
      show ?thesis
      proof (cases "sync (command_source cmd) (command_action cmd)
          (command_asset cmd) gs")
        case None
        note synced = None
        with Ready current transition assms show ?thesis
          by (simp add: execute_sync_command_def)
      next
        case (Some gs')
        note synced = Some
        have "valid_state gs'"
          using valid_state_preservation[OF assms current transition synced] .
        with Ready current transition synced show ?thesis
          by (simp add: execute_sync_command_def)
      qed
    qed
  qed
qed

fun run_sync_queue ::
  "regulatory_command list \<Rightarrow> global_state \<Rightarrow> global_state \<times> trace_event list"
where
  "run_sync_queue [] gs = (gs, [])"
| "run_sync_queue (cmd # cmds) gs =
     (let first = execute_sync_command cmd gs;
          rest = run_sync_queue cmds (fst first)
      in (fst rest, snd first # snd rest))"

theorem sync_queue_preserves_valid_state:
  assumes "valid_state gs"
  shows "valid_state (fst (run_sync_queue cmds gs))"
  using assms
proof (induction cmds arbitrary: gs)
  case Nil
  then show ?case by simp
next
  case (Cons cmd cmds)
  have first: "valid_state (fst (execute_sync_command cmd gs))"
    using sync_command_preserves_valid_state[OF Cons.prems] .
  have rest:
    "valid_state (fst (run_sync_queue cmds
      (fst (execute_sync_command cmd gs))))"
    using Cons.IH[OF first] .
  then show ?case by (simp add: Let_def)
qed

fun completed_states ::
  "regulatory_command list \<Rightarrow> global_state \<Rightarrow> global_state list"
where
  "completed_states [] gs = [gs]"
| "completed_states (cmd # cmds) gs =
     gs # completed_states cmds (fst (execute_sync_command cmd gs))"

theorem completed_states_are_valid:
  assumes "valid_state gs"
  shows "list_all valid_state (completed_states cmds gs)"
  using assms
proof (induction cmds arbitrary: gs)
  case Nil
  then show ?case by simp
next
  case (Cons cmd cmds)
  have next_valid: "valid_state (fst (execute_sync_command cmd gs))"
    using sync_command_preserves_valid_state[OF Cons.prems] .
  then show ?case using Cons.IH Cons.prems by simp
qed

theorem completed_prefixes_are_consistent:
  assumes "valid_state gs"
  shows "list_all consistent_state (completed_states cmds gs)"
  using completed_states_are_valid[OF assms]
  unfolding valid_state_def list_all_iff by blast

definition concrete_global_state :: global_state where
  "concrete_global_state =
    \<lparr>gs_chains = (\<lambda>cid aid.
       if cid = 0 \<and> aid = 0 then Some \<lparr>as_reg_state = ACTIVE\<rparr>
       else None),
     gs_locks = (\<lambda>_. False)\<rparr>"

definition concrete_sync_command :: regulatory_command where
  "concrete_sync_command =
    \<lparr>command_identity = 2001,
     command_asset = 0,
     command_actor = 9,
     command_source = 0,
     command_action = FREEZE,
     command_status = Ready\<rparr>"

lemma concrete_global_state_get_reg:
  "get_reg_state concrete_global_state cid aid =
    (if cid = 0 \<and> aid = 0 then Some ACTIVE else None)"
  by (simp add: concrete_global_state_def get_reg_state_def get_asset_state_def
      split: if_splits)

lemma concrete_global_state_valid:
  "valid_state concrete_global_state"
proof -
  have "consistent_state concrete_global_state"
    unfolding consistent_state_def
    by (auto simp: concrete_global_state_get_reg split: if_splits)
  moreover have "no_locked_without_reason concrete_global_state"
    by (simp add: no_locked_without_reason_def is_locked_def
        concrete_global_state_def)
  ultimately show ?thesis by (simp add: valid_state_def)
qed

theorem concrete_sync_premises_activate:
  "valid_state concrete_global_state \<and>
   get_reg_state concrete_global_state 0 0 = Some ACTIVE \<and>
   reg_transition ACTIVE FREEZE = Some FROZEN \<and>
   event_outcome (snd (execute_sync_command concrete_sync_command
     concrete_global_state)) = Applied FROZEN \<and>
   get_reg_state (fst (execute_sync_command concrete_sync_command
     concrete_global_state)) 0 0 = Some FROZEN"
proof -
  have valid: "valid_state concrete_global_state"
    using concrete_global_state_valid .
  have current:
    "get_reg_state concrete_global_state 0 0 = Some ACTIVE"
    by (simp add: concrete_global_state_get_reg)
  have applied:
    "event_outcome (snd (execute_sync_command concrete_sync_command
      concrete_global_state)) = Applied FROZEN"
    by (simp add: concrete_global_state_def concrete_sync_command_def
        execute_sync_command_def sync_def get_reg_state_def get_asset_state_def
        acquire_lock_def is_locked_def connected_chains_def asset_exists_def
        update_all_chains_def release_lock_def event_for_def Let_def)
  have final:
    "get_reg_state (fst (execute_sync_command concrete_sync_command
      concrete_global_state)) 0 0 = Some FROZEN"
    by (simp add: concrete_global_state_def concrete_sync_command_def
        execute_sync_command_def sync_def get_reg_state_def get_asset_state_def
        acquire_lock_def is_locked_def connected_chains_def asset_exists_def
        update_all_chains_def release_lock_def event_for_def Let_def)
  show ?thesis using valid current applied final by simp
qed


section \<open>Finite Transformation Normal Forms\<close>

definition state_vector :: "reg_action list \<Rightarrow> reg_state list" where
  "state_vector as = map (run_word as) all_reg_states"

definition vector_step ::
  "reg_state list \<Rightarrow> reg_action \<Rightarrow> reg_state list"
where
  "vector_step v a = map (\<lambda>s. state_effect s a) v"

definition normal_forms :: "reg_state list list" where
  "normal_forms =
    [[ACTIVE, FROZEN, SEIZED, CONFISCATED, RESTRICTED],
     [CONFISCATED, CONFISCATED, CONFISCATED, CONFISCATED, CONFISCATED],
     [FROZEN, FROZEN, SEIZED, CONFISCATED, FROZEN],
     [ACTIVE, FROZEN, ACTIVE, CONFISCATED, RESTRICTED],
     [RESTRICTED, FROZEN, SEIZED, CONFISCATED, RESTRICTED],
     [SEIZED, SEIZED, SEIZED, CONFISCATED, RESTRICTED],
     [ACTIVE, ACTIVE, SEIZED, CONFISCATED, RESTRICTED],
     [ACTIVE, FROZEN, SEIZED, CONFISCATED, ACTIVE],
     [FROZEN, FROZEN, ACTIVE, CONFISCATED, FROZEN],
     [SEIZED, SEIZED, SEIZED, CONFISCATED, SEIZED],
     [ACTIVE, ACTIVE, SEIZED, CONFISCATED, ACTIVE],
     [FROZEN, FROZEN, FROZEN, CONFISCATED, FROZEN],
     [RESTRICTED, FROZEN, RESTRICTED, CONFISCATED, RESTRICTED],
     [RESTRICTED, FROZEN, ACTIVE, CONFISCATED, RESTRICTED],
     [RESTRICTED, SEIZED, SEIZED, CONFISCATED, RESTRICTED],
     [RESTRICTED, ACTIVE, SEIZED, CONFISCATED, RESTRICTED],
     [SEIZED, SEIZED, SEIZED, CONFISCATED, FROZEN],
     [ACTIVE, ACTIVE, ACTIVE, CONFISCATED, RESTRICTED],
     [SEIZED, SEIZED, SEIZED, CONFISCATED, ACTIVE],
     [RESTRICTED, RESTRICTED, SEIZED, CONFISCATED, RESTRICTED],
     [ACTIVE, FROZEN, ACTIVE, CONFISCATED, ACTIVE],
     [FROZEN, FROZEN, RESTRICTED, CONFISCATED, FROZEN],
     [ACTIVE, ACTIVE, ACTIVE, CONFISCATED, ACTIVE],
     [RESTRICTED, SEIZED, RESTRICTED, CONFISCATED, RESTRICTED],
     [RESTRICTED, ACTIVE, RESTRICTED, CONFISCATED, RESTRICTED],
     [FROZEN, SEIZED, SEIZED, CONFISCATED, FROZEN],
     [RESTRICTED, ACTIVE, ACTIVE, CONFISCATED, RESTRICTED],
     [ACTIVE, SEIZED, SEIZED, CONFISCATED, ACTIVE],
     [ACTIVE, ACTIVE, ACTIVE, CONFISCATED, FROZEN],
     [RESTRICTED, RESTRICTED, RESTRICTED, CONFISCATED, RESTRICTED],
     [RESTRICTED, RESTRICTED, ACTIVE, CONFISCATED, RESTRICTED],
     [SEIZED, SEIZED, RESTRICTED, CONFISCATED, SEIZED],
     [ACTIVE, ACTIVE, RESTRICTED, CONFISCATED, ACTIVE],
     [FROZEN, SEIZED, FROZEN, CONFISCATED, FROZEN],
     [ACTIVE, SEIZED, ACTIVE, CONFISCATED, ACTIVE],
     [FROZEN, ACTIVE, ACTIVE, CONFISCATED, FROZEN],
     [RESTRICTED, RESTRICTED, RESTRICTED, CONFISCATED, FROZEN],
     [SEIZED, SEIZED, FROZEN, CONFISCATED, SEIZED],
     [SEIZED, SEIZED, ACTIVE, CONFISCATED, SEIZED],
     [FROZEN, ACTIVE, FROZEN, CONFISCATED, FROZEN],
     [FROZEN, RESTRICTED, RESTRICTED, CONFISCATED, FROZEN],
     [RESTRICTED, RESTRICTED, RESTRICTED, CONFISCATED, SEIZED],
     [RESTRICTED, RESTRICTED, RESTRICTED, CONFISCATED, ACTIVE],
     [ACTIVE, ACTIVE, FROZEN, CONFISCATED, ACTIVE],
     [FROZEN, RESTRICTED, FROZEN, CONFISCATED, FROZEN],
     [SEIZED, RESTRICTED, RESTRICTED, CONFISCATED, SEIZED],
     [ACTIVE, RESTRICTED, RESTRICTED, CONFISCATED, ACTIVE],
     [FROZEN, FROZEN, FROZEN, CONFISCATED, SEIZED],
     [ACTIVE, ACTIVE, ACTIVE, CONFISCATED, SEIZED],
     [RESTRICTED, RESTRICTED, FROZEN, CONFISCATED, RESTRICTED],
     [SEIZED, RESTRICTED, SEIZED, CONFISCATED, SEIZED],
     [ACTIVE, RESTRICTED, ACTIVE, CONFISCATED, ACTIVE],
     [SEIZED, FROZEN, FROZEN, CONFISCATED, SEIZED],
     [SEIZED, ACTIVE, ACTIVE, CONFISCATED, SEIZED],
     [FROZEN, FROZEN, FROZEN, CONFISCATED, ACTIVE],
     [SEIZED, FROZEN, SEIZED, CONFISCATED, SEIZED],
     [SEIZED, ACTIVE, SEIZED, CONFISCATED, SEIZED],
     [ACTIVE, FROZEN, FROZEN, CONFISCATED, ACTIVE],
     [FROZEN, FROZEN, FROZEN, CONFISCATED, RESTRICTED],
     [RESTRICTED, FROZEN, FROZEN, CONFISCATED, RESTRICTED]]"

definition normal_form_words :: "reg_action list list" where
  "normal_form_words =
    [[],
     [CONFISCATE],
     [FREEZE],
     [RELEASE],
     [RESTRICT],
     [SEIZE],
     [UNFREEZE],
     [UNRESTRICT],
     [FREEZE, RELEASE],
     [FREEZE, SEIZE],
     [FREEZE, UNFREEZE],
     [RELEASE, FREEZE],
     [RELEASE, RESTRICT],
     [RESTRICT, RELEASE],
     [RESTRICT, SEIZE],
     [RESTRICT, UNFREEZE],
     [SEIZE, FREEZE],
     [SEIZE, RELEASE],
     [SEIZE, UNRESTRICT],
     [UNFREEZE, RESTRICT],
     [UNRESTRICT, RELEASE],
     [FREEZE, RELEASE, RESTRICT],
     [FREEZE, SEIZE, RELEASE],
     [RELEASE, RESTRICT, SEIZE],
     [RELEASE, RESTRICT, UNFREEZE],
     [RESTRICT, SEIZE, FREEZE],
     [RESTRICT, SEIZE, RELEASE],
     [RESTRICT, SEIZE, UNRESTRICT],
     [SEIZE, FREEZE, RELEASE],
     [SEIZE, RELEASE, RESTRICT],
     [UNFREEZE, RESTRICT, RELEASE],
     [FREEZE, RELEASE, RESTRICT, SEIZE],
     [FREEZE, RELEASE, RESTRICT, UNFREEZE],
     [RELEASE, RESTRICT, SEIZE, FREEZE],
     [RELEASE, RESTRICT, SEIZE, UNRESTRICT],
     [RESTRICT, SEIZE, FREEZE, RELEASE],
     [SEIZE, FREEZE, RELEASE, RESTRICT],
     [FREEZE, RELEASE, RESTRICT, SEIZE, FREEZE],
     [FREEZE, RELEASE, RESTRICT, SEIZE, UNRESTRICT],
     [RELEASE, RESTRICT, SEIZE, FREEZE, RELEASE],
     [RESTRICT, SEIZE, FREEZE, RELEASE, RESTRICT],
     [SEIZE, FREEZE, RELEASE, RESTRICT, SEIZE],
     [SEIZE, FREEZE, RELEASE, RESTRICT, UNFREEZE],
     [FREEZE, RELEASE, RESTRICT, SEIZE, FREEZE, RELEASE],
     [RELEASE, RESTRICT, SEIZE, FREEZE, RELEASE, RESTRICT],
     [RESTRICT, SEIZE, FREEZE, RELEASE, RESTRICT, SEIZE],
     [RESTRICT, SEIZE, FREEZE, RELEASE, RESTRICT, UNFREEZE],
     [SEIZE, FREEZE, RELEASE, RESTRICT, SEIZE, FREEZE],
     [SEIZE, FREEZE, RELEASE, RESTRICT, SEIZE, UNRESTRICT],
     [FREEZE, RELEASE, RESTRICT, SEIZE, FREEZE, RELEASE, RESTRICT],
     [RELEASE, RESTRICT, SEIZE, FREEZE, RELEASE, RESTRICT, SEIZE],
     [RELEASE, RESTRICT, SEIZE, FREEZE, RELEASE, RESTRICT, UNFREEZE],
     [RESTRICT, SEIZE, FREEZE, RELEASE, RESTRICT, SEIZE, FREEZE],
     [RESTRICT, SEIZE, FREEZE, RELEASE, RESTRICT, SEIZE, UNRESTRICT],
     [SEIZE, FREEZE, RELEASE, RESTRICT, SEIZE, FREEZE, RELEASE],
     [RELEASE, RESTRICT, SEIZE, FREEZE, RELEASE, RESTRICT, SEIZE, FREEZE],
     [RELEASE, RESTRICT, SEIZE, FREEZE, RELEASE, RESTRICT, SEIZE, UNRESTRICT],
     [RESTRICT, SEIZE, FREEZE, RELEASE, RESTRICT, SEIZE, FREEZE, RELEASE],
     [SEIZE, FREEZE, RELEASE, RESTRICT, SEIZE, FREEZE, RELEASE, RESTRICT],
     [RESTRICT, SEIZE, FREEZE, RELEASE, RESTRICT, SEIZE, FREEZE, RELEASE,
       RESTRICT]]"

lemma normal_form_words_evaluate:
  "map state_vector normal_form_words = normal_forms"
  by (simp add: normal_form_words_def normal_forms_def state_vector_def
      all_reg_states_def state_effect_def legal_outcome_def)

theorem normal_forms_reachable:
  assumes "v \<in> set normal_forms"
  shows "\<exists>as \<in> set normal_form_words. state_vector as = v"
proof -
  have "v \<in> set (map state_vector normal_form_words)"
    using assms by (simp add: normal_form_words_evaluate)
  then show ?thesis by auto
qed

theorem normal_forms_cardinality:
  "length normal_forms = 60"
  by (simp add: normal_forms_def)

lemma normal_forms_closed_freeze:
  assumes "v \<in> set normal_forms"
  shows "vector_step v FREEZE \<in> set normal_forms"
  using assms by (auto simp: normal_forms_def vector_step_def
      state_effect_def legal_outcome_def)

lemma normal_forms_closed_seize:
  assumes "v \<in> set normal_forms"
  shows "vector_step v SEIZE \<in> set normal_forms"
  using assms by (auto simp: normal_forms_def vector_step_def
      state_effect_def legal_outcome_def)

lemma normal_forms_closed_confiscate:
  assumes "v \<in> set normal_forms"
  shows "vector_step v CONFISCATE \<in> set normal_forms"
  using assms by (auto simp: normal_forms_def vector_step_def
      state_effect_def legal_outcome_def)

lemma normal_forms_closed_restrict:
  assumes "v \<in> set normal_forms"
  shows "vector_step v RESTRICT \<in> set normal_forms"
  using assms by (auto simp: normal_forms_def vector_step_def
      state_effect_def legal_outcome_def)

lemma normal_forms_closed_unfreeze:
  assumes "v \<in> set normal_forms"
  shows "vector_step v UNFREEZE \<in> set normal_forms"
  using assms by (auto simp: normal_forms_def vector_step_def
      state_effect_def legal_outcome_def)

lemma normal_forms_closed_unrestrict:
  assumes "v \<in> set normal_forms"
  shows "vector_step v UNRESTRICT \<in> set normal_forms"
  using assms by (auto simp: normal_forms_def vector_step_def
      state_effect_def legal_outcome_def)

lemma normal_forms_closed_release:
  assumes "v \<in> set normal_forms"
  shows "vector_step v RELEASE \<in> set normal_forms"
  using assms by (auto simp: normal_forms_def vector_step_def
      state_effect_def legal_outcome_def)

theorem normal_forms_closed:
  assumes "v \<in> set normal_forms"
  shows "vector_step v a \<in> set normal_forms"
  using assms
  by (cases a)
     (simp_all add: normal_forms_closed_freeze normal_forms_closed_seize
       normal_forms_closed_confiscate normal_forms_closed_restrict
       normal_forms_closed_unfreeze normal_forms_closed_unrestrict
       normal_forms_closed_release)

lemma state_vector_append:
  "state_vector (as @ [a]) = vector_step (state_vector as) a"
  unfolding state_vector_def vector_step_def
  by (simp add: run_word_append all_reg_states_def)

theorem every_word_has_normal_form:
  "state_vector as \<in> set normal_forms"
proof (induction as rule: rev_induct)
  case Nil
  then show ?case
    unfolding state_vector_def normal_forms_def all_reg_states_def by simp
next
  case (snoc a as)
  have "vector_step (state_vector as) a \<in> set normal_forms"
    using normal_forms_closed[OF snoc.IH] .
  then show ?case using state_vector_append by simp
qed

theorem normal_forms_are_distinct:
  "distinct normal_forms"
  by (simp add: normal_forms_def)

end
