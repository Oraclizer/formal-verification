(*
  Title:      Cross_Domain_State_Preservation/Regulatory_Instance.thy
  Author:     Jinwook Kim (Jay) <jay@oraclizer.io>
  Maintainer: Jinwook Kim (Jay) <jay@oraclizer.io>
  License:    BSD

  Regulatory Domain Instance of the Cross-Domain State Preservation Functor

  This theory instantiates the generic locales from State_Preservation.thy
  with the regulatory state model of Oraclizer, a state synchronization
  oracle for tokenized assets across blockchain networks and off-chain
  ledgers.

  Regulatory states: ACTIVE, FROZEN, SEIZED, CONFISCATED, RESTRICTED
  Regulatory actions: FREEZE, SEIZE, CONFISCATE, RESTRICT, UNFREEZE, UNRESTRICT, RELEASE

  Locale instantiations provided in this theory:
    1. state_machine (reg_sm): the regulatory transition system satisfies
       the generic state_machine locale.
    2. state_preservation (escalation_preservation): a heterogeneous-action
       instance modelling the case where two chains share a regulatory
       state representation but have asymmetric on-chain action vocabularies.
       The source chain supports the full seven-action set, while the target
       chain only supports the four escalation actions (FREEZE, SEIZE,
       CONFISCATE, RESTRICT). De-escalation actions are out of scope on the
       target side (handled exclusively by separate judicial procedures in
       that jurisdiction). This instance exercises the locale's actions_s
       parameter as a strict subset of the source action type, together with
       the heterogeneous source/target action types ('a vs 'b) of the
       locale signature.
    3. symmetric_state_preservation (onchain_daml_bridge): a layer-crossing
       instance modelling the bidirectional binding between an on-chain
       enum representation (reg_state, five values) and an off-chain DAML
       structured permission record (daml_perm, status_tag plus auxiliary
       fields seized_by and restriction_scope). The action vocabularies on
       the two layers coincide, so action_map = id; the non-trivial content
       lives in the layer-crossing state mapping. A type-level invariant
       (valid_daml_perm) ties the auxiliary fields to the status tag; the
       bijection itself is between reg_state and the image of the
       representation map (daml_states).
    4. multi_domain_preservation (reg_multi_domain_instantiation): the
       generic multi-domain locale applies parametrically to the regulatory
       model for any finite set of chain identifiers and any global state
       satisfying valid_state.

  Key results:
    - Invariants: I1 (CONFISCATED terminal), I2 (CONFISCATE universally
      reachable), I3 (determinism inherent from fun definition).
    - Transition exclusions with legal justification:
        SEIZED → FROZEN (SEIZED is a strictly stronger constraint).
        FROZEN → RESTRICTED (must return to ACTIVE first).
    - Synchronization correctness: regulatory_homomorphism (after sync, all
      connected chains agree); sync_isolation (other assets unaffected);
      preemptive locking guards the sync function (a second acquire while the
      lock is held fails), expressing the intended exclusion of competing
      regulatory actions under the atomic model (no dynamic serialisation).
    - valid_state_preservation: sync preserves the global validity invariant
      (consistent_state and no_locked_without_reason).

  Design decisions (justified by legal precedence and operational scope):
    - RECOVER and LIQUIDATE excluded from reg_action (force transfer / external
      DEX semantics, not state transitions; modelled at a different layer).
    - SEIZED → FROZEN excluded (legally, SEIZED is a stronger constraint).
    - FROZEN → RESTRICTED excluded (must go through ACTIVE).
    - Locking scope: the guard expresses the intended exclusion of competing
      regulatory actions (atomic model, no interleaving to serialise), not
      double-spend prevention.
*)

theory Regulatory_Instance
  imports State_Preservation
begin

section \<open>Regulatory State and Action Definitions\<close>

datatype reg_state = ACTIVE | FROZEN | SEIZED | CONFISCATED | RESTRICTED

datatype reg_action = FREEZE | SEIZE | CONFISCATE | RESTRICT
                    | UNFREEZE | UNRESTRICT | RELEASE

text \<open>
  The seven constructors are the four escalation actions (\<^const>\<open>FREEZE\<close>,
  \<^const>\<open>SEIZE\<close>, \<^const>\<open>CONFISCATE\<close>, \<^const>\<open>RESTRICT\<close>) and their
  de-escalation counterparts (\<^const>\<open>UNFREEZE\<close>, \<^const>\<open>UNRESTRICT\<close>,
  \<^const>\<open>RELEASE\<close>).  RECOVER and LIQUIDATE, two of the product's six
  enforcement actions, are excluded from \<open>reg_action\<close>: they involve force
  transfers or external DEX interactions rather than regulatory state
  transitions, and are modelled at a different layer.
\<close>

text \<open>
  The regulatory transition function. Partial: returns None for invalid
  (state, action) combinations. The transition table encodes legal
  precedence: seizure is stronger than freezing, confiscation is terminal
  and universally reachable, and intermediate states must return to
  Active before lateral transitions.
\<close>

fun reg_transition :: "reg_state \<Rightarrow> reg_action \<Rightarrow> reg_state option" where
  \<comment> \<open>From ACTIVE: all forward actions valid\<close>
  "reg_transition ACTIVE FREEZE      = Some FROZEN"
| "reg_transition ACTIVE SEIZE       = Some SEIZED"
| "reg_transition ACTIVE CONFISCATE  = Some CONFISCATED"
| "reg_transition ACTIVE RESTRICT    = Some RESTRICTED"
| "reg_transition ACTIVE UNFREEZE    = None"
| "reg_transition ACTIVE UNRESTRICT  = None"
| "reg_transition ACTIVE RELEASE     = None"
  \<comment> \<open>From FROZEN: unfreeze, escalate to SEIZED or CONFISCATED\<close>
| "reg_transition FROZEN UNFREEZE    = Some ACTIVE"
| "reg_transition FROZEN SEIZE       = Some SEIZED"
| "reg_transition FROZEN CONFISCATE  = Some CONFISCATED"
| "reg_transition FROZEN FREEZE      = None"
| "reg_transition FROZEN RESTRICT    = None"
| "reg_transition FROZEN UNRESTRICT  = None"
| "reg_transition FROZEN RELEASE     = None"
  \<comment> \<open>From SEIZED: release or final confiscation only\<close>
| "reg_transition SEIZED RELEASE     = Some ACTIVE"
| "reg_transition SEIZED CONFISCATE  = Some CONFISCATED"
| "reg_transition SEIZED FREEZE      = None"
| "reg_transition SEIZED SEIZE       = None"
| "reg_transition SEIZED RESTRICT    = None"
| "reg_transition SEIZED UNFREEZE    = None"
| "reg_transition SEIZED UNRESTRICT  = None"
  \<comment> \<open>From CONFISCATED: terminal — no transitions out\<close>
| "reg_transition CONFISCATED FREEZE      = None"
| "reg_transition CONFISCATED SEIZE       = None"
| "reg_transition CONFISCATED CONFISCATE  = None"
| "reg_transition CONFISCATED RESTRICT    = None"
| "reg_transition CONFISCATED UNFREEZE    = None"
| "reg_transition CONFISCATED UNRESTRICT  = None"
| "reg_transition CONFISCATED RELEASE     = None"
  \<comment> \<open>From RESTRICTED: unrestrict, escalate to FROZEN or CONFISCATED\<close>
| "reg_transition RESTRICTED UNRESTRICT  = Some ACTIVE"
| "reg_transition RESTRICTED FREEZE      = Some FROZEN"
| "reg_transition RESTRICTED CONFISCATE  = Some CONFISCATED"
| "reg_transition RESTRICTED RESTRICT    = None"
| "reg_transition RESTRICTED SEIZE       = None"
| "reg_transition RESTRICTED UNFREEZE    = None"
| "reg_transition RESTRICTED RELEASE     = None"


section \<open>Fundamental Properties of the Transition Function\<close>

subsection \<open>Invariant I1: CONFISCATED is terminal\<close>

lemma confiscated_terminal:
  "reg_transition CONFISCATED a = None"
  by (cases a) auto

subsection \<open>Invariant I2: CONFISCATE reaches CONFISCATED from any non-terminal state\<close>

lemma confiscate_universal:
  "s \<noteq> CONFISCATED \<Longrightarrow> reg_transition s CONFISCATE = Some CONFISCATED"
  by (cases s) auto

subsection \<open>Invariant I3: Determinism (inherent from function definition)\<close>

text \<open>Determinism follows directly from the \<^theory_text>\<open>fun\<close> definition.\<close>

subsection \<open>SEIZED to FROZEN exclusion\<close>

text \<open>
  SEIZED is a strictly stronger constraint than FROZEN. Direct
  transition from SEIZED to FROZEN is legally nonsensical (cannot
  "weaken" a court-ordered seizure to a mere freeze). The path
  is: RELEASE then ACTIVE then FREEZE.
\<close>

lemma seized_no_freeze:
  "reg_transition SEIZED FREEZE = None"
  by simp

lemma seized_no_unfreeze:
  "reg_transition SEIZED UNFREEZE = None"
  by simp

lemma seized_no_restrict:
  "reg_transition SEIZED RESTRICT = None"
  by simp

subsection \<open>FROZEN to RESTRICTED exclusion\<close>

text \<open>Must go through ACTIVE: UNFREEZE then ACTIVE then RESTRICT.\<close>

lemma frozen_no_restrict:
  "reg_transition FROZEN RESTRICT = None"
  by simp

subsection \<open>Transition completeness: every non-terminal state has at least one valid action\<close>

lemma non_terminal_has_action:
  assumes "s \<noteq> CONFISCATED"
  shows "\<exists>a. reg_transition s a \<noteq> None"
proof (cases s)
  case ACTIVE
  show ?thesis
    apply (rule exI[where x=FREEZE])
    using ACTIVE by simp
next
  case FROZEN
  show ?thesis
    apply (rule exI[where x=UNFREEZE])
    using FROZEN by simp
next
  case SEIZED
  show ?thesis
    apply (rule exI[where x=RELEASE])
    using SEIZED by simp
next
  case CONFISCATED
  then show ?thesis using assms by contradiction
next
  case RESTRICTED
  show ?thesis
    apply (rule exI[where x=UNRESTRICT])
    using RESTRICTED by simp
qed

subsection \<open>Reachability from ACTIVE\<close>

text \<open>Every state is reachable from ACTIVE via some sequence of actions.\<close>

lemma active_reaches_frozen: "reg_transition ACTIVE FREEZE = Some FROZEN"
  by simp

lemma active_reaches_seized: "reg_transition ACTIVE SEIZE = Some SEIZED"
  by simp

lemma active_reaches_confiscated: "reg_transition ACTIVE CONFISCATE = Some CONFISCATED"
  by simp

lemma active_reaches_restricted: "reg_transition ACTIVE RESTRICT = Some RESTRICTED"
  by simp

subsection \<open>Return paths to ACTIVE\<close>

lemma frozen_returns: "reg_transition FROZEN UNFREEZE = Some ACTIVE"
  by simp

lemma seized_returns: "reg_transition SEIZED RELEASE = Some ACTIVE"
  by simp

lemma restricted_returns: "reg_transition RESTRICTED UNRESTRICT = Some ACTIVE"
  by simp


section \<open>State Machine Instance\<close>

text \<open>
  We show that \<^verbatim>\<open>reg_state\<close> / \<^verbatim>\<open>reg_action\<close> / \<^verbatim>\<open>reg_transition\<close> satisfy
  the \<^verbatim>\<open>state_machine\<close> locale assumptions.
\<close>

definition reg_states :: "reg_state set" where
  "reg_states = {ACTIVE, FROZEN, SEIZED, CONFISCATED, RESTRICTED}"

definition reg_actions :: "reg_action set" where
  "reg_actions = {FREEZE, SEIZE, CONFISCATE, RESTRICT, UNFREEZE, UNRESTRICT, RELEASE}"

definition reg_terminal :: "reg_state set" where
  "reg_terminal = {CONFISCATED}"

lemma reg_states_UNIV: "reg_states = UNIV"
  unfolding reg_states_def by (auto, case_tac x, auto)

lemma reg_actions_UNIV: "reg_actions = UNIV"
  unfolding reg_actions_def by (auto, case_tac x, auto)

lemma reg_transition_closed:
  "\<lbrakk> reg_transition s a = Some s' \<rbrakk> \<Longrightarrow> s' \<in> reg_states"
  unfolding reg_states_def by (cases s; cases a; auto)

interpretation reg_sm: state_machine reg_states reg_actions reg_transition reg_terminal
proof unfold_locales
  show "finite reg_states" unfolding reg_states_def by auto
next
  show "finite reg_actions" unfolding reg_actions_def by auto
next
  show "reg_terminal \<subseteq> reg_states" unfolding reg_terminal_def reg_states_def by auto
next
  fix s a
  assume "s \<in> reg_terminal" "a \<in> reg_actions"
  then show "reg_transition s a = None"
    unfolding reg_terminal_def by (auto simp: confiscated_terminal)
next
  fix s a s'
  assume "s \<in> reg_states" "a \<in> reg_actions" "reg_transition s a = Some s'"
  then show "s' \<in> reg_states"
    using reg_transition_closed by auto
next
  fix s :: reg_state and a :: reg_action
  assume "s \<notin> reg_states"
  then show "reg_transition s a = None"
    using reg_states_UNIV by auto
qed

section \<open>Asset and Global State Modeling\<close>

type_synonym asset_id = nat
type_synonym chain_id = nat
type_synonym timestamp = nat

record asset_state =
  as_reg_state :: reg_state

type_synonym chain_state = "asset_id \<Rightarrow> asset_state option"

record global_state =
  gs_chains    :: "chain_id \<Rightarrow> chain_state"
  gs_locks     :: "asset_id \<Rightarrow> bool"

text \<open>The synchronization message, reduced to the fields this model consumes:
  the regulatory action and its timestamp.  The product's full message also
  carries routing and attribution data (asset, authority, source, targets);
  in this model routing lives at the global-state level
  (\<^verbatim>\<open>connected_chains\<close> and the target set of \<^verbatim>\<open>update_all_chains\<close>), and the
  D-quencer layer adds exactly the attribution fields its priority order
  consumes (see \<^verbatim>\<open>dq_message\<close>).\<close>

record oss_message =
  msg_action    :: reg_action
  msg_timestamp :: timestamp


section \<open>State Accessors and Predicates\<close>

definition get_asset_state :: "global_state \<Rightarrow> chain_id \<Rightarrow> asset_id \<Rightarrow> asset_state option" where
  "get_asset_state gs cid aid = gs_chains gs cid aid"

definition get_reg_state :: "global_state \<Rightarrow> chain_id \<Rightarrow> asset_id \<Rightarrow> reg_state option" where
  "get_reg_state gs cid aid =
    (case get_asset_state gs cid aid of
       None \<Rightarrow> None
     | Some ast \<Rightarrow> Some (as_reg_state ast))"

definition asset_exists :: "global_state \<Rightarrow> chain_id \<Rightarrow> asset_id \<Rightarrow> bool" where
  "asset_exists gs cid aid = (get_asset_state gs cid aid \<noteq> None)"

definition is_locked :: "global_state \<Rightarrow> asset_id \<Rightarrow> bool" where
  "is_locked gs aid = gs_locks gs aid"

text \<open>Connected chains: all chains holding a given asset.\<close>

definition connected_chains :: "global_state \<Rightarrow> asset_id \<Rightarrow> chain_id set" where
  "connected_chains gs aid = {cid. asset_exists gs cid aid}"


section \<open>Global State Validity\<close>

text \<open>
  A global state is valid if all chains holding the same asset agree on
  its regulatory state. This is the cross-chain consistency invariant
  that synchronization must preserve.
\<close>

definition consistent_state :: "global_state \<Rightarrow> bool" where
  "consistent_state gs \<equiv>
    \<forall>c1 c2 aid s1 s2.
      get_reg_state gs c1 aid = Some s1 \<longrightarrow>
      get_reg_state gs c2 aid = Some s2 \<longrightarrow>
      s1 = s2"

definition no_locked_without_reason :: "global_state \<Rightarrow> bool" where
  "no_locked_without_reason gs \<equiv>
    \<forall>aid. \<not> is_locked gs aid"
  \<comment> \<open>Total absence of outstanding locks: in a quiescent valid state no
      asset is locked at all (locks are transient, held only inside a
      synchronization), not merely no unjustified lock.\<close>

definition valid_state :: "global_state \<Rightarrow> bool" where
  "valid_state gs \<equiv> consistent_state gs \<and> no_locked_without_reason gs"


section \<open>Synchronization Protocol\<close>

subsection \<open>Lock acquisition\<close>

definition acquire_lock :: "global_state \<Rightarrow> asset_id \<Rightarrow> global_state option" where
  "acquire_lock gs aid =
    (if is_locked gs aid then None
     else Some (gs\<lparr> gs_locks := (gs_locks gs)(aid := True) \<rparr>))"

definition release_lock :: "global_state \<Rightarrow> asset_id \<Rightarrow> global_state" where
  "release_lock gs aid = gs\<lparr> gs_locks := (gs_locks gs)(aid := False) \<rparr>"

subsection \<open>State update across chains\<close>

text \<open>Update all connected chains to a new regulatory state.

  We define this directly rather than using \<^verbatim>\<open>Finite_Set\<close>.fold, because
  the update for a given asset on each chain is independent — we simply
  construct a new global state where every chain's view of the asset
  is updated. This avoids the need for \<^verbatim>\<open>comp_fun_commute\<close> proofs.\<close>

definition update_all_chains ::
  "global_state \<Rightarrow> asset_id \<Rightarrow> reg_state \<Rightarrow> chain_id set \<Rightarrow> global_state"
where
  "update_all_chains gs aid new_st targets =
    gs\<lparr> gs_chains := (\<lambda>cid.
      if cid \<in> targets then
        (\<lambda>aid'. if aid' = aid then
           (case gs_chains gs cid aid of
              None \<Rightarrow> None
            | Some ast \<Rightarrow> Some (ast\<lparr> as_reg_state := new_st \<rparr>))
         else gs_chains gs cid aid')
      else gs_chains gs cid) \<rparr>"

subsection \<open>The synchronization function\<close>

text \<open>
  sync: the core synchronization operation.

  Given a source chain, action, and \<^verbatim>\<open>asset_id\<close>:
  1. Verify the asset exists on the source chain
  2. Check the transition is valid
  3. Acquire global lock (fails if already locked)
  4. Update all connected chains to the new state
  5. Release lock

  Returns None if any step fails (invalid transition, asset already
  locked, etc.)
\<close>

definition sync ::
  "chain_id \<Rightarrow> reg_action \<Rightarrow> asset_id \<Rightarrow> global_state \<Rightarrow> global_state option"
where
  "sync source action aid gs =
    (case get_reg_state gs source aid of
       None \<Rightarrow> None
     | Some current_st \<Rightarrow>
         (case reg_transition current_st action of
            None \<Rightarrow> None
          | Some new_st \<Rightarrow>
              (case acquire_lock gs aid of
                 None \<Rightarrow> None
               | Some gs_locked \<Rightarrow>
                   let targets = connected_chains gs aid in
                   let gs_updated = update_all_chains gs_locked aid new_st targets in
                   Some (release_lock gs_updated aid))))"


section \<open>Synchronization Properties\<close>

subsection \<open>No self-loops\<close>

text \<open>
  The transition table has no self-loops: a successful transition always
  changes the regulatory state, so a successful synchronization never
  rewrites an asset to the state it already carries.
\<close>

lemma no_self_loops:
  "reg_transition s a = Some s \<Longrightarrow> False"
  by (cases s; cases a; auto)

lemma transition_changes_state:
  "reg_transition s a = Some s' \<Longrightarrow> s \<noteq> s'"
  using no_self_loops by auto

subsection \<open>Properties of update\_all\_chains\<close>

text \<open>
  \<^verbatim>\<open>update_all_chains\<close> correctly updates any chain in the target set.
\<close>

lemma update_all_chains_in_targets:
  assumes "cid \<in> targets"
    and "gs_chains gs cid aid = Some ast"
  shows "gs_chains (update_all_chains gs aid new_st targets) cid aid =
         Some (ast\<lparr> as_reg_state := new_st \<rparr>)"
  unfolding update_all_chains_def using assms by auto

lemma update_all_chains_outside_targets:
  assumes "cid \<notin> targets"
  shows "gs_chains (update_all_chains gs aid new_st targets) cid = gs_chains gs cid"
  unfolding update_all_chains_def using assms by auto

lemma update_all_chains_other_asset:
  assumes "aid' \<noteq> aid"
  shows "gs_chains (update_all_chains gs aid new_st targets) cid aid' =
         gs_chains gs cid aid'"
  unfolding update_all_chains_def using assms by auto

lemma update_all_chains_locks:
  "gs_locks (update_all_chains gs aid new_st targets) = gs_locks gs"
  unfolding update_all_chains_def by auto

text \<open>Key lemma: \<^verbatim>\<open>get_reg_state\<close> after \<^verbatim>\<open>update_all_chains\<close> for a chain in targets.\<close>

lemma update_all_chains_reg_state:
  assumes "cid \<in> targets"
    and "get_asset_state gs cid aid = Some ast"
  shows "get_reg_state (update_all_chains gs aid new_st targets) cid aid = Some new_st"
proof -
  from assms(2) have chain: "gs_chains gs cid aid = Some ast"
    unfolding get_asset_state_def by simp
  then have "gs_chains (update_all_chains gs aid new_st targets) cid aid =
             Some (ast\<lparr> as_reg_state := new_st \<rparr>)"
    using update_all_chains_in_targets[OF assms(1)] by simp
  then show ?thesis
    unfolding get_reg_state_def get_asset_state_def by simp
qed

subsection \<open>Lock mutual exclusion\<close>

text \<open>
  If a lock is held, a further lock acquisition on the same asset fails
  (\<^verbatim>\<open>acquire_lock\<close> returns \<^verbatim>\<open>None\<close>).  In the atomic model this guard
  expresses the intended mutual exclusion of regulatory actions on an asset;
  there is no concurrent execution in the model to serialise.
\<close>

lemma lock_acquire_success:
  assumes "\<not> is_locked gs aid"
  shows "\<exists>gs'. acquire_lock gs aid = Some gs' \<and> is_locked gs' aid"
proof -
  from assms have "\<not> gs_locks gs aid"
    unfolding is_locked_def by simp
  then have "acquire_lock gs aid = Some (gs\<lparr> gs_locks := (gs_locks gs)(aid := True) \<rparr>)"
    unfolding acquire_lock_def is_locked_def by simp
  moreover have "is_locked (gs\<lparr> gs_locks := (gs_locks gs)(aid := True) \<rparr>) aid"
    unfolding is_locked_def by simp
  ultimately show ?thesis by auto
qed


section \<open>Main Theorem: Cross-Chain Regulatory Consistency\<close>

text \<open>
  The central theorem of this theory. If a regulatory action is applied via
  sync --- from an arbitrary global state --- every connected chain reflects
  the new regulatory state; under a valid input state, validity is preserved
  as well (\<^verbatim>\<open>valid_state_preservation\<close> below).

  This is the regulatory instantiation of the cross-domain consistency
  theorem from \<^verbatim>\<open>State_Preservation\<close>.thy.

  The proof proceeds by:
  1. Unfolding sync into lock, then \<^verbatim>\<open>update_all_chains\<close>, then unlock
  2. Showing \<^verbatim>\<open>acquire_lock\<close> and \<^verbatim>\<open>release_lock\<close> preserve chain state
  3. Showing \<^verbatim>\<open>update_all_chains\<close> updates every chain in the target set
  4. Combining these facts to establish the conclusion
\<close>

text \<open>
  Auxiliary: \<^verbatim>\<open>release_lock\<close> does not change chains.
\<close>

lemma release_lock_chains:
  "gs_chains (release_lock gs aid) = gs_chains gs"
  unfolding release_lock_def by simp

lemma release_lock_reg_state:
  "get_reg_state (release_lock gs aid) cid aid' = get_reg_state gs cid aid'"
  unfolding get_reg_state_def get_asset_state_def release_lock_chains by simp

text \<open>
  Auxiliary: \<^verbatim>\<open>acquire_lock\<close> does not change chains.
\<close>

lemma acquire_lock_chains:
  assumes "acquire_lock gs aid = Some gs'"
  shows "gs_chains gs' = gs_chains gs"
  using assms unfolding acquire_lock_def is_locked_def
  by (auto split: if_splits)

text \<open>
  Auxiliary: \<^verbatim>\<open>connected_chains\<close> uses original gs, not locked gs.
\<close>

text \<open>
  The cross-chain regulatory homomorphism theorem.
\<close>

theorem regulatory_homomorphism:
  assumes current: "get_reg_state gs source aid = Some s"
    and trans: "reg_transition s action = Some s'"
    and synced: "sync source action aid gs = Some gs'"
    and connected: "c \<in> connected_chains gs aid"
  shows "get_reg_state gs' c aid = Some s'"
proof -
  \<comment> \<open>Step 1: Unfold sync to extract intermediate states\<close>
  from synced current trans
  obtain gs_locked where
    lock: "acquire_lock gs aid = Some gs_locked"
    and gs'_def: "gs' = release_lock
      (update_all_chains gs_locked aid s' (connected_chains gs aid)) aid"
    unfolding sync_def
    by (auto split: option.splits simp: Let_def)

  \<comment> \<open>Step 2: \<^verbatim>\<open>acquire_lock\<close> preserves chains\<close>
  have locked_chains: "gs_chains gs_locked = gs_chains gs"
    using acquire_lock_chains[OF lock] by simp

  \<comment> \<open>Step 3: c is in \<^verbatim>\<open>connected_chains\<close>, so the asset exists on c\<close>
  from connected have "asset_exists gs c aid"
    unfolding connected_chains_def by simp
  then obtain ast_c where ast_c: "gs_chains gs c aid = Some ast_c"
    unfolding asset_exists_def get_asset_state_def by auto

  \<comment> \<open>Step 4: Therefore asset also exists in \<^verbatim>\<open>gs_locked\<close> on chain c\<close>
  have ast_locked: "gs_chains gs_locked c aid = Some ast_c"
    using ast_c locked_chains by simp

  \<comment> \<open>Step 5: \<^verbatim>\<open>update_all_chains\<close> updates chain c\<close>
  have updated: "gs_chains (update_all_chains gs_locked aid s' (connected_chains gs aid)) c aid =
                 Some (ast_c\<lparr> as_reg_state := s' \<rparr>)"
    using update_all_chains_in_targets[OF connected ast_locked] by simp

  \<comment> \<open>Step 6: \<^verbatim>\<open>release_lock\<close> does not change chains\<close>
  have "gs_chains gs' c aid = Some (ast_c\<lparr> as_reg_state := s' \<rparr>)"
    using updated unfolding gs'_def release_lock_chains by simp

  \<comment> \<open>Step 7: Extract \<^verbatim>\<open>reg_state\<close>\<close>
  then show ?thesis
    unfolding get_reg_state_def get_asset_state_def by simp
qed


section \<open>Valid State Preservation\<close>

text \<open>
  The central safety property: synchronization preserves global state validity.

  If the global state is valid (consistent and unlocked) before sync,
  and sync succeeds, then the resulting global state is also valid.

  This closes the inductive invariant: valid initial state + \<^verbatim>\<open>valid_state\<close>
  preservation under sync = \<^verbatim>\<open>valid_state\<close> holds at all reachable states.

  The proof decomposes into two parts:
    (1) \<^verbatim>\<open>consistent_state\<close> preservation: sync updates all connected chains
        to the same new state and leaves other assets untouched.
    (2) \<^verbatim>\<open>no_locked_without_reason\<close> preservation: sync acquires and then
        releases the lock within the same operation, so the output
        has no outstanding locks (assuming no other locks were held).
\<close>

subsection \<open>Part 1: consistent\_state preservation\<close>

text \<open>
  After sync, any two chains holding asset aid agree on its new regulatory
  state (it is s'), and any two chains holding a different asset aid' still
  agree (their states are unchanged from the consistent input).
\<close>

lemma sync_preserves_consistent_state:
  assumes valid: "valid_state gs"
    and current: "get_reg_state gs source aid = Some s"
    and trans: "reg_transition s action = Some s'"
    and synced: "sync source action aid gs = Some gs'"
  shows "consistent_state gs'"
proof -
  \<comment> \<open>Unfold sync to extract the structure\<close>
  from synced current trans
  obtain gs_locked where
    lock: "acquire_lock gs aid = Some gs_locked"
    and gs'_def: "gs' = release_lock
      (update_all_chains gs_locked aid s' (connected_chains gs aid)) aid"
    unfolding sync_def
    by (auto split: option.splits simp: Let_def)

  have locked_chains: "gs_chains gs_locked = gs_chains gs"
    using acquire_lock_chains[OF lock] by simp

  show ?thesis
  unfolding consistent_state_def
  proof (intro allI impI)
    fix c1 c2 aid' s1_final s2_final
    assume s1_eq: "get_reg_state gs' c1 aid' = Some s1_final"
       and s2_eq: "get_reg_state gs' c2 aid' = Some s2_final"

    show "s1_final = s2_final"
    proof (cases "aid' = aid")
      case True
      \<comment> \<open>Case: the synchronized asset. Two sub-cases per chain.\<close>
      show ?thesis
      proof (cases "c1 \<in> connected_chains gs aid")
        case c1_in: True
        then have ae1: "asset_exists gs c1 aid"
          unfolding connected_chains_def by simp
        then obtain ast1 where ast1: "gs_chains gs c1 aid = Some ast1"
          unfolding asset_exists_def get_asset_state_def by auto
        have ast1_locked: "gs_chains gs_locked c1 aid = Some ast1"
          using ast1 locked_chains by simp
        have upd1: "gs_chains (update_all_chains gs_locked aid s' (connected_chains gs aid)) c1 aid =
                    Some (ast1\<lparr> as_reg_state := s' \<rparr>)"
          using update_all_chains_in_targets[OF c1_in ast1_locked] by simp
        have reg1: "get_reg_state gs' c1 aid = Some s'"
          unfolding gs'_def release_lock_chains get_reg_state_def get_asset_state_def
          using upd1 by simp
        show ?thesis
        proof (cases "c2 \<in> connected_chains gs aid")
          case c2_in: True
          then have ae2: "asset_exists gs c2 aid"
            unfolding connected_chains_def by simp
          then obtain ast2 where ast2: "gs_chains gs c2 aid = Some ast2"
            unfolding asset_exists_def get_asset_state_def by auto
          have ast2_locked: "gs_chains gs_locked c2 aid = Some ast2"
            using ast2 locked_chains by simp
          have reg2: "get_reg_state gs' c2 aid = Some s'"
            unfolding gs'_def release_lock_chains get_reg_state_def get_asset_state_def
            using update_all_chains_in_targets[OF c2_in ast2_locked] by simp
          from reg1 reg2 s1_eq s2_eq True show ?thesis by simp
        next
          case c2_out: False
          \<comment> \<open>c2 is not connected, so asset doesn't exist on c2 for aid\<close>
          have "gs_chains (update_all_chains gs_locked aid s' (connected_chains gs aid)) c2 =
                gs_chains gs_locked c2"
            using update_all_chains_outside_targets[OF c2_out] by simp
          then have "gs_chains gs' c2 aid = gs_chains gs c2 aid"
            unfolding gs'_def release_lock_chains using locked_chains by simp
          moreover have "gs_chains gs c2 aid = None"
            using c2_out unfolding connected_chains_def asset_exists_def get_asset_state_def
            by auto
          ultimately have "get_reg_state gs' c2 aid = None"
            unfolding get_reg_state_def get_asset_state_def by simp
          with s2_eq True show ?thesis by simp
        qed
      next
        case c1_out: False
        \<comment> \<open>c1 not connected: asset doesn't exist there\<close>
        have "gs_chains (update_all_chains gs_locked aid s' (connected_chains gs aid)) c1 =
              gs_chains gs_locked c1"
          using update_all_chains_outside_targets[OF c1_out] by simp
        then have "gs_chains gs' c1 aid = gs_chains gs c1 aid"
          unfolding gs'_def release_lock_chains using locked_chains by simp
        moreover have "gs_chains gs c1 aid = None"
          using c1_out unfolding connected_chains_def asset_exists_def get_asset_state_def
          by auto
        ultimately have "get_reg_state gs' c1 aid = None"
          unfolding get_reg_state_def get_asset_state_def by simp
        with s1_eq True show ?thesis by simp
      qed
    next
      case diff: False
      \<comment> \<open>Case: a different asset. Sync does not touch it.\<close>
      have other1: "gs_chains (update_all_chains gs_locked aid s' (connected_chains gs aid)) c1 aid' =
                    gs_chains gs_locked c1 aid'"
        using update_all_chains_other_asset[OF diff] by simp
      have other2: "gs_chains (update_all_chains gs_locked aid s' (connected_chains gs aid)) c2 aid' =
                    gs_chains gs_locked c2 aid'"
        using update_all_chains_other_asset[OF diff] by simp
      have "gs_chains gs' c1 aid' = gs_chains gs c1 aid'"
        unfolding gs'_def release_lock_chains using other1 locked_chains by simp
      moreover have "gs_chains gs' c2 aid' = gs_chains gs c2 aid'"
        unfolding gs'_def release_lock_chains using other2 locked_chains by simp
      ultimately have "get_reg_state gs' c1 aid' = get_reg_state gs c1 aid'"
        and "get_reg_state gs' c2 aid' = get_reg_state gs c2 aid'"
        unfolding get_reg_state_def get_asset_state_def by simp_all
      with s1_eq s2_eq have
        "get_reg_state gs c1 aid' = Some s1_final"
        "get_reg_state gs c2 aid' = Some s2_final"
        by simp_all
      with valid show ?thesis
        unfolding valid_state_def consistent_state_def by blast
    qed
  qed
qed


subsection \<open>Part 2: no\_locked\_without\_reason preservation\<close>

text \<open>
  After sync, no assets are locked. The sync operation acquires a lock
  on the target asset and releases it before returning. For all other
  assets, the lock state is unchanged (and was False by \<^verbatim>\<open>valid_state\<close>).
\<close>

lemma sync_preserves_no_locks:
  assumes valid: "valid_state gs"
    and current: "get_reg_state gs source aid = Some s"
    and trans: "reg_transition s action = Some s'"
    and synced: "sync source action aid gs = Some gs'"
  shows "no_locked_without_reason gs'"
proof -
  from synced current trans
  obtain gs_locked where
    lock: "acquire_lock gs aid = Some gs_locked"
    and gs'_def: "gs' = release_lock
      (update_all_chains gs_locked aid s' (connected_chains gs aid)) aid"
    unfolding sync_def
    by (auto split: option.splits simp: Let_def)

  \<comment> \<open>Locks after acquire: only aid is locked\<close>
  from lock have locked_locks: "gs_locks gs_locked = (gs_locks gs)(aid := True)"
    unfolding acquire_lock_def is_locked_def
    by (auto split: if_splits)

  \<comment> \<open>\<^verbatim>\<open>update_all_chains\<close> does not change locks\<close>
  have upd_locks: "gs_locks (update_all_chains gs_locked aid s' (connected_chains gs aid)) =
                   gs_locks gs_locked"
    using update_all_chains_locks by simp

  \<comment> \<open>\<^verbatim>\<open>release_lock\<close> clears the lock on aid\<close>
  have final_locks: "gs_locks gs' = (gs_locks gs_locked)(aid := False)"
    unfolding gs'_def release_lock_def using upd_locks by simp

  show ?thesis
  unfolding no_locked_without_reason_def is_locked_def
  proof
    fix aid'
    show "\<not> gs_locks gs' aid'"
    proof (cases "aid' = aid")
      case True
      then show ?thesis using final_locks by simp
    next
      case False
      then have "gs_locks gs' aid' = gs_locks gs_locked aid'"
        using final_locks by simp
      also have "... = gs_locks gs aid'"
        using locked_locks False by simp
      also have "... = False"
        using valid unfolding valid_state_def no_locked_without_reason_def is_locked_def
        by simp
      finally show ?thesis by simp
    qed
  qed
qed


subsection \<open>The valid\_state preservation theorem\<close>

text \<open>
  Combining the two parts: sync preserves \<^verbatim>\<open>valid_state\<close>.
  This is the inductive invariant that guarantees \<^verbatim>\<open>valid_state\<close>
  holds at every reachable global state.
\<close>

theorem valid_state_preservation:
  assumes valid: "valid_state gs"
    and current: "get_reg_state gs source aid = Some s"
    and trans: "reg_transition s action = Some s'"
    and synced: "sync source action aid gs = Some gs'"
  shows "valid_state gs'"
  unfolding valid_state_def
  using sync_preserves_consistent_state[OF assms]
        sync_preserves_no_locks[OF assms]
  by auto


section \<open>Heterogeneous-Action State Preservation Instance\<close>

text \<open>
  This section instantiates the \<^verbatim>\<open>state_preservation\<close> locale with a concrete
  heterogeneous-action scenario between two chains.

  The scenario models the following operational situation. Two chains A and B
  share the same regulatory state space (ACTIVE, FROZEN, SEIZED, CONFISCATED,
  RESTRICTED), but their on-chain action vocabularies differ. Chain A supports
  the full seven-action set used elsewhere in this theory. Chain B is a chain
  whose jurisdiction handles de-escalation (UNFREEZE, UNRESTRICT, RELEASE)
  exclusively through separate judicial procedures rather than as on-chain
  actions; correspondingly, Chain B's on-chain action vocabulary is the
  four-action escalation subset only. The synchronisation map between the
  two chains is therefore non-trivial in two ways:

  \<^item> The source action type is \<^verbatim>\<open>reg_action\<close> and the target action type is
    a separate datatype \<^verbatim>\<open>chain_b_action\<close> with four constructors. This
    exercises the locale's heterogeneous source / target action types
    (\<^verbatim>\<open>'a\<close> vs.\ \<^verbatim>\<open>'b\<close>).
  \<^item> The locale parameter \<^verbatim>\<open>actions\<^sub>s\<close> is instantiated with a strict subset
    of the full \<^verbatim>\<open>reg_action\<close> set, namely the four escalation actions.
    De-escalation actions exist in \<^verbatim>\<open>reg_action\<close> as a datatype but are
    out of scope for this synchronisation instance.

  The naturality assumption then has to hold only on the escalation subset,
  which is exactly the design intent of the locale's \<^verbatim>\<open>actions\<^sub>s\<close> parameter:
  the user can scope structural preservation to a subset of source actions
  rather than to the full source action type.
\<close>

datatype chain_b_action = B_FREEZE | B_SEIZE | B_CONFISCATE | B_RESTRICT

text \<open>
  The escalation subset of \<^verbatim>\<open>reg_action\<close> that this instance synchronises
  across to Chain B.
\<close>

definition escalation_actions :: "reg_action set" where
  "escalation_actions = {FREEZE, SEIZE, CONFISCATE, RESTRICT}"

definition chain_b_actions :: "chain_b_action set" where
  "chain_b_actions = {B_FREEZE, B_SEIZE, B_CONFISCATE, B_RESTRICT}"

text \<open>
  Chain B's transition function. Its values mirror Chain A's transition
  function on the four escalation actions: when Chain A maps
  \<^verbatim>\<open>(s, escalation action)\<close> to \<^verbatim>\<open>Some s'\<close>, Chain B does the same; when Chain A
  rejects, Chain B rejects. Both chains share the regulatory state space, so
  no state translation is required (the state map is the identity).
\<close>

fun chain_b_transition :: "reg_state \<Rightarrow> chain_b_action \<Rightarrow> reg_state option" where
  "chain_b_transition s B_FREEZE      = reg_transition s FREEZE"
| "chain_b_transition s B_SEIZE       = reg_transition s SEIZE"
| "chain_b_transition s B_CONFISCATE  = reg_transition s CONFISCATE"
| "chain_b_transition s B_RESTRICT    = reg_transition s RESTRICT"

text \<open>The escalation action map: a 1-to-1 correspondence between Chain A's
  four escalation actions and Chain B's four constructors.\<close>

fun escalation_action_map :: "reg_action \<Rightarrow> chain_b_action" where
  "escalation_action_map FREEZE     = B_FREEZE"
| "escalation_action_map SEIZE      = B_SEIZE"
| "escalation_action_map CONFISCATE = B_CONFISCATE"
| "escalation_action_map RESTRICT   = B_RESTRICT"
| "escalation_action_map UNFREEZE   = B_FREEZE"
| "escalation_action_map UNRESTRICT = B_FREEZE"
| "escalation_action_map RELEASE    = B_FREEZE"
  \<comment> \<open>The last three clauses are unused by the locale instance, since
      \<^verbatim>\<open>actions\<^sub>s = escalation_actions\<close> excludes the de-escalation actions.
      They are present only to make the function total on \<^verbatim>\<open>reg_action\<close>.\<close>

text \<open>
  Chain B is also a state machine over the same regulatory state space.
\<close>

lemma chain_b_transition_closed:
  "chain_b_transition s a = Some s' \<Longrightarrow> s' \<in> reg_states"
proof -
  assume "chain_b_transition s a = Some s'"
  then have "\<exists>a'. reg_transition s a' = Some s'"
    by (cases a) auto
  then show "s' \<in> reg_states" using reg_transition_closed by auto
qed

lemma chain_b_terminal:
  "s \<in> reg_terminal \<Longrightarrow> chain_b_transition s a = None"
  unfolding reg_terminal_def
  by (cases a) (auto simp: confiscated_terminal)

text \<open>
  The naturality conditions of \<^verbatim>\<open>state_preservation\<close> hold for the
  escalation subset. Both directions (\<^verbatim>\<open>Some\<close> and \<^verbatim>\<open>None\<close> branches) follow
  by case analysis on the escalation action: by construction, Chain B's
  transition function on each \<^verbatim>\<open>B_X\<close> constructor mirrors Chain A's
  transition function on the corresponding \<^verbatim>\<open>X\<close> action.
\<close>

lemma escalation_naturality_some:
  assumes "a \<in> escalation_actions"
    and "reg_transition s a = Some s'"
  shows "chain_b_transition s (escalation_action_map a) = Some s'"
proof -
  from assms(1) have "a \<in> {FREEZE, SEIZE, CONFISCATE, RESTRICT}"
    unfolding escalation_actions_def by simp
  then consider "a = FREEZE" | "a = SEIZE" | "a = CONFISCATE" | "a = RESTRICT"
    by auto
  then show ?thesis using assms(2) by (cases) auto
qed

lemma escalation_naturality_none:
  assumes "a \<in> escalation_actions"
    and "reg_transition s a = None"
  shows "chain_b_transition s (escalation_action_map a) = None"
proof -
  from assms(1) have "a \<in> {FREEZE, SEIZE, CONFISCATE, RESTRICT}"
    unfolding escalation_actions_def by simp
  then consider "a = FREEZE" | "a = SEIZE" | "a = CONFISCATE" | "a = RESTRICT"
    by auto
  then show ?thesis using assms(2) by (cases) auto
qed

text \<open>
  The escalation instance: \<^verbatim>\<open>state_preservation\<close> with \<^verbatim>\<open>actions\<^sub>s\<close> the
  escalation subset of \<^verbatim>\<open>reg_action\<close>, target action type \<^verbatim>\<open>chain_b_action\<close>,
  and identity state map (both chains share the regulatory state space).
\<close>

text \<open>
  Both state-machine sides of the heterogeneous-action instance --- the
  source on the escalation subset of \<^verbatim>\<open>reg_actions\<close> and Chain~B's target ---
  have their obligations discharged inline by \<^theory_text>\<open>unfold_locales\<close>
  in the interpretation below, drawing on the closure and terminal lemmas
  above.
\<close>

text \<open>
  Heterogeneous-action instance: the source action set is the
  \<^verbatim>\<open>escalation_actions\<close> subset of \<^verbatim>\<open>reg_action\<close>, the target action set is
  \<^verbatim>\<open>chain_b_actions\<close>, and the state map is the identity. Both source and
  target state machines share the regulatory state space, so two of the
  state-machine obligations (\<^verbatim>\<open>finite reg_states\<close> and
  \<^verbatim>\<open>reg_terminal \<subseteq> reg_states\<close>) collapse between source and target; the
  proof structure below reflects this by issuing each \<^verbatim>\<open>show\<close> exactly once
  for the merged obligation.
\<close>

interpretation escalation_preservation:
  state_preservation
    reg_states escalation_actions reg_transition reg_terminal
    reg_states chain_b_actions chain_b_transition reg_terminal
    "id :: reg_state \<Rightarrow> reg_state" escalation_action_map
proof unfold_locales
  show "finite reg_states" unfolding reg_states_def by auto
next
  show "finite escalation_actions" unfolding escalation_actions_def by auto
next
  show "reg_terminal \<subseteq> reg_states" unfolding reg_terminal_def reg_states_def by auto
next
  fix s a
  assume "s \<in> reg_terminal" "a \<in> escalation_actions"
  then show "reg_transition s a = None"
    unfolding reg_terminal_def by (auto simp: confiscated_terminal)
next
  fix s a s'
  assume "s \<in> reg_states" "a \<in> escalation_actions" "reg_transition s a = Some s'"
  then show "s' \<in> reg_states" using reg_transition_closed by auto
next
  fix s :: reg_state and a :: reg_action
  assume "s \<notin> reg_states"
  then show "reg_transition s a = None" using reg_states_UNIV by auto
next
  show "finite chain_b_actions" unfolding chain_b_actions_def by auto
next
  fix s a
  assume "s \<in> reg_terminal" "a \<in> chain_b_actions"
  then show "chain_b_transition s a = None" using chain_b_terminal by auto
next
  fix s a s'
  assume "s \<in> reg_states" "a \<in> chain_b_actions" "chain_b_transition s a = Some s'"
  then show "s' \<in> reg_states" using chain_b_transition_closed by auto
next
  fix s :: reg_state and a :: chain_b_action
  assume "s \<notin> reg_states"
  then show "chain_b_transition s a = None" using reg_states_UNIV by auto
next
  fix s
  assume "s \<in> reg_states"
  then show "id s \<in> reg_states" by simp
next
  fix a
  assume "a \<in> escalation_actions"
  then show "escalation_action_map a \<in> chain_b_actions"
    unfolding escalation_actions_def chain_b_actions_def by auto
next
  fix s
  assume "s \<in> reg_terminal"
  then show "id s \<in> reg_terminal" by simp
next
  fix s a s'
  assume "s \<in> reg_states" "a \<in> escalation_actions" "reg_transition s a = Some s'"
  then show "chain_b_transition (id s) (escalation_action_map a) = Some (id s')"
    using escalation_naturality_some by simp
next
  fix s a
  assume "s \<in> reg_states" "a \<in> escalation_actions" "reg_transition s a = None"
  then show "chain_b_transition (id s) (escalation_action_map a) = None"
    using escalation_naturality_none by simp
qed

text \<open>
  As a corollary of the locale interpretation, sequential preservation
  (the locale's main theorem) applies to escalation action sequences:
  any valid sequence of escalation actions on Chain A produces, when
  mapped through \<^verbatim>\<open>escalation_action_map\<close>, a valid sequence on Chain B
  ending in the same regulatory state.
\<close>

corollary escalation_sequential_preservation:
  assumes "s \<in> reg_states"
    and "\<forall>a \<in> set as. a \<in> escalation_actions"
    and "escalation_preservation.source.apply_actions s as = Some s'"
  shows "escalation_preservation.target.apply_actions s (map escalation_action_map as)
       = Some s'"
  using assms escalation_preservation.sequential_preservation [where as = as]
  by simp


section \<open>Layer-Crossing Symmetric State Preservation Instance\<close>

text \<open>
  This section instantiates the \<^verbatim>\<open>symmetric_state_preservation\<close> locale with
  a concrete bidirectional binding between two representations of the same
  regulatory state.

  The on-chain representation is the five-element \<^verbatim>\<open>reg_state\<close> enum used
  throughout this theory. The off-chain representation is a structured
  permission record (\<^verbatim>\<open>daml_perm\<close>) modelling a DAML party-permission
  ledger entry: a status tag plus auxiliary fields that carry the
  party / scope metadata associated with a non-trivial regulatory status
  (the seizing party for SEIZED, the restriction scope for RESTRICTED).
  The identifier values themselves are representative placeholders; what
  the invariant tracks is their presence, and the layer-crossing content
  lives in the status tag.
  A type-level invariant (\<^verbatim>\<open>valid_daml_perm\<close>) ties the auxiliary fields to
  the status tag; the bijection domain itself is the image of the
  representation map (\<^verbatim>\<open>daml_states\<close>), every element of which satisfies
  the invariant.

  The action vocabularies on the two layers coincide: both layers process
  the seven actions of \<^verbatim>\<open>reg_action\<close>, and the action map is the identity.
  All of the non-trivial content of the symmetric instance therefore lives
  in the layer-crossing state mapping. The roundtrip assumptions of
  \<^verbatim>\<open>symmetric_state_preservation\<close> become a pair of bijection conditions
  between \<^verbatim>\<open>reg_state\<close> and the image \<^verbatim>\<open>daml_states\<close> of the
  representation map.
\<close>

datatype daml_status_tag =
  D_Active | D_Frozen | D_Seized | D_Confiscated | D_Restricted

record daml_perm =
  status_tag        :: daml_status_tag
  seized_by         :: "nat option"
  restriction_scope :: "nat option"

definition default_party_id :: nat where
  "default_party_id = 0"

definition default_scope_id :: nat where
  "default_scope_id = 0"

text \<open>
  The well-formedness invariant: the auxiliary fields are non-\<^verbatim>\<open>None\<close> exactly
  on the status tags that semantically require them.
\<close>

definition valid_daml_perm :: "daml_perm \<Rightarrow> bool" where
  "valid_daml_perm p \<longleftrightarrow>
     (status_tag p = D_Seized \<longleftrightarrow> seized_by p \<noteq> None) \<and>
     (status_tag p = D_Restricted \<longleftrightarrow> restriction_scope p \<noteq> None)"

text \<open>The two state maps between the two representations.\<close>

fun reg_to_daml :: "reg_state \<Rightarrow> daml_perm" where
  "reg_to_daml ACTIVE      = \<lparr> status_tag = D_Active,
                                seized_by = None,
                                restriction_scope = None \<rparr>"
| "reg_to_daml FROZEN      = \<lparr> status_tag = D_Frozen,
                                seized_by = None,
                                restriction_scope = None \<rparr>"
| "reg_to_daml SEIZED      = \<lparr> status_tag = D_Seized,
                                seized_by = Some default_party_id,
                                restriction_scope = None \<rparr>"
| "reg_to_daml CONFISCATED = \<lparr> status_tag = D_Confiscated,
                                seized_by = None,
                                restriction_scope = None \<rparr>"
| "reg_to_daml RESTRICTED  = \<lparr> status_tag = D_Restricted,
                                seized_by = None,
                                restriction_scope = Some default_scope_id \<rparr>"

fun daml_to_reg :: "daml_perm \<Rightarrow> reg_state" where
  "daml_to_reg p = (case status_tag p of
                      D_Active       \<Rightarrow> ACTIVE
                    | D_Frozen       \<Rightarrow> FROZEN
                    | D_Seized       \<Rightarrow> SEIZED
                    | D_Confiscated  \<Rightarrow> CONFISCATED
                    | D_Restricted   \<Rightarrow> RESTRICTED)"

text \<open>The DAML target state space: the image of \<^verbatim>\<open>reg_to_daml\<close>.\<close>

definition daml_states :: "daml_perm set" where
  "daml_states = range reg_to_daml"

definition daml_terminal :: "daml_perm set" where
  "daml_terminal = {reg_to_daml CONFISCATED}"

text \<open>
  The DAML transition function: lifts \<^verbatim>\<open>reg_transition\<close> through the
  representation map. By construction, \<^verbatim>\<open>daml_transition\<close> respects the
  \<^verbatim>\<open>reg_to_daml\<close> map.
\<close>

definition daml_transition :: "daml_perm \<Rightarrow> reg_action \<Rightarrow> daml_perm option" where
  "daml_transition p a =
     (if p \<in> daml_states then
        (case reg_transition (daml_to_reg p) a of
           None    \<Rightarrow> None
         | Some s' \<Rightarrow> Some (reg_to_daml s'))
      else None)"

text \<open>Roundtrip lemmas establishing the layer-crossing bijection.\<close>

lemma daml_to_reg_to_daml_id:
  "daml_to_reg (reg_to_daml s) = s"
  by (cases s) auto

lemma reg_to_daml_to_reg_on_image:
  assumes "p \<in> daml_states"
  shows "reg_to_daml (daml_to_reg p) = p"
proof -
  from assms obtain s where "p = reg_to_daml s"
    unfolding daml_states_def by auto
  then show ?thesis using daml_to_reg_to_daml_id by simp
qed

lemma reg_to_daml_valid:
  "valid_daml_perm (reg_to_daml s)"
  unfolding valid_daml_perm_def by (cases s) auto

text \<open>
  The DAML side is a state machine on the image of \<^verbatim>\<open>reg_to_daml\<close>.
\<close>

lemma daml_states_finite: "finite daml_states"
proof -
  have fin_reg: "finite reg_states" unfolding reg_states_def by auto
  hence fin_img: "finite (reg_to_daml ` reg_states)" by (rule finite_imageI)
  have eq: "daml_states = reg_to_daml ` reg_states"
    unfolding daml_states_def using reg_states_UNIV by simp
  from fin_img eq show ?thesis by simp
qed

lemma daml_terminal_subset: "daml_terminal \<subseteq> daml_states"
  unfolding daml_terminal_def daml_states_def by blast

lemma daml_terminal_absorbing:
  assumes "p \<in> daml_terminal" and "a \<in> reg_actions"
  shows "daml_transition p a = None"
proof -
  from assms(1) have "p = reg_to_daml CONFISCATED"
    unfolding daml_terminal_def by simp
  then have "daml_to_reg p = CONFISCATED" using daml_to_reg_to_daml_id by simp
  moreover have "p \<in> daml_states"
    using assms(1) daml_terminal_subset by auto
  ultimately show ?thesis
    unfolding daml_transition_def using confiscated_terminal by simp
qed

lemma daml_transition_closed:
  assumes "p \<in> daml_states" and "a \<in> reg_actions"
    and "daml_transition p a = Some p'"
  shows "p' \<in> daml_states"
proof -
  from assms(1,3) obtain s' where
    s'_eq: "reg_transition (daml_to_reg p) a = Some s'"
    and p'_def: "p' = reg_to_daml s'"
    unfolding daml_transition_def
    by (auto split: option.splits if_splits)
  then show ?thesis
    unfolding daml_states_def by auto
qed

lemma daml_transition_outside_states:
  "p \<notin> daml_states \<Longrightarrow> daml_transition p a = None"
  unfolding daml_transition_def by simp

text \<open>
  Forward naturality: \<^verbatim>\<open>reg_to_daml\<close> commutes with transitions.
\<close>

lemma reg_to_daml_naturality_some:
  assumes "s \<in> reg_states" and "a \<in> reg_actions"
    and "reg_transition s a = Some s'"
  shows "daml_transition (reg_to_daml s) a = Some (reg_to_daml s')"
proof -
  have in_states: "reg_to_daml s \<in> daml_states"
    unfolding daml_states_def by auto
  have "daml_to_reg (reg_to_daml s) = s" using daml_to_reg_to_daml_id by simp
  with assms(3) have
    "reg_transition (daml_to_reg (reg_to_daml s)) a = Some s'" by simp
  with in_states show ?thesis
    unfolding daml_transition_def by simp
qed

lemma reg_to_daml_naturality_none:
  assumes "s \<in> reg_states" and "a \<in> reg_actions"
    and "reg_transition s a = None"
  shows "daml_transition (reg_to_daml s) a = None"
proof -
  have in_states: "reg_to_daml s \<in> daml_states"
    unfolding daml_states_def by auto
  have "daml_to_reg (reg_to_daml s) = s" using daml_to_reg_to_daml_id by simp
  with assms(3) have
    "reg_transition (daml_to_reg (reg_to_daml s)) a = None" by simp
  with in_states show ?thesis
    unfolding daml_transition_def by simp
qed

text \<open>
  Backward naturality: \<^verbatim>\<open>daml_to_reg\<close> on the image of \<^verbatim>\<open>reg_to_daml\<close>
  commutes with transitions in the opposite direction.
\<close>

lemma daml_to_reg_naturality_some:
  assumes "p \<in> daml_states" and "a \<in> reg_actions"
    and "daml_transition p a = Some p'"
  shows "reg_transition (daml_to_reg p) a = Some (daml_to_reg p')"
proof -
  from assms(1,3) obtain s' where
    s'_eq: "reg_transition (daml_to_reg p) a = Some s'"
    and p'_def: "p' = reg_to_daml s'"
    unfolding daml_transition_def
    by (auto split: option.splits if_splits)
  from p'_def have "daml_to_reg p' = s'" using daml_to_reg_to_daml_id by simp
  with s'_eq show ?thesis by simp
qed

lemma daml_to_reg_naturality_none:
  assumes "p \<in> daml_states" and "a \<in> reg_actions"
    and "daml_transition p a = None"
  shows "reg_transition (daml_to_reg p) a = None"
proof (rule ccontr)
  assume "reg_transition (daml_to_reg p) a \<noteq> None"
  then obtain s' where "reg_transition (daml_to_reg p) a = Some s'" by auto
  with assms(1) have "daml_transition p a = Some (reg_to_daml s')"
    unfolding daml_transition_def by simp
  with assms(3) show False by simp
qed

text \<open>
  Forward state preservation: \<^verbatim>\<open>reg_to_daml\<close> as a structure-preserving map.
\<close>

text \<open>
  Forward state preservation. The source state machine is on
  \<^verbatim>\<open>(reg_states, reg_actions, reg_transition, reg_terminal)\<close>, which exactly
  matches the \<^verbatim>\<open>reg_sm\<close> interpretation; consequently \<^verbatim>\<open>unfold_locales\<close>
  auto-discharges all six source state-machine obligations. The target side
  is the DAML structured-permission record, for which only individual
  lemmas (not a registered interpretation) are available, so all six target
  state-machine obligations remain pending alongside the five
  preservation-specific axioms — eleven obligations in total. The
  asymmetry with \<^verbatim>\<open>backward_layer_preservation\<close> below (which has only the
  five preservation axioms remaining) reflects the order in which the
  locale extension presents the two state-machine sub-locales.
\<close>

interpretation forward_layer_preservation:
  state_preservation
    reg_states reg_actions reg_transition reg_terminal
    daml_states reg_actions daml_transition daml_terminal
    reg_to_daml id
proof unfold_locales
  show "finite daml_states" by (rule daml_states_finite)
next
  show "finite reg_actions" unfolding reg_actions_def by auto
next
  show "daml_terminal \<subseteq> daml_states" by (rule daml_terminal_subset)
next
  fix s a
  assume "s \<in> daml_terminal" "a \<in> reg_actions"
  then show "daml_transition s a = None" by (rule daml_terminal_absorbing)
next
  fix s a s'
  assume "s \<in> daml_states" "a \<in> reg_actions" "daml_transition s a = Some s'"
  then show "s' \<in> daml_states" by (rule daml_transition_closed)
next
  fix s :: daml_perm and a :: reg_action
  assume "s \<notin> daml_states"
  then show "daml_transition s a = None" by (rule daml_transition_outside_states)
next
  fix s
  assume "s \<in> reg_states"
  then show "reg_to_daml s \<in> daml_states" unfolding daml_states_def by auto
next
  fix a
  assume "a \<in> reg_actions"
  then show "id a \<in> reg_actions" by simp
next
  fix s
  assume "s \<in> reg_terminal"
  then show "reg_to_daml s \<in> daml_terminal"
    unfolding reg_terminal_def daml_terminal_def by simp
next
  fix s a s'
  assume "s \<in> reg_states" "a \<in> reg_actions" "reg_transition s a = Some s'"
  then show "daml_transition (reg_to_daml s) (id a) = Some (reg_to_daml s')"
    using reg_to_daml_naturality_some by simp
next
  fix s a
  assume "s \<in> reg_states" "a \<in> reg_actions" "reg_transition s a = None"
  then show "daml_transition (reg_to_daml s) (id a) = None"
    using reg_to_daml_naturality_none by simp
qed

text \<open>
  Backward state preservation: \<^verbatim>\<open>daml_to_reg\<close> as a structure-preserving map
  on the image of \<^verbatim>\<open>reg_to_daml\<close>.
\<close>

text \<open>
  Backward state preservation. The source side is DAML and the target side
  matches \<^verbatim>\<open>reg_sm\<close>. \<^verbatim>\<open>unfold_locales\<close> auto-discharges all twelve
  state-machine obligations from the previously registered interpretations,
  so only the five preservation axioms remain pending.
\<close>

interpretation backward_layer_preservation:
  state_preservation
    daml_states reg_actions daml_transition daml_terminal
    reg_states reg_actions reg_transition reg_terminal
    daml_to_reg id
proof unfold_locales
  fix p
  assume "p \<in> daml_states"
  then show "daml_to_reg p \<in> reg_states" using reg_states_UNIV by auto
next
  fix a
  assume "a \<in> reg_actions"
  then show "id a \<in> reg_actions" by simp
next
  fix p
  assume "p \<in> daml_terminal"
  then have "p = reg_to_daml CONFISCATED" unfolding daml_terminal_def by simp
  then have "daml_to_reg p = CONFISCATED" using daml_to_reg_to_daml_id by simp
  then show "daml_to_reg p \<in> reg_terminal" unfolding reg_terminal_def by simp
next
  fix p a p'
  assume "p \<in> daml_states" "a \<in> reg_actions" "daml_transition p a = Some p'"
  then show "reg_transition (daml_to_reg p) (id a) = Some (daml_to_reg p')"
    using daml_to_reg_naturality_some by simp
next
  fix p a
  assume "p \<in> daml_states" "a \<in> reg_actions" "daml_transition p a = None"
  then show "reg_transition (daml_to_reg p) (id a) = None"
    using daml_to_reg_naturality_none by simp
qed

text \<open>
  The symmetric instance: forward and backward state preservation
  composed with roundtrip guarantees. The non-trivial content is the
  bijection between \<^verbatim>\<open>reg_state\<close> and the image of \<^verbatim>\<open>reg_to_daml\<close> in
  \<^verbatim>\<open>daml_perm\<close>; the action map is the identity because both layers share
  the same regulatory action vocabulary.
\<close>

interpretation onchain_daml_bridge:
  symmetric_state_preservation
    reg_states reg_actions reg_transition reg_terminal
    daml_states reg_actions daml_transition daml_terminal
    reg_to_daml id
    daml_to_reg id
proof unfold_locales
  fix s
  assume "s \<in> reg_states"
  then show "daml_to_reg (reg_to_daml s) = s" using daml_to_reg_to_daml_id by simp
next
  fix p
  assume "p \<in> daml_states"
  then show "reg_to_daml (daml_to_reg p) = p" using reg_to_daml_to_reg_on_image by simp
next
  fix a
  assume "a \<in> reg_actions"
  then show "id (id a) = a" by simp
qed

text \<open>
  As a corollary of the symmetric interpretation, \<^verbatim>\<open>reg_to_daml\<close> is
  injective on \<^verbatim>\<open>reg_states\<close>: distinct on-chain states map to distinct
  off-chain DAML records, so the layer-crossing representation incurs
  no information loss.
\<close>

corollary reg_to_daml_injective_on_states:
  "\<lbrakk> s1 \<in> reg_states; s2 \<in> reg_states; reg_to_daml s1 = reg_to_daml s2 \<rbrakk>
   \<Longrightarrow> s1 = s2"
  using onchain_daml_bridge.state_map_injective .


section \<open>Multi-Domain Locale Instantiation\<close>

text \<open>
  We now instantiate the \<^verbatim>\<open>multi_domain_preservation\<close> locale from
  \<^verbatim>\<open>State_Preservation\<close>.thy with the regulatory state machine.

  The instantiation is parametric: given ANY finite set of domains
  and ANY initial \<^verbatim>\<open>domain_state\<close> function satisfying the consistency
  precondition, the locale is satisfied. This proves that the
  abstract framework applies to the concrete regulatory model
  without fixing a specific topology.

  The key bridge: we construct a \<^verbatim>\<open>domain_state\<close> function from our
  \<^verbatim>\<open>global_state\<close>, and show that \<^verbatim>\<open>valid_state\<close> implies the consistency
  precondition required by \<^verbatim>\<open>multi_domain_preservation\<close>.
\<close>

text \<open>
  Bridge from our \<^verbatim>\<open>global_state\<close> model to the \<^verbatim>\<open>multi_domain_preservation\<close>
  locale's \<^verbatim>\<open>domain_state\<close> signature.

  \<^verbatim>\<open>multi_domain_preservation\<close> expects:
    \<^verbatim>\<open>domain_state :: 'd => 'id => 's option\<close>

  We instantiate with:
    'd = \<^verbatim>\<open>chain_id\<close>, 'id = \<^verbatim>\<open>asset_id\<close>, 's = \<^verbatim>\<open>reg_state\<close>

  The bridge function extracts \<^verbatim>\<open>reg_state\<close> from our richer \<^verbatim>\<open>asset_state\<close>.
\<close>

definition reg_domain_state :: "global_state \<Rightarrow> chain_id \<Rightarrow> asset_id \<Rightarrow> reg_state option" where
  "reg_domain_state gs cid aid = get_reg_state gs cid aid"


text \<open>
  The parametric instantiation theorem: for any finite set of \<^verbatim>\<open>chain_ids\<close>
  and any valid \<^verbatim>\<open>global_state\<close>, we can interpret the \<^verbatim>\<open>multi_domain_preservation\<close>
  locale with the regulatory state machine.
\<close>

text \<open>
  The \<^verbatim>\<open>state_machine\<close> predicate as a standalone fact. This is needed for
  instantiating \<^verbatim>\<open>multi_domain_preservation\<close>, which takes \<^verbatim>\<open>state_machine\<close> as
  an opaque predicate assumption.
\<close>

lemma reg_state_machine_pred:
  "state_machine reg_states reg_actions reg_transition reg_terminal"
proof -
  have f1: "finite reg_states" unfolding reg_states_def by auto
  have f2: "finite reg_actions" unfolding reg_actions_def by auto
  have f3: "reg_terminal \<subseteq> reg_states"
    unfolding reg_terminal_def reg_states_def by auto
  have f4: "\<And>s a. s \<in> reg_terminal \<Longrightarrow> a \<in> reg_actions \<Longrightarrow> reg_transition s a = None"
    unfolding reg_terminal_def by (auto simp: confiscated_terminal)
  have f5: "\<And>s a s'. s \<in> reg_states \<Longrightarrow> a \<in> reg_actions \<Longrightarrow>
    reg_transition s a = Some s' \<Longrightarrow> s' \<in> reg_states"
    using reg_transition_closed by auto
  have f6: "\<And>s a. (s :: reg_state) \<notin> reg_states \<Longrightarrow> reg_transition s a = None"
    using reg_states_UNIV by auto
  show ?thesis
    by (intro state_machine.intro) (use f1 f2 f3 f4 f5 f6 in auto)
qed

theorem reg_multi_domain_instantiation:
  assumes fin_doms: "finite (doms :: chain_id set)"
    and valid: "valid_state gs"
  shows "multi_domain_preservation doms reg_states reg_actions reg_transition
           reg_terminal (reg_domain_state gs)"
proof (intro multi_domain_preservation.intro)
  show "finite doms" using fin_doms by simp
next
  show "state_machine reg_states reg_actions reg_transition reg_terminal"
    by (rule reg_state_machine_pred)
next
  fix d1 d2 :: chain_id and aid :: asset_id and s1 s2 :: reg_state
  assume "d1 \<in> doms" "d2 \<in> doms"
    and "reg_domain_state gs d1 aid = Some s1"
    and "reg_domain_state gs d2 aid = Some s2"
  then have "get_reg_state gs d1 aid = Some s1"
    and "get_reg_state gs d2 aid = Some s2"
    unfolding reg_domain_state_def by simp_all
  with valid show "s1 = s2"
    unfolding valid_state_def consistent_state_def by blast
qed


text \<open>
  Corollary: the generic \<^verbatim>\<open>cross_domain_consistency\<close> theorem from
  \<^verbatim>\<open>State_Preservation\<close>.thy applies to regulatory synchronization.

  This connects the abstract theory to the concrete model:
  the generic theorem guarantees that after \<^verbatim>\<open>sync_all\<close> (the abstract
  synchronization), all connected domains agree. Combined with our
  concrete \<^verbatim>\<open>regulatory_homomorphism\<close> theorem, we have both the abstract
  and concrete guarantees.

  The instantiation above (\<^verbatim>\<open>reg_multi_domain_instantiation\<close>) enables
  using all theorems proven in \<^verbatim>\<open>multi_domain_preservation\<close> — in particular
  \<^verbatim>\<open>cross_domain_consistency\<close> and \<^verbatim>\<open>sync_isolation\<close> — for the regulatory model
  without reproving them. Any consumer of this theory can invoke:

    \<^verbatim>\<open>multi_domain_preservation\<close>.\<^verbatim>\<open>cross_domain_consistency\<close>
      [OF \<^verbatim>\<open>reg_multi_domain_instantiation\<close>[OF \<^verbatim>\<open>fin_doms\<close> \<^verbatim>\<open>valid_gs\<close>]]

  to obtain the concrete guarantee for their domain set and global state.
\<close>


text \<open>
  Summary of what this theory establishes:

  1. The regulatory state machine (\<^verbatim>\<open>reg_state\<close>, \<^verbatim>\<open>reg_action\<close>, \<^verbatim>\<open>reg_transition\<close>)
     satisfies the \<^verbatim>\<open>state_machine\<close> locale from \<^verbatim>\<open>State_Preservation\<close>.thy.

  2. CONFISCATED is terminal (I1), CONFISCATE is universally reachable (I2),
     and the transition function is deterministic (I3).

  3. SEIZED to FROZEN and FROZEN to RESTRICTED direct transitions are
     excluded by design, with legal and complexity-reduction justifications.

  4. The synchronization protocol (lock, then update, then unlock) preserves
     cross-chain consistency for the same asset while isolating other assets.

  5. Preemptive locking guards the sync function against a second action
     while the lock is held; under the atomic model this expresses the
     intended exclusion of competing regulatory actions on the same asset
     (NOT double-spend prevention — that is handled at a different layer).

  6. The \<^verbatim>\<open>regulatory_homomorphism\<close> theorem establishes that after sync,
     all connected chains agree on the new regulatory state.

  7. The \<^verbatim>\<open>valid_state_preservation\<close> theorem establishes that sync preserves
     the global validity invariant: \<^verbatim>\<open>consistent_state\<close> AND no outstanding
     locks. This closes the inductive invariant.

  8. The heterogeneous-action instance (\<^verbatim>\<open>escalation_preservation\<close>) instantiates
     \<^verbatim>\<open>state_preservation\<close> with the four-action escalation subset of
     \<^verbatim>\<open>reg_action\<close> on the source side, the dedicated four-constructor
     datatype \<^verbatim>\<open>chain_b_action\<close> on the target side, and the identity state
     map. This exercises both the locale's \<^verbatim>\<open>actions\<^sub>s\<close> subset parameter
     and the heterogeneous source / target action types.

  9. The layer-crossing instance (\<^verbatim>\<open>onchain_daml_bridge\<close>) instantiates
     \<^verbatim>\<open>symmetric_state_preservation\<close> with the on-chain enum representation
     and a structured DAML permission record (\<^verbatim>\<open>daml_perm\<close>) carrying
     auxiliary fields. The action vocabularies coincide so the action map
     is the identity; the non-trivial content is the bijection between
     the enum and the image \<^verbatim>\<open>daml_states\<close> of the representation map,
     with a type-level invariant (\<^verbatim>\<open>valid_daml_perm\<close>) tying the auxiliary
     fields to the status tag.

  10. The \<^verbatim>\<open>multi_domain_preservation\<close> locale is instantiated parametrically:
      for any finite domain set and valid global state, the abstract
      framework from \<^verbatim>\<open>State_Preservation\<close>.thy applies to the regulatory
      model.

  Open work for subsequent entries:
    - Eventual consistency under the partially synchronous network model
      (with message delays, redelivery, and out-of-order arrival).
\<close>

end
