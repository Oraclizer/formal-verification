(*
  Title:      Cross_Domain_State_Preservation/Regulatory_Instance.thy
  Author:     Jinwook Kim (Jay) <jay@oraclizer.io>
  Maintainer: Jinwook Kim (Jay) <jay@oraclizer.io>
  License:    BSD

  Regulatory Domain Instance of the Cross-Domain State Preservation Functor

  This theory instantiates the generic state_machine and multi_domain_preservation
  locales from State_Preservation.thy with the regulatory state model of
  Oraclizer, a state synchronization oracle for tokenized assets across
  blockchain networks and off-chain ledgers.

  Regulatory states: ACTIVE, FROZEN, SEIZED, CONFISCATED, RESTRICTED
  Regulatory actions: FREEZE, SEIZE, CONFISCATE, RESTRICT, UNFREEZE, UNRESTRICT, RELEASE

  Key results:
    1. State machine interpretation: reg_transition satisfies state_machine locale
    2. Invariants:
       - I1: CONFISCATED is terminal (absorbing)
       - I2: CONFISCATE is reachable from every non-terminal state
       - I3: Determinism (inherent from function definition)
    3. Transition exclusions with legal justification:
       - SEIZED → FROZEN (SEIZED is a strictly stronger constraint)
       - FROZEN → RESTRICTED (must return to ACTIVE first)
    4. Synchronization correctness:
       - regulatory_homomorphism: after sync, all connected chains agree
       - Sync isolation: synchronization does not affect other assets
       - Preemptive locking: prevents concurrent regulatory action conflicts
    5. Valid state preservation: sync preserves the global validity invariant
       (consistent_state ∧ no_locked_without_reason)
    6. Multi-domain parametric instantiation: the generic
       multi_domain_preservation locale applies to the regulatory model
       for any finite domain set

  Design decisions (justified by legal precedence and operational scope):
    - RECOVER and LIQUIDATE excluded (force transfer / external DEX, not state transitions)
    - SEIZED → FROZEN excluded (legally, SEIZED is a stronger constraint)
    - FROZEN → RESTRICTED excluded (must go through ACTIVE)
    - Locking scope: concurrent regulatory action prevention, NOT double-spend prevention
*)

theory Regulatory_Instance
  imports State_Preservation
begin

section \<open>Regulatory State and Action Definitions\<close>

datatype reg_state = ACTIVE | FROZEN | SEIZED | CONFISCATED | RESTRICTED

datatype reg_action = FREEZE | SEIZE | CONFISCATE | RESTRICT
                    | UNFREEZE | UNRESTRICT | RELEASE

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

text \<open>Determinism is trivially guaranteed by the \<^theory_text>\<open>fun\<close> definition.\<close>

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
type_synonym authority_id = nat
type_synonym timestamp = nat

record asset_state =
  as_asset_id  :: asset_id
  as_reg_state :: reg_state
  as_owner     :: nat         \<comment> \<open>Abstract address\<close>
  as_locked    :: bool        \<comment> \<open>Preemptive lock\<close>

type_synonym chain_state = "asset_id \<Rightarrow> asset_state option"

record global_state =
  gs_chains    :: "chain_id \<Rightarrow> chain_state"
  gs_locks     :: "asset_id \<Rightarrow> bool"

record oss_message =
  msg_action    :: reg_action
  msg_asset_id  :: asset_id
  msg_authority :: authority_id
  msg_timestamp :: timestamp
  msg_source    :: chain_id
  msg_targets   :: "chain_id set"


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
  \<comment> \<open>In a quiescent valid state, no assets are locked.
      Locks are transient, held only during sync operations.\<close>

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

text \<open>
  Update the regulatory state of an asset on a specific chain.
  Preserves all other asset fields (owner, etc.).
\<close>

definition update_chain_reg_state ::
  "global_state \<Rightarrow> chain_id \<Rightarrow> asset_id \<Rightarrow> reg_state \<Rightarrow> global_state"
where
  "update_chain_reg_state gs cid aid new_st =
    (let old_chain = gs_chains gs cid in
     let new_chain = (\<lambda>aid'.
       if aid' = aid then
         (case old_chain aid of
            None \<Rightarrow> None
          | Some ast \<Rightarrow> Some (ast\<lparr> as_reg_state := new_st \<rparr>))
       else old_chain aid')
     in gs\<lparr> gs_chains := (gs_chains gs)(cid := new_chain) \<rparr>)"

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

  Returns None if any step fails (invalid transition, lock contention, etc.)
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

subsection \<open>Idempotency\<close>

text \<open>
  After synchronization, applying the same action again yields None
  (the state has already transitioned, so the same transition from
  the new state is typically invalid) or is a no-op.

  More precisely: if sync succeeds and produces \<^verbatim>\<open>new_st\<close>, then
  \<^verbatim>\<open>reg_transition\<close> \<^verbatim>\<open>new_st\<close> action = None for most action/state pairs
  (the transition table has no self-loops).
\<close>

lemma no_self_loops:
  "reg_transition s a = Some s \<Longrightarrow> False"
  by (cases s; cases a; auto)

lemma transition_changes_state:
  "reg_transition s a = Some s' \<Longrightarrow> s \<noteq> s'"
  using no_self_loops by auto

subsection \<open>Sync isolation: other assets are not affected\<close>

text \<open>
  Synchronization on asset aid does not change the state of any
  other asset (where the asset identifier differs) on any chain.
\<close>

lemma update_chain_other_asset:
  assumes "aid' \<noteq> aid"
  shows "gs_chains (update_chain_reg_state gs cid aid new_st) cid' aid' =
         gs_chains gs cid' aid'"
proof (cases "cid' = cid")
  case True
  then show ?thesis
    unfolding update_chain_reg_state_def Let_def
    using assms by auto
next
  case False
  then show ?thesis
    unfolding update_chain_reg_state_def Let_def by auto
qed

subsection \<open>Sync correctness: source chain updated\<close>

text \<open>
  After \<^verbatim>\<open>update_chain_reg_state\<close>, the target chain reflects the new state.
\<close>

lemma update_chain_same_asset:
  assumes "gs_chains gs cid aid = Some ast"
  shows "gs_chains (update_chain_reg_state gs cid aid new_st) cid aid =
         Some (ast\<lparr> as_reg_state := new_st \<rparr>)"
  unfolding update_chain_reg_state_def Let_def
  using assms by auto

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

lemma update_all_chains_in_targets_none:
  assumes "cid \<in> targets"
    and "gs_chains gs cid aid = None"
  shows "gs_chains (update_all_chains gs aid new_st targets) cid aid = None"
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
  If a lock is held, concurrent sync on the same asset fails.
  This prevents concurrent regulatory action conflicts.
\<close>

lemma lock_mutual_exclusion:
  assumes "is_locked gs aid"
  shows "acquire_lock gs aid = None"
  unfolding acquire_lock_def using assms by auto

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

lemma lock_release:
  shows "\<not> is_locked (release_lock gs aid) aid"
  unfolding release_lock_def is_locked_def by auto


section \<open>Main Theorem: Cross-Chain Regulatory Consistency\<close>

text \<open>
  The central theorem of this theory. Under a valid global state
  (all chains consistent, no outstanding locks), if a regulatory
  action is applied via sync, the resulting state is also valid
  (all chains consistent) and every connected chain reflects the
  new regulatory state.

  This is the regulatory instantiation of the cross-domain consistency
  theorem from \<^verbatim>\<open>State_Preservation\<close>.thy.

  The proof proceeds by:
  1. Unfolding sync into lock, then \<^verbatim>\<open>update_all_chains\<close>, then unlock
  2. Showing \<^verbatim>\<open>acquire_lock\<close> and \<^verbatim>\<open>release_lock\<close> preserve chain state
  3. Showing \<^verbatim>\<open>update_all_chains\<close> updates every chain in the target set
  4. Combining these facts to establish the conclusion
\<close>

text \<open>
  Auxiliary: update on a single chain preserves consistency for other assets.
\<close>

lemma update_chain_preserves_other_consistency:
  assumes "consistent_state gs"
    and "aid' \<noteq> aid"
    and "get_reg_state gs c1 aid' = Some s1"
    and "get_reg_state gs c2 aid' = Some s2"
  shows "get_reg_state (update_chain_reg_state gs cid aid new_st) c1 aid' = Some s1
       \<and> get_reg_state (update_chain_reg_state gs cid aid new_st) c2 aid' = Some s2"
  using assms unfolding get_reg_state_def get_asset_state_def
    update_chain_reg_state_def Let_def consistent_state_def
  by auto

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

lemma acquire_lock_reg_state:
  assumes "acquire_lock gs aid = Some gs'"
  shows "get_reg_state gs' cid aid' = get_reg_state gs cid aid'"
  using acquire_lock_chains[OF assms]
  unfolding get_reg_state_def get_asset_state_def by simp

text \<open>
  Auxiliary: \<^verbatim>\<open>connected_chains\<close> uses original gs, not locked gs.
\<close>

lemma acquire_lock_asset_exists:
  assumes "acquire_lock gs aid = Some gs'"
  shows "asset_exists gs' cid aid' = asset_exists gs cid aid'"
  using acquire_lock_chains[OF assms]
  unfolding asset_exists_def get_asset_state_def by simp

text \<open>
  The cross-chain regulatory homomorphism theorem.
\<close>

theorem regulatory_homomorphism:
  assumes valid: "valid_state gs"
    and exists: "asset_exists gs source aid"
    and current: "get_reg_state gs source aid = Some s"
    and trans: "reg_transition s action = Some s'"
    and synced: "sync source action aid gs = Some gs'"
    and connected: "c \<in> connected_chains gs aid"
    and fin: "finite (connected_chains gs aid)"
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
    and exists: "asset_exists gs source aid"
    and current: "get_reg_state gs source aid = Some s"
    and trans: "reg_transition s action = Some s'"
    and synced: "sync source action aid gs = Some gs'"
    and fin: "finite (connected_chains gs aid)"
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
    and exists: "asset_exists gs source aid"
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
    and exists: "asset_exists gs source aid"
    and current: "get_reg_state gs source aid = Some s"
    and trans: "reg_transition s action = Some s'"
    and synced: "sync source action aid gs = Some gs'"
    and fin: "finite (connected_chains gs aid)"
  shows "valid_state gs'"
  unfolding valid_state_def
  using sync_preserves_consistent_state[OF assms]
        sync_preserves_no_locks[OF valid exists current trans synced]
  by auto


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

  5. Preemptive locking prevents concurrent regulatory actions on the
     same asset (NOT double-spend prevention — that is handled at a
     different layer).

  6. The \<^verbatim>\<open>regulatory_homomorphism\<close> theorem establishes that after sync,
     all connected chains agree on the new regulatory state.

  7. The \<^verbatim>\<open>valid_state_preservation\<close> theorem establishes that sync preserves
     the global validity invariant: \<^verbatim>\<open>consistent_state\<close> AND no outstanding
     locks. This closes the inductive invariant.

  8. The \<^verbatim>\<open>multi_domain_preservation\<close> locale is instantiated parametrically:
     for any finite domain set and valid global state, the abstract
     framework from \<^verbatim>\<open>State_Preservation\<close>.thy applies to the regulatory model.

  What remains for future work:
    - Prove eventual consistency under the partially synchronous network
      model (with message delays, redelivery, and out-of-order arrival)
    - (Optional) Connect to the \<^verbatim>\<open>state_preservation\<close> locale with identity
      state/action maps for the uniform-model case
\<close>

end
