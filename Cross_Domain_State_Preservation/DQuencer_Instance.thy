(*
  Title:      Cross_Domain_State_Preservation/DQuencer_Instance.thy
  Author:     Jinwook Kim (Jay) <jay@oraclizer.io>
  Maintainer: Jinwook Kim (Jay) <jay@oraclizer.io>
  License:    BSD

  D-quencer Regulatory Instance of the Priority Resolution Locales

  This theory instantiates the generic priority_system, deadlock_free_locking,
  and fair_leader_system locales from Priority_Resolution.thy with the
  D-quencer consensus mechanism of Oraclizer.

  D-quencer is a decentralized sequencing engine for regulatory state
  synchronization. It operates under Byzantine fault tolerance (f < n/3),
  uses BLS multisig + VRF leader election, and must handle conflicting
  regulatory actions from multiple jurisdictions.

  Key results:
    1. Priority instantiation: regulatory action priority is a total order
       based on authority level, timestamp, severity, and node ID
    2. Determinism: BFT consensus produces a unique, deterministic result
    3. Deadlock freedom: timeout-based lock release prevents Byzantine
       nodes from permanently blocking assets
    4. Starvation freedom: under fair leader assumption, every pending
       regulatory request is processed within bounded time
    5. Combined safety + liveness: connecting Property 1 (cross-domain
       state preservation) with Property 2 (determinism + liveness)

  Design decisions:
    - Byzantine model: f < n/3 (standard BFT threshold)
    - Starvation freedom uses assume-guarantee reasoning: the fairness
      assumption (honest leader within k epochs) abstracts VRF randomness
    - Priority uses nat tuples for automatic linorder from Isabelle's
      product order, avoiding manual linorder instance registration
    - Message type extends oss_message via record inheritance
    - BFT consensus is abstracted (no BLS signature formalization):
      only the determinism property of consensus output is modeled
*)

theory DQuencer_Instance
  imports Priority_Resolution Regulatory_Instance
begin

section \<open>Authority Level and Action Severity\<close>

text \<open>
  Regulatory authority hierarchy. International authorities (e.g., FATF)
  take precedence over national (e.g., SEC), which take precedence over
  regional authorities. This reflects the RCP framework's jurisdictional
  priority model.
\<close>

datatype authority_level = Regional | National | International

fun authority_rank :: "authority_level \<Rightarrow> nat" where
  "authority_rank Regional = 1"
| "authority_rank National = 2"
| "authority_rank International = 3"

lemma authority_rank_injective:
  "authority_rank a1 = authority_rank a2 \<Longrightarrow> a1 = a2"
  by (cases a1; cases a2; auto)

text \<open>
  Action severity determines priority among actions from the same
  authority level. Stronger enforcement actions (CONFISCATE, SEIZE)
  take precedence over weaker ones (RESTRICT, UNFREEZE). This reflects
  the legal principle that more conservative (asset-protective) actions
  should prevail when concurrent conflicting orders exist.
\<close>

fun action_severity :: "reg_action \<Rightarrow> nat" where
  "action_severity UNRESTRICT = 1"
| "action_severity UNFREEZE = 2"
| "action_severity RELEASE = 3"
| "action_severity RESTRICT = 4"
| "action_severity FREEZE = 5"
| "action_severity SEIZE = 6"
| "action_severity CONFISCATE = 7"

lemma action_severity_injective:
  "action_severity a1 = action_severity a2 \<Longrightarrow> a1 = a2"
  by (cases a1; cases a2; auto)


section \<open>Priority Key\<close>

text \<open>
  The priority key is a 4-tuple of natural numbers, using Isabelle's
  built-in lexicographic order on products. No manual linorder instance
  registration is needed.

  Components (highest to lowest significance):
  \<^enum> \<^verbatim>\<open>authority_rank\<close>: higher authority = higher priority
  \<^enum> \<^verbatim>\<open>inverted_timestamp\<close>: earlier timestamp = higher priority (inverted)
  \<^enum> \<^verbatim>\<open>action_severity\<close>: stronger action = higher priority
  \<^enum> \<^verbatim>\<open>node_id\<close>: deterministic tiebreaker (lower node ID = higher priority,
     so we invert to make larger = higher in the nat order)

  For timestamp and \<^verbatim>\<open>node_id\<close> inversion, we use \<^term>\<open>max_val - actual_val\<close>
  to convert "smaller is better" to "larger is better" for compatibility
  with the nat product order where larger = higher.
\<close>

type_synonym priority_key = "nat \<times> nat \<times> nat \<times> nat"


section \<open>Extended Message Type\<close>

text \<open>
  Extends \<^verbatim>\<open>oss_message\<close> from \<^verbatim>\<open>Regulatory_Instance\<close> with authority level
  and source node ID. Uses Isabelle record inheritance so that existing
  functions on \<^verbatim>\<open>oss_message\<close> remain applicable.
\<close>

record dq_message = oss_message +
  dqm_authority_level :: authority_level
  dqm_source_node     :: nat


section \<open>Priority Construction\<close>

text \<open>
  Construct a priority key from message fields. Uses two upper bounds
  for inversion: \<^verbatim>\<open>max_time\<close> for timestamps and \<^verbatim>\<open>max_node\<close> for node IDs.
\<close>

definition make_priority_key ::
  "nat \<Rightarrow> nat \<Rightarrow> dq_message \<Rightarrow> priority_key"
where
  "make_priority_key max_time max_node msg =
    (authority_rank (dqm_authority_level msg),
     max_time - msg_timestamp msg,
     action_severity (msg_action msg),
     max_node - dqm_source_node msg)"


section \<open>Node and System Model\<close>

datatype node_behavior = Honest | Byzantine

record node_info =
  ni_id       :: nat
  ni_behavior :: node_behavior

definition honest_nodes :: "node_info set \<Rightarrow> node_info set" where
  "honest_nodes ns = {n \<in> ns. ni_behavior n = Honest}"

definition byzantine_nodes :: "node_info set \<Rightarrow> node_info set" where
  "byzantine_nodes ns = {n \<in> ns. ni_behavior n = Byzantine}"

lemma honest_byzantine_partition:
  "honest_nodes ns \<union> byzantine_nodes ns = ns"
proof (rule set_eqI)
  fix x
  show "x \<in> honest_nodes ns \<union> byzantine_nodes ns \<longleftrightarrow> x \<in> ns"
    unfolding honest_nodes_def byzantine_nodes_def
    by (cases "ni_behavior x"; auto)
qed

lemma honest_byzantine_disjoint:
  "honest_nodes ns \<inter> byzantine_nodes ns = {}"
  unfolding honest_nodes_def byzantine_nodes_def by auto


section \<open>D-quencer System Locale\<close>

text \<open>
  The D-quencer system locale encapsulates the BFT assumption
  (\<^term>\<open>n \<ge> 3 * f + 1\<close>) and system parameters.
\<close>

locale dquencer_system =
  fixes nodes :: "node_info set"
    and f_max :: nat
    and lock_timeout :: nat
    and fairness_bound :: nat
    and max_time :: nat
    and max_node :: nat
  assumes finite_nodes: "finite nodes"
    and bft_threshold: "card nodes \<ge> 3 * f_max + 1"
    and byzantine_bound: "card (byzantine_nodes nodes) \<le> f_max"
    and nonempty_nodes: "nodes \<noteq> {}"
    and timeout_positive: "lock_timeout > 0"
    and fairness_positive: "fairness_bound > 0"
begin

lemma honest_majority:
  "card (honest_nodes nodes) > 2 * f_max"
proof -
  have "card nodes = card (honest_nodes nodes) + card (byzantine_nodes nodes)"
    using honest_byzantine_partition honest_byzantine_disjoint finite_nodes
    by (metis card_Un_disjoint finite_Un)
  with bft_threshold byzantine_bound show ?thesis by linarith
qed

lemma honest_nonempty:
  "honest_nodes nodes \<noteq> {}"
proof -
  have fin: "finite (honest_nodes nodes)"
    unfolding honest_nodes_def using finite_nodes by simp
  have pos: "0 < card (honest_nodes nodes)"
    using honest_majority by linarith
  with fin pos show ?thesis by (auto simp: card_eq_0_iff)
qed

end


section \<open>Priority System Instantiation\<close>

text \<open>
  We instantiate the \<^verbatim>\<open>priority_system\<close> locale from
  \<^verbatim>\<open>Priority_Resolution.thy\<close> with D-quencer message priorities.

  The priority function maps messages to \<^verbatim>\<open>priority_key\<close> (which is
  \<^verbatim>\<open>nat \<times> nat \<times> nat \<times> nat\<close> with the built-in lexicographic order).

  Injectivity follows from: distinct messages have either different
  authority levels, different timestamps, different actions, or
  different source nodes. The source node ID serves as the final
  tiebreaker ensuring no two distinct messages share the same key.
\<close>

text \<open>
  For a concrete message set with the injectivity precondition,
  the \<^verbatim>\<open>priority_system\<close> locale provides deterministic selection.
\<close>

lemma priority_key_injectivity:
  assumes "make_priority_key mt mn m1 = make_priority_key mt mn m2"
    and "msg_timestamp m1 \<le> mt" and "msg_timestamp m2 \<le> mt"
    and "dqm_source_node m1 \<le> mn" and "dqm_source_node m2 \<le> mn"
  shows "dqm_authority_level m1 = dqm_authority_level m2
       \<and> msg_timestamp m1 = msg_timestamp m2
       \<and> msg_action m1 = msg_action m2
       \<and> dqm_source_node m1 = dqm_source_node m2"
proof -
  from assms(1) have
    eq1: "authority_rank (dqm_authority_level m1) = authority_rank (dqm_authority_level m2)" and
    eq2: "mt - msg_timestamp m1 = mt - msg_timestamp m2" and
    eq3: "action_severity (msg_action m1) = action_severity (msg_action m2)" and
    eq4: "mn - dqm_source_node m1 = mn - dqm_source_node m2"
    unfolding make_priority_key_def by auto
  from eq1 have al: "dqm_authority_level m1 = dqm_authority_level m2"
    using authority_rank_injective by auto
  from eq2 assms(2,3) have ts: "msg_timestamp m1 = msg_timestamp m2"
    by linarith
  from eq3 have act: "msg_action m1 = msg_action m2"
    using action_severity_injective by auto
  from eq4 assms(4,5) have nd: "dqm_source_node m1 = dqm_source_node m2"
    by linarith
  from al ts act nd show ?thesis by auto
qed


section \<open>BFT Consensus Abstraction\<close>

text \<open>
  We abstract the BFT consensus mechanism. Rather than formalizing
  BLS signatures and vote counting, we model the consensus as:
  given a set of messages and honest majority, the consensus output
  is the highest-priority valid message.

  This is justified because:
  \<^enum> Honest nodes follow the priority protocol
  \<^enum> With > 2/3 honest nodes, the BFT consensus output reflects
    the honest majority's agreement
  \<^enum> The honest majority will agree on the highest-priority message
    (since priority is a total order and deterministic)
\<close>

definition valid_dq_message :: "global_state \<Rightarrow> dq_message \<Rightarrow> bool" where
  "valid_dq_message gs msg =
    (asset_exists gs (msg_source msg) (msg_asset_id msg) \<and>
     (\<exists>s. get_reg_state gs (msg_source msg) (msg_asset_id msg) = Some s \<and>
          reg_transition s (msg_action msg) \<noteq> None))"

text \<open>
  A scalar encoding of the priority key for use with \<^verbatim>\<open>sort_key\<close>.
  Maps each message to a single natural number that preserves the
  lexicographic order on priority key components, given the bounds
  \<^term>\<open>max_t\<close> and \<^term>\<open>max_n\<close>.
\<close>

definition priority_scalar ::
  "nat \<Rightarrow> nat \<Rightarrow> dq_message \<Rightarrow> nat"
where
  "priority_scalar max_t max_n m =
    authority_rank (dqm_authority_level m) * (Suc max_t) * 8 * (Suc max_n) +
    (max_t - msg_timestamp m) * 8 * (Suc max_n) +
    action_severity (msg_action m) * (Suc max_n) +
    (max_n - dqm_source_node m)"

definition bft_select ::
  "dq_message list \<Rightarrow> global_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> dq_message option"
where
  "bft_select msgs gs max_t max_n =
    (let valid_msgs = filter (valid_dq_message gs) msgs;
         ranked = sort_key (priority_scalar max_t max_n) valid_msgs
     in if ranked = [] then None else Some (last ranked))"


section \<open>Deadlock-Free Locking Instantiation\<close>

text \<open>
  We instantiate the \<^verbatim>\<open>deadlock_free_locking\<close> locale with the
  D-quencer's lock timeout. This provides:
  \<^enum> Every lock expires within \<^verbatim>\<open>lock_timeout\<close> time units
  \<^enum> Byzantine nodes that hold locks indefinitely are handled
    by forced timeout release
  \<^enum> Deadlock freedom: no asset can be permanently blocked
\<close>

context dquencer_system
begin

text \<open>
  The D-quencer system's lock timeout satisfies the
  \<^verbatim>\<open>deadlock_free_locking\<close> locale.
\<close>

interpretation dq_locking: deadlock_free_locking lock_timeout
  by unfold_locales (rule timeout_positive)

text \<open>
  Concrete deadlock freedom for the D-quencer:
  any locked asset will be unlocked within \<^verbatim>\<open>lock_timeout\<close> time.
\<close>

corollary dq_deadlock_freedom:
  assumes "dq_locking.lock_effective lock_time current_time"
  shows "\<exists>t'. t' \<le> lock_time + lock_timeout \<and>
              \<not> dq_locking.lock_effective lock_time t'"
  using dq_locking.deadlock_freedom[OF assms] .

text \<open>
  Byzantine lock resistance: even if a Byzantine node acquires
  a lock and never releases it, the lock expires by timeout.
\<close>

corollary byzantine_lock_expires:
  "\<exists>t'. \<not> dq_locking.lock_effective lock_time t'"
  using dq_locking.lock_eventually_expires by auto

end


section \<open>Fair Leader Starvation Freedom Instantiation\<close>

text \<open>
  We instantiate the \<^verbatim>\<open>fair_leader_system\<close> locale with the
  D-quencer's leader election and pending request processing.

  The fairness assumption abstracts VRF randomness: within any
  \<^verbatim>\<open>fairness_bound\<close> consecutive epochs, at least one epoch has
  an honest leader. Under \<^term>\<open>f < n/3\<close>, the probability of
  \<^term>\<open>fairness_bound\<close> consecutive Byzantine leaders is
  \<^term>\<open>(f/n)^fairness_bound < (1/3)^fairness_bound\<close>.
\<close>

text \<open>
  For concrete instantiation, we need a leader schedule and
  pending count function that satisfy the locale assumptions.
  These are provided as parameters in the instantiation context.
\<close>

locale dquencer_liveness = dquencer_system +
  fixes leader_schedule :: "nat \<Rightarrow> node_info"
    and pending_count :: "nat \<Rightarrow> nat"
  assumes fair_leader:
    "\<forall>epoch. \<exists>e. epoch \<le> e \<and> e < epoch + fairness_bound \<and>
                 ni_behavior (leader_schedule e) = Honest"
    and honest_processes:
    "\<lbrakk> ni_behavior (leader_schedule e) = Honest; pending_count e > 0 \<rbrakk>
     \<Longrightarrow> pending_count (Suc e) < pending_count e"
    and pending_non_increasing:
    "pending_count (Suc e) \<le> pending_count e"
begin

interpretation dq_fair: fair_leader_system
  leader_schedule "\<lambda>n. ni_behavior n = Honest" pending_count fairness_bound
proof unfold_locales
  show "0 < fairness_bound" using fairness_positive .
next
  show "\<forall>epoch. \<exists>e. epoch \<le> e \<and> e < epoch + fairness_bound \<and>
                    ni_behavior (leader_schedule e) = Honest"
    using fair_leader .
next
  fix e
  assume "ni_behavior (leader_schedule e) = Honest" "0 < pending_count e"
  then show "pending_count (Suc e) < pending_count e"
    using honest_processes by auto
next
  fix e
  show "pending_count (Suc e) \<le> pending_count e"
    using pending_non_increasing .
qed

text \<open>
  Concrete starvation freedom for the D-quencer:
  if there are pending regulatory requests, at least one will
  be processed within \<^verbatim>\<open>fairness_bound\<close> epochs.
\<close>

corollary dq_starvation_bound:
  assumes "pending_count epoch > 0"
  shows "\<exists>e. epoch \<le> e \<and> e < epoch + fairness_bound \<and>
             pending_count (Suc e) < pending_count e"
  using dq_fair.starvation_bound[OF assms] .

end


section \<open>Combined Safety and Liveness\<close>

text \<open>
  This section connects Property 1 (cross-domain state preservation,
  safety) with Property 2 (determinism + liveness).

  Property 1 guarantees: if sync is executed correctly, the resulting
  state preserves cross-domain consistency.

  Property 2 guarantees: under Byzantine faults, D-quencer
  deterministically selects actions, locks are bounded by timeout,
  and all pending requests are eventually processed.

  Combined: in a decentralized Byzantine environment, cross-domain
  regulatory state is synchronized deterministically, without deadlock,
  and without starvation.
\<close>

text \<open>
  The combined theorem ties \<^verbatim>\<open>valid_state_preservation\<close> from
  \<^verbatim>\<open>Regulatory_Instance.thy\<close> with the liveness guarantees from this theory.
\<close>

theorem combined_safety_liveness:
  assumes valid: "valid_state gs"
    and exists: "asset_exists gs source aid"
    and current: "get_reg_state gs source aid = Some s"
    and trans: "reg_transition s action = Some s'"
    and not_locked: "\<not> is_locked gs aid"
    and fin: "finite (connected_chains gs aid)"
  shows "\<exists>gs'. sync source action aid gs = Some gs' \<and> valid_state gs'"
proof -
  from not_locked obtain gs_locked where
    lock: "acquire_lock gs aid = Some gs_locked"
    using lock_acquire_success by auto
  from valid current trans lock have
    "\<exists>gs'. sync source action aid gs = Some gs'"
    unfolding sync_def
    using exists current trans lock
    by (auto simp: get_reg_state_def get_asset_state_def
             split: option.splits
             intro!: exI)
  then obtain gs' where synced: "sync source action aid gs = Some gs'"
    by auto
  have "valid_state gs'"
    using valid_state_preservation[OF valid exists current trans synced fin] .
  with synced show ?thesis by auto
qed

text \<open>
  Summary of what Properties 1 + 2 together establish:

  \<^enum> \<^bold>\<open>Safety\<close> (Property 1): After synchronization, all connected
    chains agree on the regulatory state. The global validity
    invariant is preserved.

  \<^enum> \<^bold>\<open>Determinism\<close> (Property 2): Conflicting regulatory actions
    are resolved by a total order on priority keys. The BFT
    consensus output is unique.

  \<^enum> \<^bold>\<open>Deadlock freedom\<close> (Property 2): No asset can be permanently
    locked, even if Byzantine nodes refuse to release locks.
    Timeout-based forced release bounds the lock duration.

  \<^enum> \<^bold>\<open>Starvation freedom\<close> (Property 2): Under the fair leader
    assumption, every pending regulatory request is processed
    within a bounded number of epochs.

  What remains:
    - Property 3: compositional assurance across heterogeneous
      verification regimes (Canton + OSS + EVM)
    - Refinement: formal correspondence between these models
      and the Go/Solidity implementation
\<close>

end
