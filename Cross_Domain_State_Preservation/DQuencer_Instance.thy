(*
  Title:      Cross_Domain_State_Preservation/DQuencer_Instance.thy
  Author:     Jinwook Kim (Jay) <jay@oraclizer.io>
  Maintainer: Jinwook Kim (Jay) <jay@oraclizer.io>
  License:    BSD

  D-quencer Regulatory Instance of the Priority Resolution Locales

  This theory instantiates the generic locales priority_system and
  fair_leader_system from Priority_Resolution.thy with the D-quencer
  consensus mechanism of Oraclizer.

  In the Oraclizer product the D-quencer is a decentralized sequencing
  engine (BLS multisig with VRF leader election). That distributed
  consensus is product context, not what this theory formalizes: here the
  sequencer is abstracted as deterministic priority selection under a
  static Byzantine-threshold assumption, a cardinality bound (f < n/3) on
  a two-valued node tag, with conflicting regulatory actions from multiple
  jurisdictions resolved by a total priority order. BLS, VRF, network
  messaging, and adversarial node behaviour are not formalized (see the
  design decisions below).

  Locale instantiations provided in this theory:
    1. priority_system (dq_priority): instantiated on the
       \<^verbatim>\<open>priority_key\<close> type (the lexicographic four-tuple
       authority_rank, inverted timestamp, action_severity, inverted
       source node id) with the identity function as the priority
       projection. Injectivity then holds by reflexivity on the
       carrier. The connection back to D-quencer messages is established inside a
       sublocale \<^verbatim>\<open>dquencer_priority_concrete\<close>, which fixes a
       well-formed message set with distinct priority keys and provides
       a definition \<^verbatim>\<open>recover_msg\<close> mapping each priority key in the
       induced priority-key set back to its unique message via the
       priority-key distinctness assumption; the well-formedness bounds
       feed the field-level injectivity lemma \<^verbatim>\<open>priority_key_injectivity\<close>,
       lifted into the context as \<^verbatim>\<open>msg_priority_key_field_injective\<close>.
    2. fair_leader_system (dq_fair): instantiated within a sublocale
       dquencer_liveness extending dquencer_system with a leader schedule
       and pending-count function satisfying the locale assumptions.

  Key results:
    1. Priority instantiation: regulatory action priority is a total order
       based on authority level, timestamp, severity, and node ID.
    2. Determinism: the priority-ordered selection produces a unique,
       deterministic result (a total order on priority keys, not a BFT
       consensus protocol).
    3. Deadlock: out of scope (not a proved result). The atomic sync model
       has no concurrent lock contention, so deadlock does not arise within
       the model's scope; forced lock release under contention is deferred
       to the preemptive-lock property.
    4. Starvation freedom: under the fair leader assumption, every pending
       regulatory request is processed within a bounded number of epochs.
    5. Conditional safety: conditional_safety_preservation restates
       valid_state_preservation under an unlocked precondition. Its proof
       uses only the safety side and does not fuse liveness; the genuine
       fusion is oraclizer_guarded_bounded_convergence (Functor_Laws.thy).

  Design decisions:
    - Byzantine model: f < n/3 (standard BFT threshold).
    - Starvation freedom uses assume-guarantee reasoning: the fairness
      assumption (honest leader within k epochs) abstracts VRF randomness.
    - Priority uses nat tuples for automatic linorder from Isabelle's
      product order, avoiding manual linorder instance registration.
    - Message type extends oss_message via record inheritance.
    - BFT consensus is abstracted (no BLS signature formalization):
      only the determinism property of consensus output is modeled.
    - The priority_system instantiation is performed on the
      \<^verbatim>\<open>priority_key\<close> type as carrier with the identity priority
      projection, so the locale's unconditional injectivity assumption
      reduces to reflexivity. The corresponding D-quencer message is
      recovered via the definition \<^verbatim>\<open>recover_msg\<close> inside the
      \<^verbatim>\<open>dquencer_priority_concrete\<close> sublocale, which relies on the
      priority-key distinctness hypothesis (\<^verbatim>\<open>msg_set_priority_distinct\<close>);
      the well-formedness bounds enter through the field-level injectivity
      lift (\<^verbatim>\<open>msg_priority_key_field_injective\<close>).
*)

theory DQuencer_Instance
  imports Priority_Resolution Regulatory_Instance "HOL-Library.Product_Lexorder"
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
  authority level and timestamp (it is the third component of the
  lexicographic key). Stronger enforcement actions (CONFISCATE, SEIZE)
  take precedence over weaker ones (RESTRICT, UNFREEZE). This reflects
  the legal principle that more conservative (asset-protective) actions
  prevail when conflicting orders must be ranked against one another.
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
    and fairness_bound :: nat
    and max_time :: nat
    and max_node :: nat
  assumes finite_nodes: "finite nodes"
    and bft_threshold: "card nodes \<ge> 3 * f_max + 1"
    and byzantine_bound: "card (byzantine_nodes nodes) \<le> f_max"
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


text \<open>
  Auxiliary corollary: under the well-formedness bounds, equal priority
  keys imply equal messages on every priority-relevant field.

  The generic \<^verbatim>\<open>priority_system\<close> locale assumes priority injectivity
  unconditionally on its carrier type. We instantiate it with the
  identity function on \<^verbatim>\<open>priority_key\<close> as the carrier; injectivity
  holds by reflexivity on the carrier. The recovery of the unique
  D-quencer message corresponding to a chosen priority key is provided
  as a corollary inside the \<^verbatim>\<open>dquencer_priority_concrete\<close> locale,
  using the well-formedness bounds and the additional priority-key
  distinctness assumption.
\<close>

interpretation dq_priority:
  priority_system "id :: priority_key \<Rightarrow> priority_key"
  by unfold_locales auto

text \<open>
  The \<^verbatim>\<open>dquencer_priority_context\<close> locale extends \<^verbatim>\<open>dquencer_system\<close> with a
  fixed message set whose elements satisfy the well-formedness bounds.
  Together with the bound-preservation, this set induces the priority key
  set \<^verbatim>\<open>msg_priority_keys\<close> on which priority-based selection operates.
\<close>

locale dquencer_priority_context = dquencer_system +
  fixes msg_set :: "dq_message set"
  assumes msg_set_nonempty: "msg_set \<noteq> {}"
    and msg_set_well_formed:
      "\<And>m. m \<in> msg_set \<Longrightarrow> msg_timestamp m \<le> max_time
                            \<and> dqm_source_node m \<le> max_node"
begin

definition msg_priority_keys :: "priority_key set" where
  "msg_priority_keys = make_priority_key max_time max_node ` msg_set"

lemma msg_priority_keys_nonempty: "msg_priority_keys \<noteq> {}"
  using msg_set_nonempty unfolding msg_priority_keys_def by simp

lemma msg_priority_keys_finite:
  "finite msg_set \<Longrightarrow> finite msg_priority_keys"
  unfolding msg_priority_keys_def by simp

text \<open>The well-formedness bounds are what make the priority key faithful to
  the message fields: under them, equal keys force equal priority-relevant
  fields.  This lifts @{thm [source] priority_key_injectivity} into the
  context, consuming the bounds.\<close>

lemma msg_priority_key_field_injective:
  assumes "m1 \<in> msg_set" and "m2 \<in> msg_set"
    and "make_priority_key max_time max_node m1 = make_priority_key max_time max_node m2"
  shows "dqm_authority_level m1 = dqm_authority_level m2
       \<and> msg_timestamp m1 = msg_timestamp m2
       \<and> msg_action m1 = msg_action m2
       \<and> dqm_source_node m1 = dqm_source_node m2"
  using priority_key_injectivity[OF assms(3)]
        msg_set_well_formed[OF assms(1)] msg_set_well_formed[OF assms(2)]
  by blast

end

text \<open>
  The \<^verbatim>\<open>dquencer_priority_concrete\<close> locale strengthens the context with
  the priority-key distinctness assumption on \<^verbatim>\<open>msg_set\<close>. This is the
  natural BFT-consensus precondition: distinct authority / timestamp /
  severity / source-node tuples ensure determinism. Under this assumption
  the priority key uniquely identifies a message in \<^verbatim>\<open>msg_set\<close>, so
  selecting the highest priority key in \<^verbatim>\<open>msg_priority_keys\<close> is equivalent
  to selecting the highest-priority message in \<^verbatim>\<open>msg_set\<close>.
\<close>

locale dquencer_priority_concrete = dquencer_priority_context +
  assumes msg_set_priority_distinct:
    "\<And>m1 m2. m1 \<in> msg_set \<Longrightarrow> m2 \<in> msg_set
              \<Longrightarrow> make_priority_key max_time max_node m1
                = make_priority_key max_time max_node m2
              \<Longrightarrow> m1 = m2"
begin

text \<open>
  Recovery: given a priority key from \<^verbatim>\<open>msg_priority_keys\<close>, return the
  unique \<^verbatim>\<open>msg_set\<close> message with that key.
\<close>

definition recover_msg :: "priority_key \<Rightarrow> dq_message" where
  "recover_msg k = (THE m. m \<in> msg_set \<and> make_priority_key max_time max_node m = k)"

lemma recover_msg_unique_existence:
  assumes "k \<in> msg_priority_keys"
  shows "\<exists>!m. m \<in> msg_set \<and> make_priority_key max_time max_node m = k"
proof -
  from assms obtain m
    where m_in: "m \<in> msg_set"
      and m_key: "make_priority_key max_time max_node m = k"
    unfolding msg_priority_keys_def by auto
  show ?thesis
  proof (rule ex1I[of _ m])
    show "m \<in> msg_set \<and> make_priority_key max_time max_node m = k"
      using m_in m_key by auto
  next
    fix m'
    assume "m' \<in> msg_set \<and> make_priority_key max_time max_node m' = k"
    then have m'_in: "m' \<in> msg_set"
      and m'_key: "make_priority_key max_time max_node m' = k"
      by auto
    from m_key m'_key
    have "make_priority_key max_time max_node m'
        = make_priority_key max_time max_node m"
      by simp
    then show "m' = m"
      using msg_set_priority_distinct[OF m'_in m_in] by simp
  qed
qed

lemma recover_msg_correct:
  assumes "k \<in> msg_priority_keys"
  shows "recover_msg k \<in> msg_set
       \<and> make_priority_key max_time max_node (recover_msg k) = k"
proof -
  from recover_msg_unique_existence[OF assms]
  have ex1: "\<exists>!m. m \<in> msg_set \<and> make_priority_key max_time max_node m = k" .
  show ?thesis
    using theI'[OF ex1] unfolding recover_msg_def .
qed

text \<open>
  Concrete consequence: deterministic selection of the highest-priority
  key from a non-empty finite \<^verbatim>\<open>msg_priority_keys\<close> set, and recovery of
  the unique well-formed D-quencer message that produced it.
\<close>

corollary dq_select_highest_deterministic:
  "\<exists>!k. dq_priority.select_highest msg_priority_keys = Some k"
  using dq_priority.select_highest_deterministic[OF msg_priority_keys_nonempty] .

corollary dq_select_highest_in_set:
  assumes "finite msg_set"
    and "dq_priority.select_highest msg_priority_keys = Some k"
  shows "k \<in> msg_priority_keys"
  using dq_priority.select_highest_in_set
        [OF msg_priority_keys_finite[OF assms(1)] assms(2)] .

corollary dq_select_highest_message:
  assumes "finite msg_set"
    and "dq_priority.select_highest msg_priority_keys = Some k"
  shows "recover_msg k \<in> msg_set
       \<and> make_priority_key max_time max_node (recover_msg k) = k"
  using recover_msg_correct[OF dq_select_highest_in_set[OF assms]] .

text \<open>The recovered message is maximal: no well-formed message in the set
  carries a strictly higher priority key.  This projects the key-level
  maximality of \<^verbatim>\<open>select_highest\<close> back onto messages, closing the loop of
  the ``highest-priority message'' reading.\<close>

corollary dq_select_highest_message_maximal:
  assumes "finite msg_set"
    and "dq_priority.select_highest msg_priority_keys = Some k"
  shows "\<forall>m \<in> msg_set. make_priority_key max_time max_node m
           \<le> make_priority_key max_time max_node (recover_msg k)"
proof -
  have max: "\<forall>k' \<in> msg_priority_keys. k' \<le> k"
    using dq_priority.select_highest_is_max
            [OF msg_priority_keys_finite[OF assms(1)] msg_priority_keys_nonempty assms(2)]
    by simp
  have rk: "make_priority_key max_time max_node (recover_msg k) = k"
    using recover_msg_correct[OF dq_select_highest_in_set[OF assms]] by simp
  show ?thesis
  proof
    fix m assume "m \<in> msg_set"
    then have "make_priority_key max_time max_node m \<in> msg_priority_keys"
      unfolding msg_priority_keys_def by simp
    with max rk show "make_priority_key max_time max_node m
        \<le> make_priority_key max_time max_node (recover_msg k)" by simp
  qed
qed

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


section \<open>Conditional Safety alongside the Liveness Results\<close>

text \<open>
  This section records how the safety result of Property 1 (cross-domain
  state preservation) sits alongside the liveness results of Property 2
  (deterministic selection and fair scheduling).

  The theorem below, \<^verbatim>\<open>conditional_safety_preservation\<close>, is a \<^emph>\<open>conditional
  safety\<close> statement: from a valid global state in which the target asset
  is unlocked and a transition is enabled, the synchronization function
  succeeds and preserves the global validity invariant. Its proof uses
  only the safety side (\<^verbatim>\<open>lock_acquire_success\<close> and
  \<^verbatim>\<open>valid_state_preservation\<close>); it does not invoke the liveness
  interpretations (\<^verbatim>\<open>dq_priority\<close>, \<^verbatim>\<open>dq_fair\<close>) and makes no
  Byzantine, determinism, deadlock, or starvation claim of its own. Those
  liveness properties are the separate theorems of this theory
  (\<^verbatim>\<open>dq_select_highest_deterministic\<close> and
  \<^verbatim>\<open>dq_starvation_bound\<close>), each stated in its own right.

  The genuine fusion of the two sides --- safety freed of its initial-validity
  hypothesis by a well-founded progress measure on cross-chain inconsistency,
  under the fair-leader assumption --- is
  \<^verbatim>\<open>oraclizer_guarded_bounded_convergence\<close> in \<^verbatim>\<open>Functor_Laws.thy\<close>, which
  drops the initial-validity hypothesis assumed here.
\<close>

text \<open>
  The statement below is a leaf corollary: it restates
  \<^verbatim>\<open>valid_state_preservation\<close> under the explicit precondition that the asset
  is unlocked --- the precondition the lock discipline is designed to
  establish. It is deliberately not the place where liveness and safety
  are fused (see \<^verbatim>\<open>Functor_Laws.thy\<close>).
\<close>

theorem conditional_safety_preservation:
  assumes valid: "valid_state gs"
    and exists: "asset_exists gs source aid"
    and current: "get_reg_state gs source aid = Some s"
    and trans: "reg_transition s action = Some s'"
    and not_locked: "\<not> is_locked gs aid"
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
    using valid_state_preservation[OF valid current trans synced] .
  with synced show ?thesis by auto
qed

text \<open>
  Summary of what Properties 1 + 2 together establish:

  \<^enum> \<^bold>\<open>Safety\<close> (Property 1): After synchronization, all connected
    chains agree on the regulatory state. The global validity
    invariant is preserved.

  \<^enum> \<^bold>\<open>Determinism\<close> (Property 2): Conflicting regulatory actions
    are resolved by a total order on priority keys. The consensus
    output --- abstracted here as deterministic priority selection ---
    is unique. The \<^verbatim>\<open>priority_system\<close> locale is
    instantiated on the \<^verbatim>\<open>priority_key\<close> type as carrier (with the
    corresponding messages recovered inside
    \<^verbatim>\<open>dquencer_priority_concrete\<close> via \<^verbatim>\<open>recover_msg\<close>), yielding
    deterministic selection from any finite non-empty set of valid
    candidate messages.  Priority here resolves conflicts \<^emph>\<open>among
    regulatory messages\<close>; precedence of regulatory actions over ordinary
    (non-regulatory) transactions is not modelled --- the message universe
    of this theory contains regulatory actions only.

  \<^enum> \<^bold>\<open>Deadlock\<close> (Property 2, scope note): deadlock is a concurrency
    phenomenon. The atomic sync model has no concurrent lock contention
    (lock holding is a boolean without contended holders), so deadlock does
    not arise within the model's scope; forced lock release under contention
    is out of scope, deferred to the preemptive-lock property. The theory
    states no proved deadlock-freedom theorem.

  \<^enum> \<^bold>\<open>Starvation freedom\<close> (Property 2): Under the fair leader
    assumption, every pending regulatory request is processed
    within a bounded number of epochs.  The pending-count assumptions
    encode a closed system --- no new requests arrive within the analysis
    horizon; liveness under continuous arrivals belongs to the partially
    synchronous lift left to subsequent entries.

  Open work for subsequent entries:
    - Compositional assurance across heterogeneous verification regimes
      (Canton + OSS + EVM).
    - Refinement: formal correspondence between these models and the
      Rust / Solidity implementation.
\<close>

end
