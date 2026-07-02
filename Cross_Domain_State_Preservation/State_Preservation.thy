(*
  Title:      Cross_Domain_State_Preservation/State_Preservation.thy
  Author:     Jinwook Kim (Jay) <jay@oraclizer.io>
  Maintainer: Jinwook Kim (Jay) <jay@oraclizer.io>
  License:    BSD

  Cross-Domain State Preservation Functor — Generic Theory

  This theory defines generic locales for cross-domain state preservation:
  reusable abstractions for verifying that state transitions are faithfully
  preserved when synchronized across heterogeneous domains (blockchains,
  off-chain ledgers, etc.).

  Cross-domain state synchronization is modelled as a structure-preserving
  map between state machines, where the naturality (homomorphism) condition
  of the synchronization map captures preservation of transitions.

  This theory is domain-independent. The regulatory state model in
  Regulatory_Instance.thy provides concrete instances for all four
  locales defined here (state_machine, state_preservation,
  symmetric_state_preservation, multi_domain_preservation), but the
  locales apply to any domain with finite states and actions,
  deterministic transitions, and optional terminal states.

  Methodological lineage:
    Our use of locales for compositional, reusable abstractions follows
    the methodological tradition exemplified in the AFP by Lochbihler's
    ADS_Functor entry. The technical content of this theory is independent
    of ADS_Functor; the connection is one of design philosophy (locale-based
    reusable abstractions over functor-shaped data), not formal dependency.
*)

theory State_Preservation
  imports Main
begin

section \<open>Generic State Machine Locale\<close>

text \<open>
  A state machine with finite state set, deterministic partial transition
  function, and optional terminal states. Terminal states accept no transitions.
\<close>

locale state_machine =
  fixes states :: "'s set"
    and actions :: "'a set"
    and transition :: "'s \<Rightarrow> 'a \<Rightarrow> 's option"
    and terminal :: "'s set"
  assumes finite_states: "finite states"
    and finite_actions: "finite actions"
    and terminal_subset: "terminal \<subseteq> states"
    and terminal_absorbing: "\<lbrakk> s \<in> terminal; a \<in> actions \<rbrakk> \<Longrightarrow> transition s a = None"
    and transition_closed: "\<lbrakk> s \<in> states; a \<in> actions; transition s a = Some s' \<rbrakk> \<Longrightarrow> s' \<in> states"
    and transition_domain: "\<lbrakk> s \<notin> states \<rbrakk> \<Longrightarrow> transition s a = None"
begin

text \<open>Determinism is inherent: transition is a function, not a relation.\<close>

lemma transition_deterministic:
  "transition s a = Some s1 \<Longrightarrow> transition s a = Some s2 \<Longrightarrow> s1 = s2"
  by simp

text \<open>Sequential composition of actions (partial, returns None on first failure).\<close>

fun apply_actions :: "'s \<Rightarrow> 'a list \<Rightarrow> 's option" where
  "apply_actions s [] = Some s"
| "apply_actions s (a # as) = (case transition s a of
     None \<Rightarrow> None
   | Some s' \<Rightarrow> apply_actions s' as)"

lemma apply_actions_closed:
  "\<lbrakk> s \<in> states; \<forall>a \<in> set as. a \<in> actions; apply_actions s as = Some s' \<rbrakk>
   \<Longrightarrow> s' \<in> states"
  by (induction as arbitrary: s) (auto split: option.splits dest: transition_closed)

text \<open>Note: @{thm apply_actions.simps(1)} already provides the simp rule
  \<^term>\<open>apply_actions s [] = Some s\<close>, so no separate [simp] lemma is needed.\<close>

lemma apply_actions_terminal:
  "\<lbrakk> s \<in> terminal; a \<in> actions \<rbrakk> \<Longrightarrow> apply_actions s (a # as) = None"
  by (simp add: terminal_absorbing)

text \<open>Concatenation of action words is the Kleisli composition of the two
  segment maps: together with @{thm apply_actions.simps(1)} (the identity
  word), this is the functor reading of a transition system on the free
  monoid of action words.\<close>

lemma apply_actions_append:
  "apply_actions s (as @ bs) =
     (case apply_actions s as of None \<Rightarrow> None | Some s' \<Rightarrow> apply_actions s' bs)"
  by (induction as arbitrary: s) (auto split: option.splits)

text \<open>Outside the state set no action sequence makes progress: the domain
  discipline \<^verbatim>\<open>transition_domain\<close> lifts from single transitions to words.\<close>

lemma apply_actions_outside_domain:
  "s \<notin> states \<Longrightarrow> apply_actions s (a # as) = None"
  by (simp add: transition_domain)

end


section \<open>Cross-Domain State Preservation Locale\<close>

text \<open>
  Two state machines connected by a synchronization map. The key property
  (naturality / homomorphism) states that synchronizing after a local
  transition yields the same result as transitioning after synchronization.

  More precisely: for state machines (\<^verbatim>\<open>S_src\<close>, \<^verbatim>\<open>T_src\<close>) and (\<^verbatim>\<open>S_tgt\<close>, \<^verbatim>\<open>T_tgt\<close>)
  connected by sync (mapping source states to target states), the following diagram commutes:

    \<^verbatim>\<open>s_src\<close>  --\<^verbatim>\<open>T_src\<close>(a)-->  \<^verbatim>\<open>s_src\<close>'
      |                      |
    sync                   sync
      |                      |
      v                      v
    \<^verbatim>\<open>s_tgt\<close>  --\<^verbatim>\<open>T_tgt\<close>(a)-->  \<^verbatim>\<open>s_tgt\<close>'

  That is: sync (\<^verbatim>\<open>T_src\<close> s a) = \<^verbatim>\<open>T_tgt\<close> (sync s) a

  This is the structural preservation guarantee: a transition performed
  at the source domain, when synchronized, produces the same result as
  performing the corresponding transition at the target domain.
\<close>

locale state_preservation =
  source: state_machine states\<^sub>s actions\<^sub>s transition\<^sub>s terminal\<^sub>s +
  target: state_machine states\<^sub>t actions\<^sub>t transition\<^sub>t terminal\<^sub>t
  for states\<^sub>s :: "'s set" and actions\<^sub>s :: "'a set"
    and transition\<^sub>s :: "'s \<Rightarrow> 'a \<Rightarrow> 's option"
    and terminal\<^sub>s :: "'s set"
    and states\<^sub>t :: "'t set" and actions\<^sub>t :: "'b set"
    and transition\<^sub>t :: "'t \<Rightarrow> 'b \<Rightarrow> 't option"
    and terminal\<^sub>t :: "'t set" +
  fixes state_map :: "'s \<Rightarrow> 't"
    and action_map :: "'a \<Rightarrow> 'b"
  assumes state_map_well_defined: "s \<in> states\<^sub>s \<Longrightarrow> state_map s \<in> states\<^sub>t"
    and action_map_well_defined: "a \<in> actions\<^sub>s \<Longrightarrow> action_map a \<in> actions\<^sub>t"
    and terminal_preservation: "s \<in> terminal\<^sub>s \<Longrightarrow> state_map s \<in> terminal\<^sub>t"
    \<comment> \<open>The naturality / homomorphism condition:\<close>
    and naturality:
      "\<lbrakk> s \<in> states\<^sub>s; a \<in> actions\<^sub>s; transition\<^sub>s s a = Some s' \<rbrakk>
       \<Longrightarrow> transition\<^sub>t (state_map s) (action_map a) = Some (state_map s')"
    and naturality_none:
      "\<lbrakk> s \<in> states\<^sub>s; a \<in> actions\<^sub>s; transition\<^sub>s s a = None \<rbrakk>
       \<Longrightarrow> transition\<^sub>t (state_map s) (action_map a) = None"
begin

text \<open>
  The fundamental theorem: state preservation extends to sequences of actions.
  If a sequence of transitions is valid at the source, the mapped sequence
  is valid at the target with the mapped final state.
\<close>

theorem sequential_preservation:
  assumes "s \<in> states\<^sub>s"
    and "\<forall>a \<in> set as. a \<in> actions\<^sub>s"
    and "source.apply_actions s as = Some s'"
  shows "target.apply_actions (state_map s) (map action_map as) = Some (state_map s')"
  using assms
proof (induction as arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then obtain s_mid where
    step: "transition\<^sub>s s a = Some s_mid" and
    rest: "source.apply_actions s_mid as = Some s'"
    by (auto split: option.splits)
  from Cons.prems(1) Cons.prems(2) step have "s_mid \<in> states\<^sub>s"
    using source.transition_closed by auto
  from Cons.prems(1) Cons.prems(2) step
  have mapped_step: "transition\<^sub>t (state_map s) (action_map a) = Some (state_map s_mid)"
    using naturality by auto
  from \<open>s_mid \<in> states\<^sub>s\<close> Cons.prems(2) rest
  have "target.apply_actions (state_map s_mid) (map action_map as) = Some (state_map s')"
    using Cons.IH by auto
  with mapped_step show ?case by simp
qed

theorem sequential_preservation_none:
  assumes "s \<in> states\<^sub>s"
    and "\<forall>a \<in> set as. a \<in> actions\<^sub>s"
    and "source.apply_actions s as = None"
  shows "target.apply_actions (state_map s) (map action_map as) = None"
  using assms
proof (induction as arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  show ?case
  proof (cases "transition\<^sub>s s a")
    case None
    then have "transition\<^sub>t (state_map s) (action_map a) = None"
      using naturality_none Cons.prems(1) Cons.prems(2) by auto
    then show ?thesis by simp
  next
    case (Some s_mid)
    then have mid_in: "s_mid \<in> states\<^sub>s"
      using source.transition_closed Cons.prems(1) Cons.prems(2) by auto
    from Some Cons.prems(3) have "source.apply_actions s_mid as = None"
      by simp
    then have ih: "target.apply_actions (state_map s_mid) (map action_map as) = None"
      using Cons.IH mid_in Cons.prems(2) by auto
    from Some have "transition\<^sub>t (state_map s) (action_map a) = Some (state_map s_mid)"
      using naturality Cons.prems(1) Cons.prems(2) by auto
    with ih show ?thesis by simp
  qed
qed

text \<open>Terminal states are preserved: if a source state is terminal, its image is terminal.\<close>

corollary terminal_image_absorbing:
  assumes "s \<in> terminal\<^sub>s" and "a \<in> actions\<^sub>s"
  shows "transition\<^sub>t (state_map s) (action_map a) = None"
proof -
  from assms(1) have "s \<in> states\<^sub>s" using source.terminal_subset by auto
  from assms have "transition\<^sub>s s a = None"
    using source.terminal_absorbing by auto
  then show ?thesis
    using naturality_none \<open>s \<in> states\<^sub>s\<close> assms(2) by auto
qed

end


section \<open>Symmetric State Preservation\<close>

text \<open>
  For bidirectional synchronization, both directions
  must preserve structure. This locale composes two \<^verbatim>\<open>state_preservation\<close>
  instances with inverse maps, establishing that synchronization in either
  direction is structure-preserving.
\<close>

locale symmetric_state_preservation =
  forward: state_preservation
    states\<^sub>s actions\<^sub>s transition\<^sub>s terminal\<^sub>s
    states\<^sub>t actions\<^sub>t transition\<^sub>t terminal\<^sub>t
    state_map action_map +
  backward: state_preservation
    states\<^sub>t actions\<^sub>t transition\<^sub>t terminal\<^sub>t
    states\<^sub>s actions\<^sub>s transition\<^sub>s terminal\<^sub>s
    state_map_inv action_map_inv
  for states\<^sub>s :: "'s set" and actions\<^sub>s :: "'a set"
    and transition\<^sub>s :: "'s \<Rightarrow> 'a \<Rightarrow> 's option"
    and terminal\<^sub>s :: "'s set"
    and states\<^sub>t :: "'t set" and actions\<^sub>t :: "'b set"
    and transition\<^sub>t :: "'t \<Rightarrow> 'b \<Rightarrow> 't option"
    and terminal\<^sub>t :: "'t set"
    and state_map :: "'s \<Rightarrow> 't" and action_map :: "'a \<Rightarrow> 'b"
    and state_map_inv :: "'t \<Rightarrow> 's" and action_map_inv :: "'b \<Rightarrow> 'a" +
  assumes roundtrip_state_src: "s \<in> states\<^sub>s \<Longrightarrow> state_map_inv (state_map s) = s"
    and roundtrip_state_tgt: "t \<in> states\<^sub>t \<Longrightarrow> state_map (state_map_inv t) = t"
    and roundtrip_action_src: "a \<in> actions\<^sub>s \<Longrightarrow> action_map_inv (action_map a) = a"
    and roundtrip_action_tgt: "b \<in> actions\<^sub>t \<Longrightarrow> action_map (action_map_inv b) = b"
begin

text \<open>
  Under symmetric preservation with roundtrip maps, \<^verbatim>\<open>state_map\<close> is injective
  on the state set — distinct source states map to distinct target states.
  This guarantees no information loss during synchronization.
\<close>

lemma state_map_injective:
  "\<lbrakk> s1 \<in> states\<^sub>s; s2 \<in> states\<^sub>s; state_map s1 = state_map s2 \<rbrakk> \<Longrightarrow> s1 = s2"
  using roundtrip_state_src by metis

text \<open>The roundtrip pair upgrades injectivity to a bijection between the two
  state sets and between the two action sets --- the formal content of ``no
  information loss'' for bidirectional synchronization.\<close>

lemma state_map_bij: "bij_betw state_map states\<^sub>s states\<^sub>t"
proof (rule bij_betw_byWitness[where f' = state_map_inv])
  show "\<forall>s \<in> states\<^sub>s. state_map_inv (state_map s) = s"
    using roundtrip_state_src by blast
  show "\<forall>t \<in> states\<^sub>t. state_map (state_map_inv t) = t"
    using roundtrip_state_tgt by blast
  show "state_map ` states\<^sub>s \<subseteq> states\<^sub>t"
    using forward.state_map_well_defined by auto
  show "state_map_inv ` states\<^sub>t \<subseteq> states\<^sub>s"
    using backward.state_map_well_defined by auto
qed

lemma action_map_bij: "bij_betw action_map actions\<^sub>s actions\<^sub>t"
proof (rule bij_betw_byWitness[where f' = action_map_inv])
  show "\<forall>a \<in> actions\<^sub>s. action_map_inv (action_map a) = a"
    using roundtrip_action_src by blast
  show "\<forall>b \<in> actions\<^sub>t. action_map (action_map_inv b) = b"
    using roundtrip_action_tgt by blast
  show "action_map ` actions\<^sub>s \<subseteq> actions\<^sub>t"
    using forward.action_map_well_defined by auto
  show "action_map_inv ` actions\<^sub>t \<subseteq> actions\<^sub>s"
    using backward.action_map_well_defined by auto
qed

end


section \<open>Multi-Domain State Preservation\<close>

text \<open>
  Generalization to N domains sharing the same abstract state machine.
  This models scenarios where a single asset exists on multiple
  domains (e.g., blockchain networks), all of which must reflect
  the same state.

  The key property: if one domain transitions, the synchronization
  brings ALL other domains to the same resulting state.

  We model this as: all domains are instances of the same abstract
  state machine, connected by identity-like state/action maps.
  The "same abstract state machine" assumption holds when the
  protocol enforces a uniform state model across all domains.
\<close>

locale multi_domain_preservation =
  fixes domains :: "'d set"
    and states :: "'s set"
    and actions :: "'a set"
    and transition :: "'s \<Rightarrow> 'a \<Rightarrow> 's option"
    and terminal :: "'s set"
    and domain_state :: "'d \<Rightarrow> 'id \<Rightarrow> 's option"
      \<comment> \<open>Current state of asset 'id in domain 'd\<close>
  assumes fin_domains: "finite domains"
    and sm: "state_machine states actions transition terminal"
    and consistent_init:
      \<comment> \<open>Precondition: all domains holding an asset agree on its state\<close>
      "\<lbrakk> d1 \<in> domains; d2 \<in> domains;
         domain_state d1 aid = Some s1; domain_state d2 aid = Some s2 \<rbrakk>
       \<Longrightarrow> s1 = s2"
begin

text \<open>Which domains hold a given asset.\<close>

definition connected_domains :: "'id \<Rightarrow> 'd set" where
  "connected_domains aid = {d \<in> domains. domain_state d aid \<noteq> None}"

text \<open>The global consensus state of an asset (well-defined by \<^verbatim>\<open>consistent_init\<close>).\<close>

definition consensus_state :: "'id \<Rightarrow> 's option" where
  "consensus_state aid =
    (if connected_domains aid = {} then None
     else domain_state (SOME d. d \<in> connected_domains aid) aid)"

text \<open>The finiteness of the domain roster bounds every connected set.\<close>

lemma connected_domains_finite: "finite (connected_domains aid)"
proof -
  have "connected_domains aid \<subseteq> domains"
    unfolding connected_domains_def by auto
  then show ?thesis using fin_domains by (rule finite_subset)
qed

text \<open>The consensus state is well-defined: by \<^verbatim>\<open>consistent_init\<close> the choice
  of witnessing domain is immaterial, so the \<^verbatim>\<open>SOME\<close> in the definition is
  sound --- every connected domain reports the consensus value.\<close>

lemma consensus_state_well_defined:
  assumes "d \<in> connected_domains aid"
  shows "consensus_state aid = domain_state d aid"
proof -
  have some_in: "(SOME d'. d' \<in> connected_domains aid) \<in> connected_domains aid"
    using assms by (rule someI)
  from assms have ne: "connected_domains aid \<noteq> {}" by auto
  obtain s where s: "domain_state d aid = Some s"
    using assms unfolding connected_domains_def by auto
  obtain s' where s': "domain_state (SOME d'. d' \<in> connected_domains aid) aid = Some s'"
    using some_in unfolding connected_domains_def by auto
  have "d \<in> domains" "(SOME d'. d' \<in> connected_domains aid) \<in> domains"
    using assms some_in unfolding connected_domains_def by auto
  then have "s' = s" using consistent_init s s' by blast
  then show ?thesis
    unfolding consensus_state_def using ne s s' by simp
qed


text \<open>
  After synchronizing an action on an asset, all connected domains
  reflect the new state. This is the cross-domain consistency theorem.
\<close>

definition sync_all ::
  "'d \<Rightarrow> 'a \<Rightarrow> 'id \<Rightarrow> ('d \<Rightarrow> 'id \<Rightarrow> 's option) \<Rightarrow> ('d \<Rightarrow> 'id \<Rightarrow> 's option) option"
where
  "sync_all source action aid ds =
    (case ds source aid of
       None \<Rightarrow> None
     | Some s \<Rightarrow>
         (case transition s action of
            None \<Rightarrow> None
          | Some s' \<Rightarrow>
              Some (\<lambda>d aid'.
                if aid' = aid \<and> d \<in> connected_domains aid
                then Some s'
                else ds d aid')))"

text \<open>Terminal states admit no synchronization: the state-machine assumption
  \<^verbatim>\<open>sm\<close> transports terminal absorption to \<^verbatim>\<open>sync_all\<close>.\<close>

lemma sync_all_terminal_none:
  assumes "domain_state source aid = Some s"
    and "s \<in> terminal" and "action \<in> actions"
  shows "sync_all source action aid domain_state = None"
proof -
  have "transition s action = None"
    using state_machine.terminal_absorbing[OF sm assms(2) assms(3)] .
  then show ?thesis
    unfolding sync_all_def using assms(1) by simp
qed

text \<open>
  The cross-domain consistency theorem: after \<^verbatim>\<open>sync_all\<close>, every connected
  domain agrees on the new state.
\<close>

theorem cross_domain_consistency:
  assumes "source \<in> domains"
    and "domain_state source aid = Some s"
    and "s \<in> states"
    and "action \<in> actions"
    and "transition s action = Some s'"
    and "sync_all source action aid domain_state = Some ds'"
    and "d \<in> connected_domains aid"
  shows "ds' d aid = Some s'"
proof -
  from assms(2,5,6) have
    "ds' = (\<lambda>d aid'.
      if aid' = aid \<and> d \<in> connected_domains aid
      then Some s'
      else domain_state d aid')"
    unfolding sync_all_def by auto
  with assms(7) show ?thesis by simp
qed

text \<open>
  \<^verbatim>\<open>sync_all\<close> does not affect other assets.
\<close>

theorem sync_isolation:
  assumes "sync_all source action aid domain_state = Some ds'"
    and "aid' \<noteq> aid"
  shows "ds' d aid' = domain_state d aid'"
proof -
  from assms(1) obtain s s' where
    "domain_state source aid = Some s"
    "transition s action = Some s'"
    unfolding sync_all_def by (auto split: option.splits)
  then have "ds' = (\<lambda>d aid'.
    if aid' = aid \<and> d \<in> connected_domains aid
    then Some s'
    else domain_state d aid')"
    using assms(1) unfolding sync_all_def by auto
  with assms(2) show ?thesis by auto
qed

end

end
