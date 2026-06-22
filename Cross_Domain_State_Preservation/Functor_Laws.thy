(*
  Title:      Cross_Domain_State_Preservation/Functor_Laws.thy
  Author:     Jinwook Kim (Jay) <jay@oraclizer.io>
  Maintainer: Jinwook Kim (Jay) <jay@oraclizer.io>
  License:    BSD

  Cross-Domain State Preservation Functor — Functor Laws and Merkle Composition

  This theory establishes that cross-domain state preservation is functorial.
  Viewing state machines as objects and state-preservation maps as morphisms,
  we prove the three category axioms on these morphisms:

    * identity is a preservation morphism            (preservation_id)
    * preservation morphisms compose                 (preservation_compose)
    * morphism composition is associative            (preservation_assoc)

  Together these force the term "Functor" to be a theorem rather than a
  slogan: the cross-domain construction is a functor on the category whose
  objects are state machines and whose morphisms are the structure-preserving
  synchronization maps of State_Preservation.thy.

  The second part composes this functorial structure with Lochbihler and
  Maric's authenticated-data-structure interface (ADS_Functor.Merkle_Interface).
  Two glue predicates, state_join and state_refines, lift the ADS merge (join)
  and blinding (partial order) operations to the global-state level.  The
  soundness results invoke the merkle_interface lemmas merge_respects_hashes,
  join and hash explicitly, so that the dependency on the ADS interface is
  load-bearing and not merely an import of a signature.

  Reuse beyond the regulatory instance.  The glue layer is an abstract
  structure: an authenticated data structure carrying a cross-domain state
  view.  It applies to distributed databases with Merkle-authenticated
  replication, to sharded blockchains with authenticated cross-shard
  messages, and to the public/witness layering of zero-knowledge proof
  systems, where state_refines expresses that a public view is a blinding
  refinement of a full witness.
*)

theory Functor_Laws
  imports
    Composition
    Regulatory_Instance
    DQuencer_Instance
    Proof_Automation
    "ADS_Functor.Merkle_Interface"
begin

section \<open>Functor Laws on State-Preservation Morphisms\<close>

text \<open>
  We regard the locale @{locale state_preservation} as a morphism between two
  objects of a category.  An object is a state machine
  \<^term>\<open>(states, actions, transition, terminal)\<close>; a morphism from one object to
  another is a pair \<^term>\<open>(state_map, action_map)\<close> satisfying the well-definedness,
  terminal-preservation and naturality conditions of @{locale state_preservation}.
  The following three theorems are the category axioms for this notion of
  morphism.
\<close>

subsection \<open>Identity morphism\<close>

text \<open>The identity pair \<^term>\<open>(id, id)\<close> is a state-preservation morphism from any
  object to itself: \<open>F\<close> sends identities to identities.\<close>

theorem preservation_id:
  assumes "state_machine states actions transition terminal"
  shows "state_preservation states actions transition terminal
                            states actions transition terminal id id"
  using assms
  unfolding state_preservation_def state_preservation_axioms_def
  by simp

subsection \<open>Composition of morphisms\<close>

text \<open>The composite of two state-preservation morphisms is a state-preservation
  morphism: the naturality square of the second morphism is stacked on that of
  the first.  This is the cross-domain analogue of "closed under composition".\<close>

theorem preservation_compose:
  assumes f: "state_preservation S\<^sub>a A\<^sub>a T\<^sub>a F\<^sub>a S\<^sub>b A\<^sub>b T\<^sub>b F\<^sub>b f f'"
      and g: "state_preservation S\<^sub>b A\<^sub>b T\<^sub>b F\<^sub>b S\<^sub>c A\<^sub>c T\<^sub>c F\<^sub>c g g'"
  shows "state_preservation S\<^sub>a A\<^sub>a T\<^sub>a F\<^sub>a S\<^sub>c A\<^sub>c T\<^sub>c F\<^sub>c (g \<circ> f) (g' \<circ> f')"
proof -
  interpret f: state_preservation S\<^sub>a A\<^sub>a T\<^sub>a F\<^sub>a S\<^sub>b A\<^sub>b T\<^sub>b F\<^sub>b f f' by (rule f)
  interpret g: state_preservation S\<^sub>b A\<^sub>b T\<^sub>b F\<^sub>b S\<^sub>c A\<^sub>c T\<^sub>c F\<^sub>c g g' by (rule g)
  show ?thesis
  proof (unfold_locales)
    fix s assume "s \<in> S\<^sub>a"
    then show "(g \<circ> f) s \<in> S\<^sub>c"
      by (simp add: f.state_map_well_defined g.state_map_well_defined)
  next
    fix a assume "a \<in> A\<^sub>a"
    then show "(g' \<circ> f') a \<in> A\<^sub>c"
      by (simp add: f.action_map_well_defined g.action_map_well_defined)
  next
    fix s assume "s \<in> F\<^sub>a"
    then show "(g \<circ> f) s \<in> F\<^sub>c"
      by (simp add: f.terminal_preservation g.terminal_preservation)
  next
    fix s a s'
    assume A: "s \<in> S\<^sub>a" and B: "a \<in> A\<^sub>a" and C: "T\<^sub>a s a = Some s'"
    have fs: "f s \<in> S\<^sub>b" using A f.state_map_well_defined by simp
    have fa: "f' a \<in> A\<^sub>b" using B f.action_map_well_defined by simp
    have "T\<^sub>b (f s) (f' a) = Some (f s')" using f.naturality A B C by simp
    then have "T\<^sub>c (g (f s)) (g' (f' a)) = Some (g (f s'))"
      using g.naturality fs fa by simp
    then show "T\<^sub>c ((g \<circ> f) s) ((g' \<circ> f') a) = Some ((g \<circ> f) s')"
      by (simp add: comp_def)
  next
    fix s a
    assume A: "s \<in> S\<^sub>a" and B: "a \<in> A\<^sub>a" and C: "T\<^sub>a s a = None"
    have fs: "f s \<in> S\<^sub>b" using A f.state_map_well_defined by simp
    have fa: "f' a \<in> A\<^sub>b" using B f.action_map_well_defined by simp
    have "T\<^sub>b (f s) (f' a) = None" using f.naturality_none A B C by simp
    then have "T\<^sub>c (g (f s)) (g' (f' a)) = None"
      using g.naturality_none fs fa by simp
    then show "T\<^sub>c ((g \<circ> f) s) ((g' \<circ> f') a) = None"
      by (simp add: comp_def)
  qed
qed

subsection \<open>Associativity of morphism composition\<close>

text \<open>Composition of state-preservation morphisms is associative on both the
  state and the action components.  Since the components are functions, this is
  exactly associativity of function composition; the three morphism hypotheses
  fix the objects across which the equation is read, completing the category
  axioms (identity, composition, associativity).\<close>

theorem preservation_assoc:
  assumes "state_preservation S\<^sub>a A\<^sub>a T\<^sub>a F\<^sub>a S\<^sub>b A\<^sub>b T\<^sub>b F\<^sub>b f f'"
      and "state_preservation S\<^sub>b A\<^sub>b T\<^sub>b F\<^sub>b S\<^sub>c A\<^sub>c T\<^sub>c F\<^sub>c g g'"
      and "state_preservation S\<^sub>c A\<^sub>c T\<^sub>c F\<^sub>c S\<^sub>d A\<^sub>d T\<^sub>d F\<^sub>d k k'"
  shows "((k \<circ> g) \<circ> f = k \<circ> (g \<circ> f)) \<and> ((k' \<circ> g') \<circ> f' = k' \<circ> (g' \<circ> f'))"
  by (simp add: comp_assoc)


section \<open>Composition Exercised: A Heterogeneous Three-Domain Chain\<close>

text \<open>
  @{thm [source] preservation_compose} is exercised on a concrete chain of
  three distinct domains: the off-chain DAML permission ledger (structured
  records), the on-chain regulatory enum, and Chain~B with its dedicated
  four-action vocabulary.  In HOL the morphisms of a heterogeneous chain
  cannot be packed into one object --- the domains carry genuinely different
  state and action types --- so the correct formal expression of an
  \<open>N\<close>-domain chain is exactly the composite of pairwise morphisms, with
  @{thm [source] preservation_assoc} making longer path composites
  unambiguous.  Both legs are scoped to the escalation subset of the action
  vocabulary: the DAML machine restricts a fortiori (a machine restricted to
  a subset of its action set is again a machine), and the layer-crossing
  naturality of \<^const>\<open>daml_to_reg\<close> holds on the subset because it holds on
  the full vocabulary.
\<close>

lemma daml_escalation_state_machine:
  "state_machine daml_states escalation_actions daml_transition daml_terminal"
proof unfold_locales
  show "finite daml_states" by (rule daml_states_finite)
next
  show "finite escalation_actions" unfolding escalation_actions_def by simp
next
  show "daml_terminal \<subseteq> daml_states" by (rule daml_terminal_subset)
next
  fix p a
  assume "p \<in> daml_terminal" and "a \<in> escalation_actions"
  then show "daml_transition p a = None"
    using daml_terminal_absorbing reg_actions_UNIV by auto
next
  fix p a p'
  assume "p \<in> daml_states" and "a \<in> escalation_actions"
     and "daml_transition p a = Some p'"
  then show "p' \<in> daml_states"
    using daml_transition_closed reg_actions_UNIV by auto
next
  fix p :: daml_perm and a :: reg_action
  assume "p \<notin> daml_states"
  then show "daml_transition p a = None" by (rule daml_transition_outside_states)
qed

text \<open>The escalation-scoped backward bridge: \<^const>\<open>daml_to_reg\<close> as a morphism
  from the DAML machine to the regulatory machine, both restricted to the
  escalation actions.\<close>

lemma daml_to_reg_escalation_bridge:
  "state_preservation daml_states escalation_actions daml_transition daml_terminal
                      reg_states escalation_actions reg_transition reg_terminal
                      daml_to_reg id"
proof unfold_locales
  \<comment> \<open>Source state-machine obligations (the DAML machine on the escalation
      subset is not registered, so its six obligations remain pending); the
      target machine coincides with the source machine of the registered
      \<open>escalation_preservation\<close> interpretation and is discharged
      automatically.\<close>
  show "finite daml_states" by (rule daml_states_finite)
next
  show "finite escalation_actions" unfolding escalation_actions_def by simp
next
  show "daml_terminal \<subseteq> daml_states" by (rule daml_terminal_subset)
next
  fix p a
  assume "p \<in> daml_terminal" and "a \<in> escalation_actions"
  then show "daml_transition p a = None"
    using daml_terminal_absorbing reg_actions_UNIV by auto
next
  fix p a p'
  assume "p \<in> daml_states" and "a \<in> escalation_actions"
     and "daml_transition p a = Some p'"
  then show "p' \<in> daml_states"
    using daml_transition_closed reg_actions_UNIV by auto
next
  fix p :: daml_perm and a :: reg_action
  assume "p \<notin> daml_states"
  then show "daml_transition p a = None" by (rule daml_transition_outside_states)
next
  fix p
  assume "p \<in> daml_states"
  then show "daml_to_reg p \<in> reg_states" using reg_states_UNIV by auto
next
  fix a
  assume "a \<in> escalation_actions"
  then show "id a \<in> escalation_actions" by simp
next
  fix p
  assume "p \<in> daml_terminal"
  then have "p = reg_to_daml CONFISCATED" unfolding daml_terminal_def by simp
  then have "daml_to_reg p = CONFISCATED" using daml_to_reg_to_daml_id by simp
  then show "daml_to_reg p \<in> reg_terminal" unfolding reg_terminal_def by simp
next
  fix p a p'
  assume "p \<in> daml_states" and "a \<in> escalation_actions"
     and "daml_transition p a = Some p'"
  then show "reg_transition (daml_to_reg p) (id a) = Some (daml_to_reg p')"
    using daml_to_reg_naturality_some reg_actions_UNIV by auto
next
  fix p a
  assume "p \<in> daml_states" and "a \<in> escalation_actions"
     and "daml_transition p a = None"
  then show "reg_transition (daml_to_reg p) (id a) = None"
    using daml_to_reg_naturality_none reg_actions_UNIV by auto
qed

text \<open>The escalation morphism of \<^theory>\<open>Cross_Domain_State_Preservation.Regulatory_Instance\<close>
  in predicate (bundle) form, so that it can be fed to
  @{thm [source] preservation_compose}.\<close>

lemma escalation_preservation_bundle:
  "state_preservation reg_states escalation_actions reg_transition reg_terminal
                      reg_states chain_b_actions chain_b_transition reg_terminal
                      id escalation_action_map"
  \<comment> \<open>This very instance is registered as the \<open>escalation_preservation\<close>
      interpretation of \<^theory>\<open>Cross_Domain_State_Preservation.Regulatory_Instance\<close>,
      so every obligation is discharged from the registration.\<close>
  by unfold_locales

text \<open>
  The composed three-domain morphism: DAML permission records, synchronized
  through the regulatory enum, arrive on Chain~B's vocabulary.  The composite
  is literally @{thm [source] preservation_compose} applied to the two legs;
  no new naturality argument is needed, which is the point of the functor
  laws.  Arbitrary finite heterogeneous chains are expressed the same way, as
  composites of pairwise morphisms.
\<close>

theorem daml_to_chain_b_composed:
  "state_preservation daml_states escalation_actions daml_transition daml_terminal
                      reg_states chain_b_actions chain_b_transition reg_terminal
                      (id \<circ> daml_to_reg) (escalation_action_map \<circ> id)"
  using preservation_compose[OF daml_to_reg_escalation_bridge
                                escalation_preservation_bundle] .

text \<open>
  The domain guard of the layer-crossing bridge is load-bearing, not a
  notational convenience.  The record below carries the \<open>D_Seized\<close> tag with
  no seizing party: it violates \<^const>\<open>valid_daml_perm\<close> and lies outside
  \<^const>\<open>daml_states\<close>.  The guarded DAML transition rejects \<^const>\<open>RELEASE\<close>
  on it, while the bare enum projection of the same record would accept it
  --- so dropping the guard would break naturality on exactly such records.
  Preservation holds on the carved-out domain and only there; the guard is
  the boundary of the preservation guarantee, recorded here permanently as a
  machine-checked witness.
\<close>

definition invalid_daml_perm :: daml_perm where
  "invalid_daml_perm =
     \<lparr> status_tag = D_Seized, seized_by = None, restriction_scope = None \<rparr>"

lemma guard_is_load_bearing:
  "\<not> valid_daml_perm invalid_daml_perm"
  "invalid_daml_perm \<notin> daml_states"
  "daml_transition invalid_daml_perm RELEASE = None"
  "reg_transition (daml_to_reg invalid_daml_perm) RELEASE = Some ACTIVE"
proof -
  show "\<not> valid_daml_perm invalid_daml_perm"
    by (simp add: valid_daml_perm_def invalid_daml_perm_def)
  have "\<And>s. invalid_daml_perm \<noteq> reg_to_daml s"
  proof -
    fix s show "invalid_daml_perm \<noteq> reg_to_daml s"
      by (cases s) (auto simp: invalid_daml_perm_def)
  qed
  then show notin: "invalid_daml_perm \<notin> daml_states"
    by (auto simp: daml_states_def)
  from notin show "daml_transition invalid_daml_perm RELEASE = None"
    by (rule daml_transition_outside_states)
  show "reg_transition (daml_to_reg invalid_daml_perm) RELEASE = Some ACTIVE"
    by (simp add: invalid_daml_perm_def)
qed


section \<open>Proof Automation Exercised on the Regulatory Instances\<close>

text \<open>
  The discharge methods of \<^theory>\<open>Cross_Domain_State_Preservation.Proof_Automation\<close>
  are fed here with the equational content of the regulatory, Chain~B and
  DAML domains, and then exercised: each \<open>_via_method\<close> lemma below restates a
  preservation or machine instance --- proved manually above or registered in
  \<^theory>\<open>Cross_Domain_State_Preservation.Regulatory_Instance\<close> --- and
  discharges it with a single method invocation, giving a one-to-one
  comparison between the manual proofs and the automated ones.  The instance
  obligations are not weakened in any way: the statements are identical to
  their manual counterparts.
\<close>

text \<open>Finiteness of the enumerated regulatory types, in the normal form the
  simplifier reaches after rewriting the set definitions to \<^const>\<open>UNIV\<close>.\<close>

lemma finite_reg_state_UNIV [discharge_simps]: "finite (UNIV :: reg_state set)"
  using reg_sm.finite_states by (simp add: reg_states_UNIV)

lemma finite_reg_action_UNIV [discharge_simps]: "finite (UNIV :: reg_action set)"
  using reg_sm.finite_actions by (simp add: reg_actions_UNIV)

text \<open>Terminal and well-definedness helpers for the layer-crossing maps, in
  conditional-rewrite form.\<close>

lemma daml_to_reg_terminal_val [discharge_simps]:
  "p \<in> daml_terminal \<Longrightarrow> daml_to_reg p = CONFISCATED"
  by (auto simp: daml_terminal_def daml_to_reg_to_daml_id)

lemma reg_to_daml_terminal [discharge_simps]:
  "s \<in> reg_terminal \<Longrightarrow> reg_to_daml s \<in> daml_terminal"
  by (auto simp: reg_terminal_def daml_terminal_def)

lemma reg_to_daml_in_states [discharge_simps]:
  "reg_to_daml s \<in> daml_states"
  by (simp add: daml_states_def)

text \<open>The collections.  Equational and conditional-rewrite content goes to
  \<open>discharge_simps\<close>; closure rules, whose condition variables do not all
  occur in their conclusions, go to \<open>discharge_intros\<close>.\<close>

lemmas [discharge_simps] =
  reg_states_UNIV reg_actions_UNIV
  escalation_actions_def chain_b_actions_def reg_terminal_def
  confiscated_terminal chain_b_terminal
  daml_states_finite daml_terminal_subset
  daml_terminal_absorbing daml_transition_outside_states
  reg_to_daml_naturality_some reg_to_daml_naturality_none
  daml_to_reg_naturality_some daml_to_reg_naturality_none
  escalation_naturality_some escalation_naturality_none

lemmas [discharge_intros] =
  reg_transition_closed chain_b_transition_closed daml_transition_closed

text \<open>The layer-crossing maps are introduced with \<open>fun\<close>, so their defining
  equations are default simplification rules; the methods must keep the maps
  opaque so that the conditional naturality and terminal rewrites above can
  match their redexes.\<close>

lemmas [discharge_dels] =
  daml_to_reg.simps reg_to_daml.simps

text \<open>
  The comparison lemmas.  The first three restate instances proved manually
  in this theory; the method rediscovers each proof from the collections
  alone (none of these instances is registered, so \<open>unfold_locales\<close> receives
  every obligation atomically).
\<close>

lemma daml_escalation_state_machine_via_method:
  "state_machine daml_states escalation_actions daml_transition daml_terminal"
  by discharge_state_machine

lemma daml_to_reg_escalation_bridge_via_method:
  "state_preservation daml_states escalation_actions daml_transition daml_terminal
                      reg_states escalation_actions reg_transition reg_terminal
                      daml_to_reg id"
  by discharge_preservation

lemma daml_to_chain_b_composed_via_method:
  "state_preservation daml_states escalation_actions daml_transition daml_terminal
                      reg_states chain_b_actions chain_b_transition reg_terminal
                      (id \<circ> daml_to_reg) (escalation_action_map \<circ> id)"
  by discharge_preservation

text \<open>The forward escalation-scoped bridge is a new instance with no manual
  counterpart: the method constructs it outright, which is the reuse claim in
  its sharpest form.\<close>

lemma reg_to_daml_escalation_bridge_via_method:
  "state_preservation reg_states escalation_actions reg_transition reg_terminal
                      daml_states escalation_actions daml_transition daml_terminal
                      reg_to_daml id"
  by discharge_preservation

text \<open>
  The remaining three restate instances registered as interpretations in
  \<^theory>\<open>Cross_Domain_State_Preservation.Regulatory_Instance\<close>; for these,
  \<open>unfold_locales\<close> discharges the obligations from the registrations, so the
  one-line proofs are registration-backed rather than search-backed.  The
  search-backed counterparts above show that the method does not depend on
  the registrations.
\<close>

lemma escalation_preservation_via_method:
  "state_preservation reg_states escalation_actions reg_transition reg_terminal
                      reg_states chain_b_actions chain_b_transition reg_terminal
                      id escalation_action_map"
  by discharge_preservation

lemma forward_layer_preservation_via_method:
  "state_preservation reg_states reg_actions reg_transition reg_terminal
                      daml_states reg_actions daml_transition daml_terminal
                      reg_to_daml id"
  by discharge_preservation

lemma backward_layer_preservation_via_method:
  "state_preservation daml_states reg_actions daml_transition daml_terminal
                      reg_states reg_actions reg_transition reg_terminal
                      daml_to_reg id"
  by discharge_preservation


section \<open>State Glue: Join and Refinement\<close>

text \<open>
  The two glue predicates lift the authenticated-data-structure operations to
  the global-state level.  \<^term>\<open>state_join sa sb sab\<close> says that \<open>sab\<close> is the
  consistent combination of the partial views \<open>sa\<close> and \<open>sb\<close>: on every chain
  connected in either view, \<open>sab\<close> carries the value of whichever view knows the
  chain (preferring \<open>sa\<close>), the two views agree wherever both are defined, and
  \<open>sab\<close> reveals no chain beyond the union of the two views (the containment
  clause).  This is the state-level reading of the ADS \<^term>\<open>join\<close>: on revealed
  holdings \<open>sab\<close> is the least consistent combination of \<open>sa\<close> and \<open>sb\<close> --- the
  lock components are unconstrained --- and the agreement clause is the
  state-level reading of equal hashes (mergeability).  Without the containment
  clause a candidate join could carry an arbitrary holding on a chain outside
  both views and still be accepted; the regression witness
  \<open>rogue_join_excluded\<close> below records that such a candidate is now rejected.

  \<^term>\<open>state_refines sa sb\<close> says that \<open>sa\<close> is a partial view of \<open>sb\<close>: every
  chain known to \<open>sa\<close> is known to \<open>sb\<close> with the same regulatory state.  This is
  the state-level reading of the ADS blinding order \<^term>\<open>bo\<close>: a more-blinded
  value agrees with a less-blinded one on everything it can observe.
\<close>

definition state_join :: "global_state \<Rightarrow> global_state \<Rightarrow> global_state \<Rightarrow> bool" where
  "state_join sa sb sab \<equiv>
     (\<forall>aid c.
        (c \<in> connected_chains sa aid \<or> c \<in> connected_chains sb aid)
        \<longrightarrow> get_reg_state sab c aid =
              (if c \<in> connected_chains sa aid then get_reg_state sa c aid
               else get_reg_state sb c aid))
   \<and> (\<forall>aid c1 c2.
        c1 \<in> connected_chains sa aid \<and> c2 \<in> connected_chains sb aid
        \<longrightarrow> get_reg_state sa c1 aid = get_reg_state sb c2 aid)
   \<and> (\<forall>aid c.
        c \<in> connected_chains sab aid
        \<longrightarrow> c \<in> connected_chains sa aid \<or> c \<in> connected_chains sb aid)"

definition state_refines :: "global_state \<Rightarrow> global_state \<Rightarrow> bool" where
  "state_refines sa sb \<equiv>
     \<forall>aid c. c \<in> connected_chains sa aid
       \<longrightarrow> c \<in> connected_chains sb aid \<and> get_reg_state sa c aid = get_reg_state sb c aid"

text \<open>Refinement is reflexive and transitive: a partial-view preorder on states.\<close>

lemma state_refines_refl: "state_refines sa sa"
  unfolding state_refines_def by simp

lemma state_refines_trans:
  "state_refines sa sb \<Longrightarrow> state_refines sb sc \<Longrightarrow> state_refines sa sc"
  unfolding state_refines_def by metis

text \<open>A consistent state refined by another transports its consistency upward:
  if \<^term>\<open>sa\<close> refines a consistent \<^term>\<open>sb\<close>, then \<^term>\<open>sa\<close> is consistent.\<close>

lemma state_refines_preserves_consistency:
  assumes "state_refines sa sb" and "consistent_state sb"
  shows "consistent_state sa"
  unfolding consistent_state_def
proof (intro allI impI)
  fix c1 c2 aid s1 s2
  assume "get_reg_state sa c1 aid = Some s1" and "get_reg_state sa c2 aid = Some s2"
  moreover have "c1 \<in> connected_chains sa aid" and "c2 \<in> connected_chains sa aid"
    using calculation unfolding connected_chains_def asset_exists_def
          get_reg_state_def get_asset_state_def
    by (auto split: option.splits)
  ultimately have "get_reg_state sb c1 aid = Some s1" and "get_reg_state sb c2 aid = Some s2"
    using assms(1) unfolding state_refines_def by metis+
  then show "s1 = s2" using assms(2) unfolding consistent_state_def by blast
qed


section \<open>Authenticated Cross-Domain State\<close>

text \<open>
  An authenticated state structure equips a Merkle interface
  \<^term>\<open>(h, bo, m)\<close> with an extraction map \<open>extract_map\<close> that reads a global
  state out of an authenticated value.  The three coherence assumptions tie the
  authenticated layer to the state-glue layer:

    * \<open>extract_respects_merging\<close>: merging hash-compatible authenticated values
      yields a state that is the join of the extracted views;
    * \<open>extract_under_blinding\<close>: a blinding of an authenticated value extracts to
      a refinement of the extracted state;
    * \<open>extract_preserves_validity\<close>: every extracted state is valid.

  The merging and blinding assumptions are guarded by the hash-equality
  condition \<^term>\<open>h a = h b\<close>, which is the ADS notion of mergeability.  The two
  soundness theorems below discharge this condition from the ADS lemmas
  \<open>merge_respects_hashes\<close> and \<open>hash\<close>, and use \<open>join\<close> to exhibit the join as a
  refinement of each input — so the Merkle interface is used in the proofs, not
  merely imported.
\<close>

text \<open>The extraction map is named \<open>extract_map\<close> rather than \<open>extract\<close>, because
  \<open>extract\<close> is a reserved Isabelle command keyword and cannot be used as a
  locale parameter name.\<close>

locale authenticated_state =
  mk: merkle_interface h bo m
  for h :: "'d \<Rightarrow> 'e"
    and bo :: "'d \<Rightarrow> 'd \<Rightarrow> bool"
    and m :: "'d \<Rightarrow> 'd \<Rightarrow> 'd option"
    and extract_map :: "'d \<Rightarrow> global_state option" +
  assumes extract_respects_merging:
      "\<lbrakk> h a = h b; m a b = Some ab; extract_map a = Some sa; extract_map b = Some sb \<rbrakk>
       \<Longrightarrow> \<exists>sab. extract_map ab = Some sab \<and> state_join sa sb sab"
    and extract_under_blinding:
      "\<lbrakk> h a = h b; bo a b; extract_map b = Some sb \<rbrakk>
       \<Longrightarrow> \<exists>sa. extract_map a = Some sa \<and> state_refines sa sb"
    and extract_preserves_validity:
      "extract_map a = Some s \<Longrightarrow> valid_state s"
begin

text \<open>Blinding preserves hashes: the explicit state-level use of the
  @{thm [source] mk.hash} lemma of the Merkle interface.\<close>

lemma bo_hash_eq:
  assumes "bo x y"
  shows "h x = h y"
proof -
  have "vimage2p h h (=) x y" using mk.hash assms by (rule predicate2D)
  then show ?thesis by (simp add: vimage2p_def)
qed

text \<open>
  Soundness of authenticated preservation under merging.  If two authenticated
  values merge, then their extracted states have a valid join, and that join
  refines each input view.  The proof calls \<open>merge_respects_hashes\<close> (to certify
  mergeability as hash-equality), \<open>join\<close> (to obtain the blinding relation of each
  input to the merge), and \<open>hash\<close> (via @{thm [source] bo_hash_eq}, to transport
  that blinding relation to the extracted states).
\<close>

theorem authenticated_preservation_soundness:
  assumes mab: "m a b = Some ab"
    and ea: "extract_map a = Some sa" and va: "valid_state sa"
    and eb: "extract_map b = Some sb" and vb: "valid_state sb"
  shows "\<exists>sab. extract_map ab = Some sab \<and> valid_state sab
              \<and> state_refines sa sab \<and> state_refines sb sab"
proof -
  \<comment> \<open>ADS lemma 1: a merge exists, so the hashes agree (mergeability).\<close>
  have ex_merge: "\<exists>x. m a b = Some x" using mab by blast
  have hab: "h a = h b" using mk.merge_respects_hashes ex_merge by blast
  \<comment> \<open>ADS lemma 2: the merge \<open>ab\<close> is the least upper bound of \<open>a\<close> and \<open>b\<close> (join).\<close>
  have lub: "bo a ab \<and> bo b ab \<and> (\<forall>u. bo a u \<longrightarrow> bo b u \<longrightarrow> bo ab u)"
    using mk.join mab by blast
  then have boa: "bo a ab" and bob: "bo b ab" by simp_all
  \<comment> \<open>State-level join from the merging assumption, using the hash equality \<open>hab\<close>.\<close>
  obtain sab where esab: "extract_map ab = Some sab" and sj: "state_join sa sb sab"
    using extract_respects_merging[OF hab mab ea eb] by blast
  have vsab: "valid_state sab" using extract_preserves_validity[OF esab] .
  \<comment> \<open>ADS lemma 3 (hash): each input blinds to \<open>ab\<close>, hence shares its hash, so the
      extracted join refines each input view.\<close>
  have "h a = h ab" using bo_hash_eq[OF boa] .
  then have ra: "state_refines sa sab"
    using extract_under_blinding[OF \<open>h a = h ab\<close> boa esab] ea by auto
  have "h b = h ab" using bo_hash_eq[OF bob] .
  then have rb: "state_refines sb sab"
    using extract_under_blinding[OF \<open>h b = h ab\<close> bob esab] eb by auto
  from esab vsab ra rb show ?thesis by blast
qed

text \<open>
  Blinded views preserve validity.  A blinding \<open>a\<close> of an authenticated value
  \<open>b\<close> extracts to a valid state that refines the extraction of \<open>b\<close>.  This is the
  need-to-know guarantee: a partial (blinded) view is still a valid,
  consistency-respecting view.  The proof calls \<open>hash\<close> (via
  @{thm [source] bo_hash_eq}) to certify the hash equality that licenses the
  blinding coherence assumption.
\<close>

theorem blinded_view_preserves_validity:
  assumes boab: "bo a b" and eb: "extract_map b = Some sb" and vb: "valid_state sb"
  shows "\<exists>sa. extract_map a = Some sa \<and> valid_state sa \<and> state_refines sa sb"
proof -
  have hab: "h a = h b" using bo_hash_eq[OF boab] .
  obtain sa where ea: "extract_map a = Some sa" and sr: "state_refines sa sb"
    using extract_under_blinding[OF hab boab eb] by blast
  have "valid_state sa" using extract_preserves_validity[OF ea] .
  with ea sr show ?thesis by blast
qed

end


section \<open>Authenticated Cross-Domain State: the Oraclizer Instance\<close>

text \<open>
  We discharge the model obligation of @{locale authenticated_state} by
  exhibiting a concrete, non-degenerate instance.  Without it the two soundness
  theorems above would range over a possibly empty class of structures; the
  instance below pins them to an extraction map that reads a genuine cross-domain
  state out of authenticated data.

  An authenticated datum is a pair \<^term>\<open>(r, P)\<close>: a consensus regulatory state
  \<open>r\<close> together with the set \<open>P\<close> of chains that have revealed --- are known to
  hold --- the shared asset in that state.  The hash @{term auth_hash} commits to
  the consensus state \<open>r\<close> alone, so two data are mergeable exactly when they
  agree on \<open>r\<close>; the merge @{term auth_merge} then unions the revealed-chain sets,
  and the blinding order @{term auth_bo} forgets some of them.  This is the
  state-level reading the glue layer asks for: @{term auth_merge} realises the
  ADS \<open>join\<close>, @{term auth_bo} the ADS blinding order, and @{term auth_extract}
  sends \<^term>\<open>(r, P)\<close> to the global state in which every chain of \<open>P\<close> holds the
  asset in state \<open>r\<close>.  Because the hash fixes \<open>r\<close>, merging never forces two
  chains to disagree, so the extracted join is consistent and the three
  obligations hold with no weakening of the hypotheses.
\<close>

definition auth_hash :: "reg_state \<times> chain_id set \<Rightarrow> reg_state" where
  "auth_hash a = fst a"

definition auth_bo :: "reg_state \<times> chain_id set \<Rightarrow> reg_state \<times> chain_id set \<Rightarrow> bool" where
  "auth_bo a b \<longleftrightarrow> fst a = fst b \<and> snd a \<subseteq> snd b"

definition auth_merge ::
  "reg_state \<times> chain_id set \<Rightarrow> reg_state \<times> chain_id set \<Rightarrow> (reg_state \<times> chain_id set) option" where
  "auth_merge a b = (if fst a = fst b then Some (fst a, snd a \<union> snd b) else None)"

text \<open>The merge is the union of revealed-chain sets, guarded by agreement on the
  consensus state.  Idempotence, commutativity and associativity descend from the
  corresponding laws of set union, and the blinding order is exactly the subset
  order on revealed chains; hence the triple is a Merkle interface.\<close>

lemma merkle_interface_auth [locale_witness]:
  "merkle_interface auth_hash auth_bo auth_merge"
proof (rule merkle_interface.intro)
  show "\<And>a b. (auth_hash a = auth_hash b) = (\<exists>ab. auth_merge a b = Some ab)"
    by (auto simp: auth_hash_def auth_merge_def)
  show "\<And>a. auth_merge a a = Some a"
    by (simp add: auth_merge_def)
  show "\<And>a b. auth_merge a b = auth_merge b a"
    by (auto simp: auth_merge_def Un_commute)
  show "\<And>a b c. auth_merge a b \<bind> auth_merge c = auth_merge b c \<bind> auth_merge a"
    by (auto simp: auth_merge_def ac_simps split: if_splits)
  show "\<And>a b. auth_bo a b = (auth_merge a b = Some b)"
    by (auto simp: auth_bo_def auth_merge_def prod_eq_iff subset_Un_eq)
qed

text \<open>The extraction map.  \<^term>\<open>auth_state r P\<close> is the global state in which each
  chain of \<open>P\<close> holds asset \<open>0\<close> in regulatory state \<open>r\<close>, with nothing locked.\<close>

definition auth_state :: "reg_state \<Rightarrow> chain_id set \<Rightarrow> global_state" where
  "auth_state r P =
     \<lparr> gs_chains = (\<lambda>c a. if c \<in> P \<and> a = 0
                          then Some \<lparr> as_asset_id = 0, as_reg_state = r,
                                      as_owner = 0, as_locked = False \<rparr>
                          else None),
       gs_locks = (\<lambda>a. False) \<rparr>"

definition auth_extract :: "reg_state \<times> chain_id set \<Rightarrow> global_state option" where
  "auth_extract a = Some (auth_state (fst a) (snd a))"

text \<open>Accessors of the extracted state, read off the definition.\<close>

lemma auth_state_get_reg:
  "get_reg_state (auth_state r P) c a = (if c \<in> P \<and> a = 0 then Some r else None)"
  by (simp add: auth_state_def get_reg_state_def get_asset_state_def split: if_splits)

lemma auth_state_connected:
  "connected_chains (auth_state r P) a = (if a = 0 then P else {})"
  by (auto simp: connected_chains_def asset_exists_def get_asset_state_def auth_state_def
           split: if_splits)

text \<open>Every extracted state is valid: all chains carry the same consensus state
  \<open>r\<close>, so the state is consistent, and no asset is locked.\<close>

lemma auth_state_valid: "valid_state (auth_state r P)"
proof -
  have "consistent_state (auth_state r P)"
    unfolding consistent_state_def by (auto simp: auth_state_get_reg split: if_splits)
  moreover have "no_locked_without_reason (auth_state r P)"
    by (simp add: no_locked_without_reason_def is_locked_def auth_state_def)
  ultimately show ?thesis by (simp add: valid_state_def)
qed

text \<open>The merge of two views with the same consensus state extracts to the join
  of the two extracted states: the union of revealed chains, agreeing on \<open>r\<close>.\<close>

lemma state_join_auth:
  "state_join (auth_state r Pa) (auth_state r Pb) (auth_state r (Pa \<union> Pb))"
  unfolding state_join_def
  by (auto simp: auth_state_connected auth_state_get_reg split: if_splits)

text \<open>A view over fewer chains refines a view over more chains with the same
  consensus state.\<close>

lemma state_refines_auth:
  "Pa \<subseteq> Pb \<Longrightarrow> state_refines (auth_state r Pa) (auth_state r Pb)"
  unfolding state_refines_def
  by (auto simp: auth_state_connected auth_state_get_reg subset_iff split: if_splits)

text \<open>
  The instance.  The three coherence obligations are discharged from the lemmas
  above: merging extracts to the join (@{thm [source] state_join_auth}), blinding
  extracts to a refinement (@{thm [source] state_refines_auth}), and every
  extracted state is valid (@{thm [source] auth_state_valid}).  The Merkle
  interface obligation is @{thm [source] merkle_interface_auth}.
\<close>

interpretation oss_authenticated:
  authenticated_state auth_hash auth_bo auth_merge auth_extract
proof unfold_locales
  fix a b ab sa sb
  assume hab: "auth_hash a = auth_hash b" and mab: "auth_merge a b = Some ab"
     and ea: "auth_extract a = Some sa" and eb: "auth_extract b = Some sb"
  from hab have rfst: "fst a = fst b" by (simp add: auth_hash_def)
  with mab have ab_eq: "ab = (fst a, snd a \<union> snd b)" by (simp add: auth_merge_def)
  have sa_eq: "sa = auth_state (fst a) (snd a)" using ea by (simp add: auth_extract_def)
  have sb_eq: "sb = auth_state (fst a) (snd b)" using eb rfst by (simp add: auth_extract_def)
  have "auth_extract ab = Some (auth_state (fst a) (snd a \<union> snd b))"
    by (simp add: auth_extract_def ab_eq)
  moreover have "state_join sa sb (auth_state (fst a) (snd a \<union> snd b))"
    unfolding sa_eq sb_eq by (rule state_join_auth)
  ultimately show "\<exists>sab. auth_extract ab = Some sab \<and> state_join sa sb sab"
    by blast
next
  fix a b sb
  assume bo: "auth_bo a b" and eb: "auth_extract b = Some sb"
  from bo have rfst: "fst a = fst b" and sub: "snd a \<subseteq> snd b"
    by (simp_all add: auth_bo_def)
  have sb_eq: "sb = auth_state (fst a) (snd b)" using eb rfst by (simp add: auth_extract_def)
  have "auth_extract a = Some (auth_state (fst a) (snd a))" by (simp add: auth_extract_def)
  moreover have "state_refines (auth_state (fst a) (snd a)) sb"
    unfolding sb_eq using sub by (rule state_refines_auth)
  ultimately show "\<exists>sa. auth_extract a = Some sa \<and> state_refines sa sb"
    by blast
next
  fix a s
  assume "auth_extract a = Some s"
  then have "s = auth_state (fst a) (snd a)" by (simp add: auth_extract_def)
  then show "valid_state s" by (simp add: auth_state_valid)
qed

text \<open>
  The model is non-degenerate: the extraction map returns rich states, and the
  merging law is exercised by genuinely distinct partial views.  The witnesses
  below record that a two-chain view extracts to a state with two connected
  chains carrying \<^term>\<open>ACTIVE\<close>, and that merging the single-chain views over
  chains \<open>0\<close> and \<^term>\<open>Suc 0\<close> joins them into the two-chain view.
\<close>

lemma oss_authenticated_extract_nontrivial:
  "auth_extract (ACTIVE, {0, Suc 0}) = Some (auth_state ACTIVE {0, Suc 0})"
  "connected_chains (auth_state ACTIVE {0, Suc 0}) 0 = {0, Suc 0}"
  "get_reg_state (auth_state ACTIVE {0, Suc 0}) 0 0 = Some ACTIVE"
  by (simp_all add: auth_extract_def auth_state_connected auth_state_get_reg)

lemma oss_authenticated_merge_nontrivial:
  "auth_merge (ACTIVE, {0}) (ACTIVE, {Suc 0}) = Some (ACTIVE, {0, Suc 0})"
  "auth_extract (ACTIVE, {0}) = Some (auth_state ACTIVE {0})"
  "auth_extract (ACTIVE, {Suc 0}) = Some (auth_state ACTIVE {Suc 0})"
  "state_join (auth_state ACTIVE {0}) (auth_state ACTIVE {Suc 0}) (auth_state ACTIVE {0, Suc 0})"
  using state_join_auth[of ACTIVE "{0}" "{Suc 0}"]
  by (simp_all add: auth_merge_def auth_extract_def insert_commute)

text \<open>
  Regression witness for the containment clause of \<^const>\<open>state_join\<close>.  The
  rogue candidate extends the union of the two single-chain \<^const>\<open>ACTIVE\<close>
  views with a \<^const>\<open>FROZEN\<close> holding on chain \<open>7\<close> --- a chain revealed by
  neither view.  The candidate is itself inconsistent, and the containment
  clause rejects it as a join of the two views.
\<close>

definition rogue_join_state :: global_state where
  "rogue_join_state =
     \<lparr> gs_chains = (\<lambda>c a. if a = 0 \<and> (c = 0 \<or> c = Suc 0)
                          then Some \<lparr> as_asset_id = 0, as_reg_state = ACTIVE,
                                      as_owner = 0, as_locked = False \<rparr>
                          else if a = 0 \<and> c = 7
                          then Some \<lparr> as_asset_id = 0, as_reg_state = FROZEN,
                                      as_owner = 0, as_locked = False \<rparr>
                          else None),
       gs_locks = (\<lambda>a. False) \<rparr>"

lemma rogue_join_state_get_reg:
  "get_reg_state rogue_join_state c a =
     (if a = 0 \<and> (c = 0 \<or> c = Suc 0) then Some ACTIVE
      else if a = 0 \<and> c = 7 then Some FROZEN else None)"
  by (simp add: rogue_join_state_def get_reg_state_def get_asset_state_def)

lemma rogue_join_excluded:
  "\<not> consistent_state rogue_join_state"
  "\<not> state_join (auth_state ACTIVE {0}) (auth_state ACTIVE {Suc 0}) rogue_join_state"
proof -
  have a: "get_reg_state rogue_join_state 0 0 = Some ACTIVE"
    and f: "get_reg_state rogue_join_state 7 0 = Some FROZEN"
    by (simp_all add: rogue_join_state_get_reg)
  show "\<not> consistent_state rogue_join_state"
  proof
    assume "consistent_state rogue_join_state"
    then have "ACTIVE = FROZEN" using a f unfolding consistent_state_def by blast
    then show False by simp
  qed
  have c7: "(7::nat) \<in> connected_chains rogue_join_state 0"
    by (simp add: connected_chains_def asset_exists_def get_asset_state_def
                  rogue_join_state_def)
  have "(7::nat) \<notin> connected_chains (auth_state ACTIVE {0}) 0"
    and "(7::nat) \<notin> connected_chains (auth_state ACTIVE {Suc 0}) 0"
    by (simp_all add: auth_state_connected)
  then show "\<not> state_join (auth_state ACTIVE {0}) (auth_state ACTIVE {Suc 0}) rogue_join_state"
    using c7 unfolding state_join_def by blast
qed


section \<open>Inconsistency Measure on Global States\<close>

text \<open>
  The convergence argument needs a well-founded progress measure that a
  synchronization strictly decreases while the global state is inconsistent.
  We use the number of unordered pairs of connected chains that disagree on
  the regulatory state of a shared asset.  On a state with finitely many
  asset holdings this count is finite, it is zero exactly when the state is
  consistent, and a synchronization of an inconsistent asset strictly
  decreases it.
\<close>

definition finite_domain :: "global_state \<Rightarrow> bool" where
  "finite_domain gs \<longleftrightarrow> finite {(c, aid). asset_exists gs c aid}"

definition inconsistency_set ::
  "global_state \<Rightarrow> (chain_id \<times> chain_id \<times> asset_id) set" where
  "inconsistency_set gs =
     {(c1, c2, aid). c1 \<in> connected_chains gs aid \<and> c2 \<in> connected_chains gs aid
        \<and> c1 < c2 \<and> get_reg_state gs c1 aid \<noteq> get_reg_state gs c2 aid}"

definition inconsistency_pairs :: "global_state \<Rightarrow> nat" where
  "inconsistency_pairs gs = card (inconsistency_set gs)"

text \<open>A connected chain always carries a defined regulatory state for the asset.\<close>

lemma connected_chains_get_reg_state:
  assumes "c \<in> connected_chains gs aid"
  shows "\<exists>s. get_reg_state gs c aid = Some s"
  using assms
  unfolding connected_chains_def asset_exists_def get_reg_state_def get_asset_state_def
  by (auto split: option.splits)

text \<open>On a finite-domain state, the connected-chain set of any asset is finite.\<close>

lemma connected_chains_finite:
  assumes "finite_domain gs"
  shows "finite (connected_chains gs aid)"
proof -
  have "connected_chains gs aid \<subseteq> fst ` {(c, a). asset_exists gs c a}"
    by (auto simp: connected_chains_def image_iff)
  moreover have "finite (fst ` {(c, a). asset_exists gs c a})"
    using assms unfolding finite_domain_def by simp
  ultimately show ?thesis by (rule finite_subset)
qed

text \<open>On a finite-domain state, the inconsistency set is finite.\<close>

lemma inconsistency_set_finite:
  assumes "finite_domain gs"
  shows "finite (inconsistency_set gs)"
proof -
  let ?E = "{(c, a). asset_exists gs c a}"
  have "inconsistency_set gs \<subseteq> (\<lambda>(p, q). (fst p, fst q, snd p)) ` (?E \<times> ?E)"
  proof
    fix t assume "t \<in> inconsistency_set gs"
    then obtain c1 c2 aid where t: "t = (c1, c2, aid)"
      and m1: "c1 \<in> connected_chains gs aid" and m2: "c2 \<in> connected_chains gs aid"
      unfolding inconsistency_set_def by auto
    from m1 have e1: "(c1, aid) \<in> ?E" by (simp add: connected_chains_def)
    from m2 have e2: "(c2, aid) \<in> ?E" by (simp add: connected_chains_def)
    have "t = (\<lambda>(p, q). (fst p, fst q, snd p)) ((c1, aid), (c2, aid))" using t by simp
    then show "t \<in> (\<lambda>(p, q). (fst p, fst q, snd p)) ` (?E \<times> ?E)"
      using e1 e2 by blast
  qed
  moreover have "finite ((\<lambda>(p, q). (fst p, fst q, snd p)) ` (?E \<times> ?E))"
    using assms unfolding finite_domain_def by simp
  ultimately show ?thesis by (rule finite_subset)
qed

text \<open>The measure is zero exactly on consistent states.\<close>

lemma inconsistency_pairs_zero_iff_consistent:
  assumes "finite_domain gs"
  shows "inconsistency_pairs gs = 0 \<longleftrightarrow> consistent_state gs"
proof
  assume "inconsistency_pairs gs = 0"
  then have empty: "inconsistency_set gs = {}"
    using inconsistency_set_finite[OF assms] unfolding inconsistency_pairs_def by simp
  show "consistent_state gs"
    unfolding consistent_state_def
  proof (intro allI impI)
    fix c1 c2 aid s1 s2
    assume a1: "get_reg_state gs c1 aid = Some s1" and a2: "get_reg_state gs c2 aid = Some s2"
    have in1: "c1 \<in> connected_chains gs aid" and in2: "c2 \<in> connected_chains gs aid"
      using a1 a2 unfolding connected_chains_def asset_exists_def
            get_reg_state_def get_asset_state_def by (auto split: option.splits)
    show "s1 = s2"
    proof (rule ccontr)
      assume ne: "s1 \<noteq> s2"
      then have rne: "get_reg_state gs c1 aid \<noteq> get_reg_state gs c2 aid" using a1 a2 by simp
      have "c1 \<noteq> c2" using a1 a2 ne by auto
      then consider "c1 < c2" | "c2 < c1" by linarith
      then show False
      proof cases
        case 1
        then have "(c1, c2, aid) \<in> inconsistency_set gs"
          using in1 in2 rne unfolding inconsistency_set_def by simp
        with empty show False by simp
      next
        case 2
        then have "(c2, c1, aid) \<in> inconsistency_set gs"
          using in1 in2 rne unfolding inconsistency_set_def by auto
        with empty show False by simp
      qed
    qed
  qed
next
  assume cons: "consistent_state gs"
  have "inconsistency_set gs = {}"
  proof (rule ccontr)
    assume "inconsistency_set gs \<noteq> {}"
    then obtain c1 c2 aid where
      m1: "c1 \<in> connected_chains gs aid" and m2: "c2 \<in> connected_chains gs aid"
      and rne: "get_reg_state gs c1 aid \<noteq> get_reg_state gs c2 aid"
      unfolding inconsistency_set_def by auto
    obtain s1 where s1: "get_reg_state gs c1 aid = Some s1"
      using connected_chains_get_reg_state[OF m1] by blast
    obtain s2 where s2: "get_reg_state gs c2 aid = Some s2"
      using connected_chains_get_reg_state[OF m2] by blast
    have "s1 = s2" using cons s1 s2 unfolding consistent_state_def by blast
    with s1 s2 rne show False by simp
  qed
  then show "inconsistency_pairs gs = 0" unfolding inconsistency_pairs_def by simp
qed


section \<open>Structural Effect of Synchronization\<close>

text \<open>
  The following lemmas isolate the effect of a successful synchronization on
  the regulatory states and on asset existence.  They are proved without
  assuming the input state is valid (consistent and unlocked), because the
  convergence argument starts from an arbitrary state.  The existing theorem
  @{thm [source] regulatory_homomorphism} establishes the analogous fact under
  the @{term valid_state} hypothesis; here we re-establish the parts needed for
  convergence with no such hypothesis.
\<close>

lemma sync_components:
  assumes "sync src act aid0 gs = Some gs'"
  shows "\<exists>current_st new_st gs_locked.
           get_reg_state gs src aid0 = Some current_st
         \<and> reg_transition current_st act = Some new_st
         \<and> acquire_lock gs aid0 = Some gs_locked
         \<and> gs' = release_lock
                   (update_all_chains gs_locked aid0 new_st (connected_chains gs aid0)) aid0"
  using assms unfolding sync_def by (auto split: option.splits simp: Let_def)

text \<open>Synchronizing asset \<open>aid0\<close> leaves the chain map of every other asset unchanged.\<close>

lemma sync_chains_other_asset:
  assumes synced: "sync src act aid0 gs = Some gs'" and ne: "aid \<noteq> aid0"
  shows "gs_chains gs' c aid = gs_chains gs c aid"
proof -
  from sync_components[OF synced] obtain current_st new_st gs_locked where
    lock: "acquire_lock gs aid0 = Some gs_locked"
    and gs': "gs' = release_lock
                 (update_all_chains gs_locked aid0 new_st (connected_chains gs aid0)) aid0"
    by blast
  have lc: "gs_chains gs_locked = gs_chains gs" using acquire_lock_chains[OF lock] .
  have "gs_chains (update_all_chains gs_locked aid0 new_st (connected_chains gs aid0)) c aid
        = gs_chains gs_locked c aid"
    using update_all_chains_other_asset[OF ne] by simp
  then show ?thesis unfolding gs' release_lock_chains using lc by simp
qed

lemma sync_reg_other_asset:
  assumes synced: "sync src act aid0 gs = Some gs'" and ne: "aid \<noteq> aid0"
  shows "get_reg_state gs' c aid = get_reg_state gs c aid"
  unfolding get_reg_state_def get_asset_state_def
  using sync_chains_other_asset[OF synced ne] by simp

text \<open>After synchronizing asset \<open>aid0\<close>, all chains connected to \<open>aid0\<close> agree on its
  new regulatory state.\<close>

lemma sync_synced_asset_uniform:
  assumes synced: "sync src act aid0 gs = Some gs'"
  shows "\<exists>ns. \<forall>c' \<in> connected_chains gs aid0. get_reg_state gs' c' aid0 = Some ns"
proof -
  from sync_components[OF synced] obtain current_st new_st gs_locked where
    lock: "acquire_lock gs aid0 = Some gs_locked"
    and gs': "gs' = release_lock
                 (update_all_chains gs_locked aid0 new_st (connected_chains gs aid0)) aid0"
    by blast
  have lc: "gs_chains gs_locked = gs_chains gs" using acquire_lock_chains[OF lock] .
  have "\<forall>c' \<in> connected_chains gs aid0. get_reg_state gs' c' aid0 = Some new_st"
  proof
    fix c' assume c'conn: "c' \<in> connected_chains gs aid0"
    then have "asset_exists gs c' aid0" by (simp add: connected_chains_def)
    then obtain ast where ast: "get_asset_state gs c' aid0 = Some ast"
      unfolding asset_exists_def by auto
    then have astl: "get_asset_state gs_locked c' aid0 = Some ast"
      unfolding get_asset_state_def using lc by simp
    have "get_reg_state
            (update_all_chains gs_locked aid0 new_st (connected_chains gs aid0)) c' aid0 = Some new_st"
      using update_all_chains_reg_state[OF c'conn astl] .
    then show "get_reg_state gs' c' aid0 = Some new_st"
      unfolding gs' by (simp add: release_lock_reg_state)
  qed
  then show ?thesis by blast
qed

text \<open>Synchronization preserves asset existence, hence the connected-chain sets.\<close>

lemma sync_asset_exists_preserved:
  assumes synced: "sync src act aid0 gs = Some gs'"
  shows "asset_exists gs' c aid = asset_exists gs c aid"
proof (cases "aid = aid0")
  case False
  then have "gs_chains gs' c aid = gs_chains gs c aid"
    using sync_chains_other_asset[OF synced] by simp
  then show ?thesis unfolding asset_exists_def get_asset_state_def by simp
next
  case True
  show ?thesis
  proof (cases "c \<in> connected_chains gs aid0")
    case in_conn: True
    then have e_gs: "asset_exists gs c aid0" by (simp add: connected_chains_def)
    obtain ns where "\<forall>c'\<in>connected_chains gs aid0. get_reg_state gs' c' aid0 = Some ns"
      using sync_synced_asset_uniform[OF synced] by blast
    then have "get_reg_state gs' c aid0 = Some ns" using in_conn by blast
    then have "asset_exists gs' c aid0"
      unfolding asset_exists_def get_reg_state_def get_asset_state_def
      by (auto split: option.splits)
    with e_gs True show ?thesis by simp
  next
    case out_conn: False
    then have ngs: "\<not> asset_exists gs c aid0" by (simp add: connected_chains_def)
    from sync_components[OF synced] obtain current_st new_st gs_locked where
      lock: "acquire_lock gs aid0 = Some gs_locked"
      and gs': "gs' = release_lock
                   (update_all_chains gs_locked aid0 new_st (connected_chains gs aid0)) aid0"
      by blast
    have lc: "gs_chains gs_locked = gs_chains gs" using acquire_lock_chains[OF lock] .
    have "gs_chains gs' c = gs_chains gs c"
      unfolding gs' release_lock_chains
      using update_all_chains_outside_targets[OF out_conn] lc by simp
    then have "asset_exists gs' c aid0 = asset_exists gs c aid0"
      unfolding asset_exists_def get_asset_state_def by simp
    with True show ?thesis by simp
  qed
qed

lemma sync_connected_chains_preserved:
  assumes "sync src act aid0 gs = Some gs'"
  shows "connected_chains gs' aid = connected_chains gs aid"
  unfolding connected_chains_def using sync_asset_exists_preserved[OF assms] by simp

lemma sync_preserves_finite_domain:
  assumes "finite_domain gs" and "sync src act aid0 gs = Some gs'"
  shows "finite_domain gs'"
proof -
  have "{(c, aid). asset_exists gs' c aid} = {(c, aid). asset_exists gs c aid}"
    using sync_asset_exists_preserved[OF assms(2)] by simp
  then show ?thesis using assms(1) unfolding finite_domain_def by simp
qed

text \<open>Synchronization preserves the unlocked invariant.  This is the lock half of
  @{thm [source] valid_state_preservation}, re-established without the
  @{term consistent_state} hypothesis.\<close>

lemma sync_preserves_unlocked:
  assumes nl: "no_locked_without_reason gs" and synced: "sync src act aid0 gs = Some gs'"
  shows "no_locked_without_reason gs'"
proof -
  from sync_components[OF synced] obtain current_st new_st gs_locked where
    lock: "acquire_lock gs aid0 = Some gs_locked"
    and gs': "gs' = release_lock
                 (update_all_chains gs_locked aid0 new_st (connected_chains gs aid0)) aid0"
    by blast
  from lock have locked_locks: "gs_locks gs_locked = (gs_locks gs)(aid0 := True)"
    unfolding acquire_lock_def is_locked_def by (auto split: if_splits)
  have upd_locks: "gs_locks (update_all_chains gs_locked aid0 new_st (connected_chains gs aid0))
                   = gs_locks gs_locked"
    using update_all_chains_locks by simp
  have final_locks: "gs_locks gs' = (gs_locks gs_locked)(aid0 := False)"
    unfolding gs' release_lock_def using upd_locks by simp
  show ?thesis
  unfolding no_locked_without_reason_def is_locked_def
  proof
    fix aid'
    show "\<not> gs_locks gs' aid'"
    proof (cases "aid' = aid0")
      case True then show ?thesis using final_locks by simp
    next
      case False
      then have "gs_locks gs' aid' = gs_locks gs aid'"
        using final_locks locked_locks by simp
      also have "\<dots> = False"
        using nl unfolding no_locked_without_reason_def is_locked_def by simp
      finally show ?thesis by simp
    qed
  qed
qed


section \<open>The Critical Path: Synchronization Reduces Inconsistency\<close>

text \<open>
  A connected chain witnesses asset existence, so a defined regulatory state
  places the chain in the connected set.
\<close>

lemma get_reg_state_connected:
  assumes "get_reg_state gs c aid = Some s"
  shows "c \<in> connected_chains gs aid"
  using assms unfolding connected_chains_def asset_exists_def
        get_reg_state_def get_asset_state_def by (auto split: option.splits)

text \<open>
  The critical convergence step.  Synchronizing an asset \<open>aid0\<close> on which two
  connected chains disagree strictly decreases the inconsistency measure: every
  inconsistent pair of \<open>aid0\<close> is removed (all its connected chains are driven to
  one regulatory state), pairs of other assets are untouched, and the witness
  pair certifies that at least one pair really disappears.
\<close>

lemma sync_reduces_inconsistency:
  assumes fin: "finite_domain gs"
    and synced: "sync src act aid0 gs = Some gs'"
    and ca: "ca \<in> connected_chains gs aid0"
    and cb: "cb \<in> connected_chains gs aid0"
    and dis: "get_reg_state gs ca aid0 \<noteq> get_reg_state gs cb aid0"
  shows "inconsistency_pairs gs' < inconsistency_pairs gs"
proof -
  obtain ns where uniform: "\<forall>c'\<in>connected_chains gs aid0. get_reg_state gs' c' aid0 = Some ns"
    using sync_synced_asset_uniform[OF synced] by blast
  have conn_eq: "\<And>aid. connected_chains gs' aid = connected_chains gs aid"
    using sync_connected_chains_preserved[OF synced] by simp
  \<comment> \<open>Step 1: the inconsistency set of \<open>gs'\<close> is contained in that of \<open>gs\<close>.\<close>
  have subset: "inconsistency_set gs' \<subseteq> inconsistency_set gs"
  proof
    fix t assume "t \<in> inconsistency_set gs'"
    then obtain c1 c2 aid where t: "t = (c1, c2, aid)"
      and i1: "c1 \<in> connected_chains gs' aid" and i2: "c2 \<in> connected_chains gs' aid"
      and lt: "c1 < c2" and rne: "get_reg_state gs' c1 aid \<noteq> get_reg_state gs' c2 aid"
      unfolding inconsistency_set_def by auto
    have ane: "aid \<noteq> aid0"
    proof
      assume eq: "aid = aid0"
      have "c1 \<in> connected_chains gs aid0" "c2 \<in> connected_chains gs aid0"
        using i1 i2 conn_eq eq by auto
      then have "get_reg_state gs' c1 aid0 = Some ns" "get_reg_state gs' c2 aid0 = Some ns"
        using uniform by auto
      with rne eq show False by simp
    qed
    have "c1 \<in> connected_chains gs aid" "c2 \<in> connected_chains gs aid"
      using i1 i2 conn_eq by auto
    moreover have "get_reg_state gs c1 aid \<noteq> get_reg_state gs c2 aid"
      using rne sync_reg_other_asset[OF synced ane] by simp
    ultimately have "(c1, c2, aid) \<in> inconsistency_set gs"
      using lt unfolding inconsistency_set_def by simp
    then show "t \<in> inconsistency_set gs" using t by simp
  qed
  \<comment> \<open>Step 2: the witness pair on \<open>aid0\<close> is in \<open>gs\<close> but not in \<open>gs'\<close>.\<close>
  have caneb: "ca \<noteq> cb" using dis by auto
  define c1 where "c1 = min ca cb"
  define c2 where "c2 = max ca cb"
  have lt: "c1 < c2" using caneb unfolding c1_def c2_def by auto
  have c1conn: "c1 \<in> connected_chains gs aid0" and c2conn: "c2 \<in> connected_chains gs aid0"
    using ca cb unfolding c1_def c2_def by (auto simp: min_def max_def)
  have wdis: "get_reg_state gs c1 aid0 \<noteq> get_reg_state gs c2 aid0"
    using dis unfolding c1_def c2_def by (auto simp: min_def max_def)
  have wit_in: "(c1, c2, aid0) \<in> inconsistency_set gs"
    using c1conn c2conn lt wdis unfolding inconsistency_set_def by simp
  have wit_out: "(c1, c2, aid0) \<notin> inconsistency_set gs'"
  proof
    assume "(c1, c2, aid0) \<in> inconsistency_set gs'"
    then have rne: "get_reg_state gs' c1 aid0 \<noteq> get_reg_state gs' c2 aid0"
      and "c1 \<in> connected_chains gs' aid0" and "c2 \<in> connected_chains gs' aid0"
      unfolding inconsistency_set_def by auto
    then have "c1 \<in> connected_chains gs aid0" "c2 \<in> connected_chains gs aid0"
      using conn_eq by auto
    then have "get_reg_state gs' c1 aid0 = Some ns" "get_reg_state gs' c2 aid0 = Some ns"
      using uniform by auto
    with rne show False by simp
  qed
  \<comment> \<open>Step 3: a strict subset of a finite set has strictly smaller cardinality.\<close>
  have psub: "inconsistency_set gs' \<subset> inconsistency_set gs"
    using subset wit_in wit_out by blast
  have "card (inconsistency_set gs') < card (inconsistency_set gs)"
    using psubset_card_mono[OF inconsistency_set_finite[OF fin] psub] .
  then show ?thesis unfolding inconsistency_pairs_def .
qed


section \<open>Existence of a Reducing Synchronization\<close>

text \<open>
  From any inconsistent, finite-domain, unlocked global state there is a
  synchronization that strictly reduces the inconsistency measure.  An
  inconsistency exhibits two chains disagreeing on a shared asset; at least one
  carries a non-terminal (non-\<open>CONFISCATED\<close>) regulatory state, from which the
  \<open>CONFISCATE\<close> action is always enabled (@{thm [source] confiscate_universal}),
  so a synchronization succeeds and, by @{thm [source] sync_reduces_inconsistency},
  reduces the measure.
\<close>

definition reducing_sync ::
  "global_state \<Rightarrow> (chain_id \<times> reg_action \<times> asset_id) \<Rightarrow> bool" where
  "reducing_sync gs p \<longleftrightarrow> (case p of (src, act, aid) \<Rightarrow>
       (\<exists>gs'. sync src act aid gs = Some gs' \<and> inconsistency_pairs gs' < inconsistency_pairs gs))"

lemma inconsistent_has_reducing_sync:
  assumes fin: "finite_domain gs" and nl: "no_locked_without_reason gs"
    and inc: "\<not> consistent_state gs"
  shows "\<exists>p. reducing_sync gs p"
proof -
  from inc obtain c1 c2 aid0 s1 s2 where
    g1: "get_reg_state gs c1 aid0 = Some s1" and g2: "get_reg_state gs c2 aid0 = Some s2"
    and ne: "s1 \<noteq> s2"
    unfolding consistent_state_def by blast
  have conn1: "c1 \<in> connected_chains gs aid0" using get_reg_state_connected[OF g1] .
  have conn2: "c2 \<in> connected_chains gs aid0" using get_reg_state_connected[OF g2] .
  \<comment> \<open>One of the two disagreeing chains is non-terminal.\<close>
  obtain src ssrc where src_conn: "src \<in> connected_chains gs aid0"
    and src_reg: "get_reg_state gs src aid0 = Some ssrc"
    and src_nonterm: "ssrc \<noteq> CONFISCATED"
  proof (cases "s1 = CONFISCATED")
    case True
    then have "s2 \<noteq> CONFISCATED" using ne by auto
    then show thesis using that conn2 g2 by blast
  next
    case False
    then show thesis using that conn1 g1 by blast
  qed
  \<comment> \<open>\<open>CONFISCATE\<close> is enabled from any non-terminal state, and the asset is unlocked.\<close>
  have ctrans: "reg_transition ssrc CONFISCATE = Some CONFISCATED"
    using confiscate_universal[OF src_nonterm] .
  have notlocked: "\<not> is_locked gs aid0"
    using nl unfolding no_locked_without_reason_def by simp
  obtain gsl where acq: "acquire_lock gs aid0 = Some gsl"
    using lock_acquire_success[OF notlocked] by blast
  have "sync src CONFISCATE aid0 gs
        = Some (release_lock
                  (update_all_chains gsl aid0 CONFISCATED (connected_chains gs aid0)) aid0)"
    unfolding sync_def using src_reg ctrans acq by (simp add: Let_def)
  then obtain gs' where synced: "sync src CONFISCATE aid0 gs = Some gs'" by blast
  have dis: "get_reg_state gs c1 aid0 \<noteq> get_reg_state gs c2 aid0" using g1 g2 ne by simp
  have "inconsistency_pairs gs' < inconsistency_pairs gs"
    using sync_reduces_inconsistency[OF fin synced conn1 conn2 dis] .
  then have "reducing_sync gs (src, CONFISCATE, aid0)"
    unfolding reducing_sync_def using synced by auto
  then show ?thesis by blast
qed


section \<open>Terminal-Faithful Safe Recovery\<close>

text \<open>
  A measure-reducing synchronization alone leaves the realization map two
  degrees of freedom that no recovery procedure should have.  First, it may
  resolve a mere \<^const>\<open>ACTIVE\<close>/\<^const>\<open>FROZEN\<close> disagreement by broadcasting
  \<^const>\<open>CONFISCATED\<close>: an indiscriminate-confiscation implementation would
  refine the model.  Second, in the reverse direction: the broadcast
  overwrites every connected chain without consulting the target chain's own
  transition relation, so it may overwrite a recorded \<^const>\<open>CONFISCATED\<close>
  holding with a non-terminal value, erasing a confiscation.  The predicate
  \<^term>\<open>safe_recovery\<close> closes both: a recovery is safe when it reduces the
  measure \emph{and} uses \<^const>\<open>CONFISCATE\<close> exactly on the assets that
  already carry the terminal state on some chain.  The equivalence is needed
  in both directions: left-to-right forbids fresh confiscations, and
  right-to-left forbids completing an inconsistency on a terminal-bearing
  asset with anything weaker than the terminal value.
\<close>

definition terminal_present :: "global_state \<Rightarrow> asset_id \<Rightarrow> bool" where
  "terminal_present gs aid \<longleftrightarrow> (\<exists>c. get_reg_state gs c aid = Some CONFISCATED)"

definition safe_recovery ::
  "global_state \<Rightarrow> (chain_id \<times> reg_action \<times> asset_id) \<Rightarrow> bool" where
  "safe_recovery gs p \<longleftrightarrow> reducing_sync gs p \<and>
     (case p of (src, act, aid) \<Rightarrow> (act = CONFISCATE) = terminal_present gs aid)"

lemma safe_recovery_reducing:
  "safe_recovery gs p \<Longrightarrow> reducing_sync gs p"
  by (simp add: safe_recovery_def)

text \<open>The only regulatory action whose result is the terminal state is
  \<^const>\<open>CONFISCATE\<close> itself: the transition table admits no other entry to
  \<^const>\<open>CONFISCATED\<close>.\<close>

lemma to_confiscated_only_confiscate:
  "reg_transition s a = Some CONFISCATED \<Longrightarrow> a = CONFISCATE"
  by (cases s; cases a) simp_all

text \<open>From every non-terminal regulatory state some non-\<^const>\<open>CONFISCATE\<close>
  action is enabled; the witnesses are the de-escalation returns and, from
  \<^const>\<open>ACTIVE\<close>, an escalation that is not a confiscation.\<close>

lemma non_terminal_non_confiscate_step:
  assumes "s \<noteq> CONFISCATED"
  shows "\<exists>a s'. a \<noteq> CONFISCATE \<and> reg_transition s a = Some s'"
proof (cases s)
  case ACTIVE
  then have "FREEZE \<noteq> CONFISCATE \<and> reg_transition s FREEZE = Some FROZEN" by simp
  then show ?thesis by blast
next
  case FROZEN
  then have "UNFREEZE \<noteq> CONFISCATE \<and> reg_transition s UNFREEZE = Some ACTIVE" by simp
  then show ?thesis by blast
next
  case SEIZED
  then have "RELEASE \<noteq> CONFISCATE \<and> reg_transition s RELEASE = Some ACTIVE" by simp
  then show ?thesis by blast
next
  case CONFISCATED
  then show ?thesis using assms by contradiction
next
  case RESTRICTED
  then have "UNRESTRICT \<noteq> CONFISCATE \<and> reg_transition s UNRESTRICT = Some ACTIVE" by simp
  then show ?thesis by blast
qed

text \<open>
  Existence of a safe recovery from any inconsistent carrier state.  The
  proof refines @{thm [source] inconsistent_has_reducing_sync} by selecting
  the synchronization action according to the terminal census of the
  inconsistent asset: if the terminal state is already present on some chain,
  the recovery completes it by confiscating from a non-terminal disagreeing
  chain; if it is absent, the recovery synchronizes with a
  non-\<^const>\<open>CONFISCATE\<close> action enabled on a disagreeing chain.  Either way
  the synchronization succeeds and strictly reduces the inconsistency
  measure, and the chosen action satisfies the terminal-faithfulness
  equivalence.
\<close>

lemma inconsistent_has_safe_recovery:
  assumes fin: "finite_domain gs" and nl: "no_locked_without_reason gs"
    and inc: "\<not> consistent_state gs"
  shows "\<exists>p. safe_recovery gs p"
proof -
  from inc obtain c1 c2 aid0 s1 s2 where
    g1: "get_reg_state gs c1 aid0 = Some s1" and g2: "get_reg_state gs c2 aid0 = Some s2"
    and ne: "s1 \<noteq> s2"
    unfolding consistent_state_def by blast
  have conn1: "c1 \<in> connected_chains gs aid0" using get_reg_state_connected[OF g1] .
  have conn2: "c2 \<in> connected_chains gs aid0" using get_reg_state_connected[OF g2] .
  have dis: "get_reg_state gs c1 aid0 \<noteq> get_reg_state gs c2 aid0" using g1 g2 ne by simp
  have notlocked: "\<not> is_locked gs aid0"
    using nl unfolding no_locked_without_reason_def by simp
  obtain gsl where acq: "acquire_lock gs aid0 = Some gsl"
    using lock_acquire_success[OF notlocked] by blast
  show ?thesis
  proof (cases "terminal_present gs aid0")
    case True
    \<comment> \<open>Terminal completion: one of the disagreeing chains is non-terminal,
        and confiscating from it completes the recorded confiscation.\<close>
    obtain src ssrc where src_reg: "get_reg_state gs src aid0 = Some ssrc"
      and src_nonterm: "ssrc \<noteq> CONFISCATED"
    proof (cases "s1 = CONFISCATED")
      case True
      then have "s2 \<noteq> CONFISCATED" using ne by simp
      then show thesis using that g2 by blast
    next
      case False
      then show thesis using that g1 by blast
    qed
    have ctrans: "reg_transition ssrc CONFISCATE = Some CONFISCATED"
      using confiscate_universal[OF src_nonterm] .
    have "sync src CONFISCATE aid0 gs
          = Some (release_lock
                    (update_all_chains gsl aid0 CONFISCATED (connected_chains gs aid0)) aid0)"
      unfolding sync_def using src_reg ctrans acq by (simp add: Let_def)
    then obtain gs' where synced: "sync src CONFISCATE aid0 gs = Some gs'" by blast
    have "inconsistency_pairs gs' < inconsistency_pairs gs"
      using sync_reduces_inconsistency[OF fin synced conn1 conn2 dis] .
    then have "reducing_sync gs (src, CONFISCATE, aid0)"
      unfolding reducing_sync_def using synced by auto
    then have "safe_recovery gs (src, CONFISCATE, aid0)"
      using True by (simp add: safe_recovery_def)
    then show ?thesis by blast
  next
    case False
    \<comment> \<open>No terminal holding: the first disagreeing chain is non-terminal, and
        a non-\<^const>\<open>CONFISCATE\<close> action is enabled there.\<close>
    have s1_nonterm: "s1 \<noteq> CONFISCATED"
      using False g1 unfolding terminal_present_def by blast
    obtain act ns where act_nc: "act \<noteq> CONFISCATE"
      and atrans: "reg_transition s1 act = Some ns"
      using non_terminal_non_confiscate_step[OF s1_nonterm] by blast
    have "sync c1 act aid0 gs
          = Some (release_lock
                    (update_all_chains gsl aid0 ns (connected_chains gs aid0)) aid0)"
      unfolding sync_def using g1 atrans acq by (simp add: Let_def)
    then obtain gs' where synced: "sync c1 act aid0 gs = Some gs'" by blast
    have "inconsistency_pairs gs' < inconsistency_pairs gs"
      using sync_reduces_inconsistency[OF fin synced conn1 conn2 dis] .
    then have "reducing_sync gs (c1, act, aid0)"
      unfolding reducing_sync_def using synced by auto
    then have "safe_recovery gs (c1, act, aid0)"
      using False act_nc by (simp add: safe_recovery_def)
    then show ?thesis by blast
  qed
qed

text \<open>Terminal completion is definitional: on a terminal-bearing asset a safe
  recovery can only be the completing confiscation.\<close>

corollary recovery_terminal_completion:
  assumes "safe_recovery gs (src, act, aid)" and "terminal_present gs aid"
  shows "act = CONFISCATE"
  using assms by (simp add: safe_recovery_def)

text \<open>
  The value a successful synchronization writes onto a connected chain is the
  output of the regulatory transition fired at the source.  This exposes, for
  the safety argument below, the link between the broadcast value and the
  transition table that produced it.
\<close>

lemma sync_connected_value:
  assumes synced: "sync src act aid0 gs = Some gs'"
    and conn: "c \<in> connected_chains gs aid0"
  shows "\<exists>cur new_st. get_reg_state gs src aid0 = Some cur
       \<and> reg_transition cur act = Some new_st
       \<and> get_reg_state gs' c aid0 = Some new_st"
proof -
  from sync_components[OF synced] obtain cur new_st gs_locked where
    cs: "get_reg_state gs src aid0 = Some cur"
    and tr: "reg_transition cur act = Some new_st"
    and lock: "acquire_lock gs aid0 = Some gs_locked"
    and gs': "gs' = release_lock
                 (update_all_chains gs_locked aid0 new_st (connected_chains gs aid0)) aid0"
    by blast
  have lc: "gs_chains gs_locked = gs_chains gs" using acquire_lock_chains[OF lock] .
  from conn have "asset_exists gs c aid0" by (simp add: connected_chains_def)
  then obtain ast where "get_asset_state gs c aid0 = Some ast"
    unfolding asset_exists_def by auto
  then have astl: "get_asset_state gs_locked c aid0 = Some ast"
    unfolding get_asset_state_def using lc by simp
  have "get_reg_state
          (update_all_chains gs_locked aid0 new_st (connected_chains gs aid0)) c aid0
        = Some new_st"
    using update_all_chains_reg_state[OF conn astl] .
  then have "get_reg_state gs' c aid0 = Some new_st"
    unfolding gs' by (simp add: release_lock_reg_state)
  with cs tr show ?thesis by blast
qed

text \<open>
  The single-step safety payload of the terminal-faithfulness equivalence: a
  safe-recovery synchronization never makes the terminal state appear on an
  asset that did not already carry it.  If the synchronized value were
  \<^const>\<open>CONFISCATED\<close>, then by @{thm [source] to_confiscated_only_confiscate}
  the action was \<^const>\<open>CONFISCATE\<close>, so by the equivalence the asset already
  carried the terminal state --- a contradiction.
\<close>

lemma safe_recovery_sync_no_fresh_terminal:
  assumes sr: "safe_recovery gs (src, act, aid0)"
    and synced: "sync src act aid0 gs = Some gs'"
    and nt: "\<not> terminal_present gs aid"
  shows "\<not> terminal_present gs' aid"
proof
  assume "terminal_present gs' aid"
  then obtain c where c: "get_reg_state gs' c aid = Some CONFISCATED"
    unfolding terminal_present_def by blast
  show False
  proof (cases "aid = aid0")
    case False
    then have "get_reg_state gs c aid = Some CONFISCATED"
      using c sync_reg_other_asset[OF synced False] by simp
    then show False using nt unfolding terminal_present_def by blast
  next
    case True
    have "c \<in> connected_chains gs' aid0"
      using c True get_reg_state_connected by blast
    then have conn: "c \<in> connected_chains gs aid0"
      using sync_connected_chains_preserved[OF synced] by simp
    obtain cur new_st where
      tr: "reg_transition cur act = Some new_st"
      and val: "get_reg_state gs' c aid0 = Some new_st"
      using sync_connected_value[OF synced conn] by blast
    have "new_st = CONFISCATED" using c val True by simp
    then have "act = CONFISCATE" using to_confiscated_only_confiscate tr by blast
    then have "terminal_present gs aid0"
      using sr by (simp add: safe_recovery_def)
    then show False using nt True by simp
  qed
qed

text \<open>
  Machine-checked regression witnesses for the two excluded behaviours.  The
  two-chain builder places the given regulatory values on chains \<open>0\<close> and
  \<^term>\<open>Suc 0\<close> of asset \<open>0\<close>; both witnesses evaluate by unfolding.
\<close>

definition mixed_pair_state :: "reg_state \<Rightarrow> reg_state \<Rightarrow> global_state" where
  "mixed_pair_state v0 v1 =
     \<lparr> gs_chains = (\<lambda>c a. if a = 0 \<and> c = 0
                          then Some \<lparr> as_asset_id = 0, as_reg_state = v0,
                                      as_owner = 0, as_locked = False \<rparr>
                          else if a = 0 \<and> c = Suc 0
                          then Some \<lparr> as_asset_id = 0, as_reg_state = v1,
                                      as_owner = 0, as_locked = False \<rparr>
                          else None),
       gs_locks = (\<lambda>a. False) \<rparr>"

lemma mixed_pair_get_reg:
  "get_reg_state (mixed_pair_state v0 v1) c a =
     (if a = 0 \<and> c = 0 then Some v0 else if a = 0 \<and> c = Suc 0 then Some v1 else None)"
  by (simp add: mixed_pair_state_def get_reg_state_def get_asset_state_def)

text \<open>Indiscriminate confiscation is excluded: on a plain
  \<^const>\<open>ACTIVE\<close>/\<^const>\<open>FROZEN\<close> disagreement with no terminal holding, no
  \<^const>\<open>CONFISCATE\<close> propagation is a safe recovery, from any source chain.\<close>

lemma blind_confiscate_excluded:
  "\<not> terminal_present (mixed_pair_state ACTIVE FROZEN) 0"
  "\<not> safe_recovery (mixed_pair_state ACTIVE FROZEN) (c, CONFISCATE, 0)"
  by (auto simp: terminal_present_def safe_recovery_def mixed_pair_get_reg split: if_splits)

text \<open>Confiscation erasure is excluded: on a \<^const>\<open>CONFISCATED\<close>/\<^const>\<open>ACTIVE\<close>
  disagreement the terminal state is present, so no non-\<^const>\<open>CONFISCATE\<close>
  broadcast is a safe recovery --- a recorded confiscation cannot be revived
  by overwriting it with a non-terminal value.\<close>

lemma terminal_overwrite_excluded:
  "terminal_present (mixed_pair_state CONFISCATED ACTIVE) 0"
  "act \<noteq> CONFISCATE \<Longrightarrow> \<not> safe_recovery (mixed_pair_state CONFISCATED ACTIVE) (c, act, 0)"
proof -
  have "get_reg_state (mixed_pair_state CONFISCATED ACTIVE) 0 0 = Some CONFISCATED"
    by (simp add: mixed_pair_get_reg)
  then show "terminal_present (mixed_pair_state CONFISCATED ACTIVE) 0"
    unfolding terminal_present_def by blast
  then show "act \<noteq> CONFISCATE \<Longrightarrow> \<not> safe_recovery (mixed_pair_state CONFISCATED ACTIVE) (c, act, 0)"
    by (simp add: safe_recovery_def)
qed


section \<open>The Oraclizer as a Converging Composition\<close>

text \<open>
  We package the oraclizer synchronization protocol as the data of a
  @{locale converging_composition}: the carrier is the set of finite-domain,
  unlocked global states; the operations are synchronization triples; the
  invariant is cross-chain consistency; the progress measure is the
  inconsistency count; and the realization map picks, in any inconsistent
  state, a terminal-faithful safe recovery --- a synchronization that reduces
  the measure and uses \<^const>\<open>CONFISCATE\<close> exactly on terminal-bearing assets
  (existence guaranteed by @{thm [source] inconsistent_has_safe_recovery}).
\<close>

definition oss_carrier :: "global_state set" where
  "oss_carrier = {gs. finite_domain gs \<and> no_locked_without_reason gs}"

definition oss_step ::
  "global_state \<Rightarrow> (chain_id \<times> reg_action \<times> asset_id) \<Rightarrow> global_state option" where
  "oss_step gs p = (case p of (src, act, aid) \<Rightarrow> sync src act aid gs)"

definition oss_ops :: "(chain_id \<times> reg_action \<times> asset_id) set" where
  "oss_ops = UNIV"

definition oss_guard ::
  "global_state \<Rightarrow> (chain_id \<times> reg_action \<times> asset_id) \<Rightarrow> bool" where
  "oss_guard gs p = (case p of (src, act, aid) \<Rightarrow> (\<exists>gs'. sync src act aid gs = Some gs'))"

definition oss_realize ::
  "node_info \<Rightarrow> global_state \<Rightarrow> (chain_id \<times> reg_action \<times> asset_id) option" where
  "oss_realize ev gs =
     (if consistent_state gs then None else Some (SOME p. safe_recovery gs p))"

lemma oss_step_closed:
  assumes "gs \<in> oss_carrier" and "oss_step gs p = Some gs'"
  shows "gs' \<in> oss_carrier"
proof -
  obtain src act aid where p: "p = (src, act, aid)" by (cases p)
  with assms(2) have synced: "sync src act aid gs = Some gs'" by (simp add: oss_step_def)
  from assms(1) have "finite_domain gs" and "no_locked_without_reason gs"
    by (simp_all add: oss_carrier_def)
  then have "finite_domain gs'" and "no_locked_without_reason gs'"
    using sync_preserves_finite_domain[OF _ synced] sync_preserves_unlocked[OF _ synced] by auto
  then show ?thesis by (simp add: oss_carrier_def)
qed

lemma oss_guarded_preservation:
  assumes carr: "gs \<in> oss_carrier" and cons: "consistent_state gs"
    and synced: "oss_step gs p = Some gs'"
  shows "consistent_state gs'"
proof -
  obtain src act aid where p: "p = (src, act, aid)" by (cases p)
  with synced have s: "sync src act aid gs = Some gs'" by (simp add: oss_step_def)
  from carr have nl: "no_locked_without_reason gs" and fd: "finite_domain gs"
    by (simp_all add: oss_carrier_def)
  have valid: "valid_state gs" using cons nl by (simp add: valid_state_def)
  from sync_components[OF s] obtain current_st new_st gs_locked where
    cur: "get_reg_state gs src aid = Some current_st"
    and tr: "reg_transition current_st act = Some new_st" by blast
  have ex: "asset_exists gs src aid"
    using cur unfolding asset_exists_def get_reg_state_def get_asset_state_def
    by (auto split: option.splits)
  have finc: "finite (connected_chains gs aid)" using connected_chains_finite[OF fd] .
  show ?thesis
    using sync_preserves_consistent_state[OF valid ex cur tr s finc] .
qed

lemma oss_realize_discharges:
  assumes carr: "gs \<in> oss_carrier" and r: "oss_realize ev gs = Some opn"
  shows "opn \<in> oss_ops \<and> oss_guard gs opn"
proof -
  from r have ninc: "\<not> consistent_state gs" and opn: "opn = (SOME p. safe_recovery gs p)"
    by (auto simp: oss_realize_def split: if_splits)
  from carr have fd: "finite_domain gs" and nl: "no_locked_without_reason gs"
    by (simp_all add: oss_carrier_def)
  have "\<exists>p. safe_recovery gs p" using inconsistent_has_safe_recovery[OF fd nl ninc] .
  then have "safe_recovery gs opn" using opn by (metis someI_ex)
  then have "reducing_sync gs opn" by (rule safe_recovery_reducing)
  then obtain src act aid gs' where "opn = (src, act, aid)" and "sync src act aid gs = Some gs'"
    unfolding reducing_sync_def by (auto split: prod.splits)
  then have "oss_guard gs opn" by (auto simp: oss_guard_def)
  then show ?thesis by (simp add: oss_ops_def)
qed

lemma oss_realize_progresses:
  assumes "consistent_state gs" and "oss_realize ev gs = Some opn"
  shows "\<exists>gs'. oss_step gs opn = Some gs' \<and> consistent_state gs'"
  using assms by (simp add: oss_realize_def)

lemma oss_measure_zero_inv:
  assumes "gs \<in> oss_carrier" and "inconsistency_pairs gs = 0"
  shows "consistent_state gs"
proof -
  from assms(1) have "finite_domain gs" by (simp add: oss_carrier_def)
  then show ?thesis using assms(2) inconsistency_pairs_zero_iff_consistent by blast
qed

lemma oss_discharge_progresses:
  assumes carr: "gs \<in> oss_carrier" and ninc: "\<not> consistent_state gs"
  shows "\<exists>opn gs'. oss_realize ev gs = Some opn \<and> oss_step gs opn = Some gs'
                   \<and> inconsistency_pairs gs' < inconsistency_pairs gs"
proof -
  from carr have fd: "finite_domain gs" and nl: "no_locked_without_reason gs"
    by (simp_all add: oss_carrier_def)
  have ex: "\<exists>p. safe_recovery gs p" using inconsistent_has_safe_recovery[OF fd nl ninc] .
  define opn where "opn = (SOME p. safe_recovery gs p)"
  have sr: "safe_recovery gs opn" unfolding opn_def using ex by (rule someI_ex)
  have rs: "reducing_sync gs opn" using sr by (rule safe_recovery_reducing)
  have realize: "oss_realize ev gs = Some opn"
    using ninc unfolding oss_realize_def opn_def by simp
  from rs obtain src act aid gs' where
    p: "opn = (src, act, aid)" and s: "sync src act aid gs = Some gs'"
    and dec: "inconsistency_pairs gs' < inconsistency_pairs gs"
    unfolding reducing_sync_def by (auto split: prod.splits)
  have "oss_step gs opn = Some gs'" using p s by (simp add: oss_step_def)
  with realize dec show ?thesis by blast
qed


section \<open>Guarded Bounded Convergence for the Oraclizer\<close>

text \<open>
  Inside the Byzantine fault-tolerant D-quencer with fair leader election, the
  oraclizer data above forms a @{locale converging_composition}: the honest
  leader within every fairness window discharges a measure-reducing
  synchronization.  The fairness assumption is exactly the \<open>fair_leader\<close>
  assumption of @{locale dquencer_liveness} and the window positivity is its
  \<open>fairness_positive\<close> assumption (inherited from @{locale dquencer_system}).
\<close>

text \<open>
  The fairness assumption of @{locale dquencer_liveness} is satisfiable in
  every D-quencer system: the BFT threshold yields an honest node
  (@{thm [source] dquencer_system.honest_nonempty}), and the constant
  schedule on that node meets every fairness window.  This grounds the
  assume-guarantee abstraction: the fair-leader hypothesis is the
  deterministic residue of VRF-based election, and the system's own
  threshold already supplies a witness schedule, so the hypothesis is
  satisfiable rather than merely plausible.
\<close>

context dquencer_system
begin

lemma fair_schedule_exists:
  "\<exists>sched :: nat \<Rightarrow> node_info.
     \<forall>epoch. \<exists>e. epoch \<le> e \<and> e < epoch + fairness_bound \<and>
                 ni_behavior (sched e) = Honest"
proof -
  obtain h where "h \<in> honest_nodes nodes"
    using honest_nonempty by blast
  then have hb: "ni_behavior h = Honest" by (simp add: honest_nodes_def)
  define sched :: "nat \<Rightarrow> node_info" where "sched = (\<lambda>_. h)"
  have body: "\<forall>epoch. \<exists>e. epoch \<le> e \<and> e < epoch + fairness_bound
               \<and> ni_behavior (sched e) = Honest"
  proof
    fix epoch :: nat
    have "epoch \<le> epoch \<and> epoch < epoch + fairness_bound
          \<and> ni_behavior (sched epoch) = Honest"
      using fairness_positive hb by (simp add: sched_def)
    then show "\<exists>e. epoch \<le> e \<and> e < epoch + fairness_bound
                 \<and> ni_behavior (sched e) = Honest"
      by blast
  qed
  show ?thesis
    by (rule exI[where P = "\<lambda>s :: nat \<Rightarrow> node_info.
                              \<forall>epoch. \<exists>e. epoch \<le> e \<and> e < epoch + fairness_bound
                                \<and> ni_behavior (s e) = Honest"
                 and x = sched, OF body])
qed

end

context dquencer_liveness
begin

interpretation oss: converging_composition
  oss_carrier oss_step oss_ops consistent_state oss_guard
  leader_schedule "\<lambda>n. ni_behavior n = Honest" fairness_bound oss_realize inconsistency_pairs
proof unfold_locales
  show "\<And>s opn s'. s \<in> oss_carrier \<Longrightarrow> opn \<in> oss_ops \<Longrightarrow> oss_step s opn = Some s'
          \<Longrightarrow> s' \<in> oss_carrier"
    using oss_step_closed by blast
next
  show "\<And>s opn s'. s \<in> oss_carrier \<Longrightarrow> opn \<in> oss_ops \<Longrightarrow> consistent_state s
          \<Longrightarrow> oss_guard s opn \<Longrightarrow> oss_step s opn = Some s' \<Longrightarrow> consistent_state s'"
    using oss_guarded_preservation by blast
next
  show "0 < fairness_bound" using fairness_positive .
next
  show "\<forall>t. \<exists>t'. t \<le> t' \<and> t' < t + fairness_bound \<and> ni_behavior (leader_schedule t') = Honest"
    using fair_leader .
next
  show "\<And>s ev opn. s \<in> oss_carrier \<Longrightarrow> ni_behavior ev = Honest \<Longrightarrow> oss_realize ev s = Some opn
          \<Longrightarrow> opn \<in> oss_ops \<and> oss_guard s opn"
    using oss_realize_discharges by blast
next
  show "\<And>s ev opn. s \<in> oss_carrier \<Longrightarrow> consistent_state s \<Longrightarrow> ni_behavior ev = Honest
          \<Longrightarrow> oss_realize ev s = Some opn \<Longrightarrow> \<exists>s'. oss_step s opn = Some s' \<and> consistent_state s'"
    using oss_realize_progresses by blast
next
  show "\<And>s. s \<in> oss_carrier \<Longrightarrow> inconsistency_pairs s = 0 \<Longrightarrow> consistent_state s"
    using oss_measure_zero_inv by blast
next
  show "\<And>s ev. s \<in> oss_carrier \<Longrightarrow> \<not> consistent_state s \<Longrightarrow> ni_behavior ev = Honest
          \<Longrightarrow> \<exists>opn s'. oss_realize ev s = Some opn \<and> oss_step s opn = Some s'
                      \<and> inconsistency_pairs s' < inconsistency_pairs s"
    using oss_discharge_progresses by blast
qed

text \<open>
  The headline of revision~3's convergence layer.  From an \emph{arbitrary}
  finite-domain, unlocked global state --- in particular with \emph{no}
  assumption that the cross-chain consistency invariant holds initially --- the
  oraclizer reaches, within @{term "inconsistency_pairs gs\<^sub>0 * fairness_bound"}
  evolution steps, a state that is valid (consistent and unlocked).  Contrast
  @{thm [source] combined_safety_liveness}, which assumes @{term "valid_state gs"}:
  revision~3 upgrades conditional safety to unconditional bounded convergence.
\<close>

theorem oraclizer_guarded_bounded_convergence:
  assumes fin: "finite_domain gs\<^sub>0"
    and unlocked: "no_locked_without_reason gs\<^sub>0"
  shows "\<exists>t \<le> oss.convergence_bound gs\<^sub>0. \<exists>gs\<^sub>t.
           oss.evolves_to gs\<^sub>0 t gs\<^sub>t \<and> valid_state gs\<^sub>t"
proof -
  have carr: "gs\<^sub>0 \<in> oss_carrier" using fin unlocked by (simp add: oss_carrier_def)
  obtain t gs\<^sub>t where tb: "t \<le> oss.convergence_bound gs\<^sub>0"
    and ev: "oss.evolves_to gs\<^sub>0 t gs\<^sub>t" and cons: "consistent_state gs\<^sub>t"
    using oss.bounded_convergence_from_arbitrary[OF carr] by blast
  \<comment> \<open>The reached state remains in the carrier, hence is unlocked, hence valid.\<close>
  have "gs\<^sub>t = oss.run_from 0 gs\<^sub>0 t"
    using ev by (simp add: oss.evolves_to_def oss.run_def)
  then have "gs\<^sub>t \<in> oss_carrier" using oss.run_from_carrier[OF carr] by simp
  then have "no_locked_without_reason gs\<^sub>t" by (simp add: oss_carrier_def)
  then have "valid_state gs\<^sub>t" using cons by (simp add: valid_state_def)
  with tb ev show ?thesis by blast
qed

text \<open>
  Terminal faithfulness along whole recovery runs.  Every evolution step
  either stutters or applies a realized safe recovery, and a safe recovery
  never confiscates an asset that carried no terminal holding
  (@{thm [source] safe_recovery_sync_no_fresh_terminal}); by induction the
  guarantee extends to the entire trajectory: an asset that starts with no
  recorded confiscation never acquires one, no matter how the run is
  scheduled.  Together with @{thm [source] recovery_terminal_completion} ---
  on a terminal-bearing asset a safe recovery can only complete the
  confiscation --- this pins the recovery layer to the two behaviours the
  regulatory semantics admits, excluding both indiscriminate confiscation
  and confiscation erasure.
\<close>

lemma oss_evolve_step_no_fresh_terminal:
  assumes carr: "gs \<in> oss_carrier"
    and nt: "\<not> terminal_present gs aid"
  shows "\<not> terminal_present (oss.evolve_step t gs) aid"
proof (cases "ni_behavior (leader_schedule t) = Honest")
  case False
  then show ?thesis using nt by (simp add: oss.evolve_step_def)
next
  case True
  show ?thesis
  proof (cases "oss_realize (leader_schedule t) gs")
    case None
    with True show ?thesis using nt by (simp add: oss.evolve_step_def)
  next
    case (Some opn)
    note r = this
    show ?thesis
    proof (cases "oss_step gs opn")
      case None
      with True r show ?thesis using nt by (simp add: oss.evolve_step_def)
    next
      case (Some gs')
      note st = this
      from r have ninc: "\<not> consistent_state gs"
        and opn_eq: "opn = (SOME p. safe_recovery gs p)"
        by (auto simp: oss_realize_def split: if_splits)
      from carr have fd: "finite_domain gs" and nl: "no_locked_without_reason gs"
        by (simp_all add: oss_carrier_def)
      have "\<exists>p. safe_recovery gs p" using inconsistent_has_safe_recovery[OF fd nl ninc] .
      then have sr: "safe_recovery gs opn" using opn_eq by (metis someI_ex)
      obtain src act aid0 where p: "opn = (src, act, aid0)" by (cases opn)
      have synced: "sync src act aid0 gs = Some gs'" using st p by (simp add: oss_step_def)
      have "\<not> terminal_present gs' aid"
        using safe_recovery_sync_no_fresh_terminal[OF sr[unfolded p] synced nt] .
      with True r st show ?thesis by (simp add: oss.evolve_step_def)
    qed
  qed
qed

lemma oss_run_from_no_fresh_terminal:
  assumes carr: "gs\<^sub>0 \<in> oss_carrier"
    and nt: "\<not> terminal_present gs\<^sub>0 aid"
  shows "\<not> terminal_present (oss.run_from k gs\<^sub>0 n) aid"
proof (induction n)
  case 0
  show ?case using nt by simp
next
  case (Suc n)
  have c: "oss.run_from k gs\<^sub>0 n \<in> oss_carrier" using oss.run_from_carrier[OF carr] .
  show ?case using oss_evolve_step_no_fresh_terminal[OF c Suc.IH] by simp
qed

theorem recovery_no_fresh_terminal:
  assumes carr: "gs\<^sub>0 \<in> oss_carrier"
    and nt: "\<not> terminal_present gs\<^sub>0 aid"
    and ev: "oss.evolves_to gs\<^sub>0 t gs\<^sub>t"
  shows "\<not> terminal_present gs\<^sub>t aid"
proof -
  have "gs\<^sub>t = oss.run_from 0 gs\<^sub>0 t"
    using ev by (simp add: oss.evolves_to_def oss.run_def)
  then show ?thesis using oss_run_from_no_fresh_terminal[OF carr nt] by simp
qed

end


section \<open>Global Model Witnesses for the Liveness Hosts\<close>

text \<open>
  The liveness interpretations above live inside @{locale dquencer_liveness},
  so they establish the consistency of their conclusions only relative to the
  host locale's assumptions.  The interpretations below discharge those
  assumptions globally, with no ambient hypotheses: a single-honest-node
  system with zero Byzantine budget, unit lock timeout and unit fairness
  window, scheduled constantly on its one node, with no pending requests.
  Every assumption of @{locale dquencer_system} and @{locale dquencer_liveness}
  holds outright (the BFT threshold reads \<open>1 \<ge> 3 \<cdot> 0 + 1\<close>, the Byzantine
  census is empty, and the constant schedule meets every unit fairness
  window), so the assumption sets of the liveness hosts are consistent
  absolutely, not merely relative to a hypothetical deployment.
\<close>

definition singleton_node :: node_info where
  "singleton_node = \<lparr> ni_id = 0, ni_behavior = Honest \<rparr>"

lemma singleton_fair_leader:
  "\<forall>epoch. \<exists>e. epoch \<le> e \<and> e < epoch + (1::nat)
             \<and> ni_behavior ((\<lambda>_. singleton_node) e) = Honest"
proof
  fix epoch :: nat
  have "epoch \<le> epoch \<and> epoch < epoch + 1
        \<and> ni_behavior ((\<lambda>_. singleton_node) epoch) = Honest"
    by (simp add: singleton_node_def)
  then show "\<exists>e. epoch \<le> e \<and> e < epoch + 1
               \<and> ni_behavior ((\<lambda>_. singleton_node) e) = Honest"
    by blast
qed

interpretation singleton_dq: dquencer_liveness
  "{singleton_node}" 0 1 1 0 0 "\<lambda>_. singleton_node" "\<lambda>_. 0"
  by unfold_locales
     (auto simp: byzantine_nodes_def singleton_node_def intro: singleton_fair_leader)

text \<open>
  The priority sublocale receives the analogous witness: the one-message set
  over the same singleton system.  The well-formedness bounds hold with both
  maxima at \<open>0\<close>, and priority-key distinctness on a one-element set is
  immediate.
\<close>

definition singleton_msg :: dq_message where
  "singleton_msg =
     \<lparr> msg_action = FREEZE, msg_asset_id = 0, msg_authority = 0, msg_timestamp = 0,
       msg_source = 0, msg_targets = {}, dqm_authority_level = National,
       dqm_source_node = 0 \<rparr>"

interpretation singleton_dq_priority: dquencer_priority_concrete
  "{singleton_node}" 0 1 1 0 0 "{singleton_msg}"
  by unfold_locales
     (auto simp: byzantine_nodes_def singleton_node_def singleton_msg_def
           intro: singleton_fair_leader)

end
