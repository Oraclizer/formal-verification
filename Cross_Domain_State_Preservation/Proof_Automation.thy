(*
  Title:      Cross_Domain_State_Preservation/Proof_Automation.thy
  Author:     Jinwook Kim (Jay) <jay@oraclizer.io>
  Maintainer: Jinwook Kim (Jay) <jay@oraclizer.io>
  License:    BSD

  Cross-Domain State Preservation Functor — Proof Automation

  Reusable Eisbach discharge methods for the instance obligations of the
  generic locales of State_Preservation.thy.  The methods are part of the
  entry's reusable surface: an importer instantiating state_machine or
  state_preservation on a finite, enumerated domain declares the defining
  equations of its sets and transition functions into the named theorem
  collections below and discharges whole instances with one method
  invocation.  The theory depends only on the generic locale layer and on
  Eisbach; it carries no application vocabulary.
*)

theory Proof_Automation
  imports State_Preservation "HOL-Eisbach.Eisbach"
begin

section \<open>Discharge Methods for Instance Obligations\<close>

text \<open>
  Two named theorem collections feed the methods.  \<open>discharge_simps\<close> holds
  the equational content of a concrete instance: defining equations of the
  state/action/terminal sets, finiteness facts, terminal-absorption
  equations, and naturality equations of structured state maps (conditional
  rewrites whose premises the simplifier discharges from the goal's
  assumptions).  \<open>discharge_intros\<close> holds introduction rules whose extra
  premises must be instantiated by unification against the goal's
  assumptions --- typically closure lemmas, whose condition variables do not
  all occur in the conclusion and which are therefore out of reach of
  conditional rewriting.
\<close>

named_theorems discharge_simps
  \<open>defining equations and conditional rewrites consumed by the discharge methods\<close>

named_theorems discharge_intros
  \<open>introduction rules consumed by the discharge methods\<close>

named_theorems discharge_dels
  \<open>default simplification rules suppressed by the discharge methods ---
   typically the defining equations of structured state maps introduced with
   \<open>fun\<close>, whose eager unfolding would destroy the redexes that the
   conditional naturality rewrites of \<open>discharge_simps\<close> match on\<close>

text \<open>
  The common skeleton: unfold the locale predicate into its atomic
  obligations (\<open>unfold_locales\<close> also discharges sub-locale obligations
  already available from registered interpretations), then close each
  remaining obligation by simplifier-driven exhaustive case analysis ---
  membership of an action in an enumerated set splits into finitely many
  cases, after which the defining equations of the transition functions
  decide the goal, with \<open>option\<close>/\<open>if\<close> splits for partially defined
  transitions.

  \<open>discharge_state_machine\<close> is the entry point for @{locale state_machine}
  obligations (finiteness, terminal containment, terminal absorption,
  closure, domain);
  \<open>discharge_preservation\<close> is the entry point for
  @{locale state_preservation} obligations, whose unfolding contains the two
  sub-machines' obligations together with the morphism axioms
  (well-definedness, terminal preservation, and the two naturality
  directions).
\<close>

method discharge_state_machine declares discharge_simps discharge_intros discharge_dels =
  (unfold_locales;
   (auto simp add: discharge_simps simp del: discharge_dels
         intro: discharge_intros
         split: option.splits if_splits))

method discharge_preservation declares discharge_simps discharge_intros discharge_dels =
  (unfold_locales;
   (auto simp add: discharge_simps simp del: discharge_dels
         intro: discharge_intros
         split: option.splits if_splits))

text \<open>
  The two entry points share their skeleton deliberately: a
  @{locale state_preservation} goal unfolds into the union of the two
  obligation families, so the preservation method must subsume the machine
  method.  Keeping both names separates the reusable surface by intent ---
  an importer discharging a bare machine instance is not invited to reach
  for the morphism-level method --- and lets the two evolve independently
  if the obligation families diverge in a future revision.
\<close>

end
