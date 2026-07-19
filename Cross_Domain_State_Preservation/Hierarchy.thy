(*
  Title:      Cross_Domain_State_Preservation/Hierarchy.thy
  Author:     Jinwook Kim (Jay) <jay@oraclizer.io>
  Maintainer: Jinwook Kim (Jay) <jay@oraclizer.io>
  License:    BSD

  Cross-Domain State Preservation Functor — Sync Degree Hierarchy

  This theory layers a degree stratification on top of the functorial
  cross-domain construction of Functor_Laws.thy, formalising the
  monotonicity of the synchronization degree hierarchy.

  Each synchronization degree k models a coupling breadth: a degree-k system
  keeps chains 0..k of an asset in lockstep around a hub chain (chain 0).
  This index does not formalize the product's S0--S3 operational meanings,
  such as directional observation, bidirectional causal execution, atomic
  binding, or mutual rollback; connecting those meanings to F k requires a
  separate refinement.
  This yields a tower of transition functors F 0, F 1, F 2, F 3, ... with the
  weaker functor obtained from the stronger one by forgetting the top coupled
  chain.  The word-level construction fixes one asset; for each such asset,
  F k is a genuine functor on the free category of regulatory action words:
  it preserves the identity word and word concatenation
  (deg_run_Nil, deg_run_append), and --- the non-degenerate content --- its
  action on a word collapses to the composite regulatory transition broadcast
  once (deg_run_collapse, via the broadcast-overwrite and hub-tracking lemmas),
  so it is not a vacuous fold over an index set.  The forgetful map
  degree_forget is a natural transformation between consecutive degrees: its
  single-step naturality square commutes (degree_natural_transformation) and,
  by induction over action words, the naturality holds on the corresponding
  fixed-asset action-word category (degree_forget_natural_run), not merely on
  generators.  Natural
  transformations are closed under composition (nt_compose / nt_vertical_compose),
  so the whole ladder F (k+2) => F (k+1) => F k is structurally coherent, not
  merely a point-to-point collection of forgetful maps.  This functor-tower
  layer, with genuine functors and natural transformations between them, is the
  region of the design that Lochbihler and Maric's ADS_Functor does not develop:
  ADS_Functor establishes closure of functors under composition; to our
  knowledge it does not build a hierarchy of functors with natural
  transformations between them.

  Degree demotion is information-discarding: degree_forget yields a blinding
  refinement in the exact sense of the glue layer of Functor_Laws.thy
  (state_refines, the state-level reading of the ADS blinding order bo).  The
  lemma degree_forget_refines makes this load-bearing connection explicit,
  so the hierarchy is built on the functor laws rather than beside them.

  The second part proves the monotonicity payload, parametrically in an
  arbitrary degree assignment (the assignment is operational data, fixed in
  an anonymous context): reduction containment of the degree classes
  (reduction_containment), and a genuinely one-directional degree monotonicity
  --- over-provisioning reconciles all of an asset's required chains
  (over_provisioning_guarantees) while under-provisioning carries no such
  guarantee (no_downward_safety); a companion theorem
  (over_provisioning_reconciles) shows the degree hypothesis load-bearing
  from an arbitrary hub-defined state.  Validity preservation itself is
  degree-free (processing_preserves_validity); the auxiliary lemma
  hierarchy_monotonicity is its degree-free alias and carries no
  provisioning hypothesis.  The timestamp-order degree boundary
  that separates degree 1 from degree 2 (boundary_well_defined) is grounded in
  a strict timestamp order.  A concrete example assignment witnesses
  non-vacuity, and a static-promotion corollary (static_promotion_safety)
  records that the over-provisioning guarantee transfers verbatim to any
  re-assignment within the system's capability.
*)

theory Hierarchy
  imports Functor_Laws
begin

section \<open>Sync Degree Stratification\<close>

text \<open>
  A degree-\<open>k\<close> broadcast drives every chain \<open>c \<le> k\<close> that currently holds the
  asset \<open>aid\<close> to the regulatory value \<open>v\<close>, leaving every other chain and every
  other asset untouched.  It is the state-level effect of synchronizing the
  asset across the chains coupled at degree \<open>k\<close>.
\<close>

definition broadcast_le ::
  "nat \<Rightarrow> asset_id \<Rightarrow> reg_state \<Rightarrow> global_state \<Rightarrow> global_state" where
  "broadcast_le k aid v gs =
     gs\<lparr> gs_chains :=
           (\<lambda>c. if c \<le> k
                then (\<lambda>aid'. if aid' = aid
                             then map_option (\<lambda>ast. ast\<lparr> as_reg_state := v \<rparr>)
                                             (gs_chains gs c aid)
                             else gs_chains gs c aid')
                else gs_chains gs c) \<rparr>"

lemma broadcast_le_locks [simp]:
  "gs_locks (broadcast_le k aid v gs) = gs_locks gs"
  by (simp add: broadcast_le_def)

lemma broadcast_le_exists [simp]:
  "asset_exists (broadcast_le k aid v gs) c aid' = asset_exists gs c aid'"
  by (auto simp: broadcast_le_def asset_exists_def get_asset_state_def
           split: option.splits)

lemma broadcast_le_reg_other_asset:
  "aid' \<noteq> aid \<Longrightarrow>
     get_reg_state (broadcast_le k aid v gs) c aid' = get_reg_state gs c aid'"
  by (simp add: broadcast_le_def get_reg_state_def get_asset_state_def)

lemma broadcast_le_reg_out:
  "\<not> c \<le> k \<Longrightarrow>
     get_reg_state (broadcast_le k aid v gs) c aid' = get_reg_state gs c aid'"
  by (simp add: broadcast_le_def get_reg_state_def get_asset_state_def)

lemma broadcast_le_reg_in:
  "c \<le> k \<Longrightarrow>
     get_reg_state (broadcast_le k aid v gs) c aid =
       (case get_reg_state gs c aid of None \<Rightarrow> None | Some _ \<Rightarrow> Some v)"
  by (simp add: broadcast_le_def get_reg_state_def get_asset_state_def
           map_option_case split: option.splits)

text \<open>Pointwise reading of the chain map after a broadcast: a clean rewrite that
  avoids unfolding the raw record update inside nested terms.\<close>

lemma broadcast_le_chains:
  "gs_chains (broadcast_le k aid v gs) c =
     (if c \<le> k
      then (\<lambda>aid'. if aid' = aid
                   then map_option (\<lambda>ast. ast\<lparr> as_reg_state := v \<rparr>) (gs_chains gs c aid)
                   else gs_chains gs c aid')
      else gs_chains gs c)"
  by (simp add: broadcast_le_def)

text \<open>
  Degree demotion: \<^term>\<open>degree_forget j\<close> drops the holdings of chain \<open>j\<close>,
  the top chain coupled one degree up.  It keeps locks and every other chain.
\<close>

definition degree_forget :: "nat \<Rightarrow> global_state \<Rightarrow> global_state" where
  "degree_forget j gs = gs\<lparr> gs_chains := (gs_chains gs)(j := (\<lambda>aid. None)) \<rparr>"

lemma degree_forget_locks [simp]:
  "gs_locks (degree_forget j gs) = gs_locks gs"
  by (simp add: degree_forget_def)

lemma degree_forget_reg_eq:
  "c \<noteq> j \<Longrightarrow> get_reg_state (degree_forget j gs) c aid = get_reg_state gs c aid"
  by (simp add: degree_forget_def get_reg_state_def get_asset_state_def)

lemma degree_forget_exists:
  "asset_exists (degree_forget j gs) c aid =
     (c \<noteq> j \<and> asset_exists gs c aid)"
  by (simp add: degree_forget_def asset_exists_def get_asset_state_def)

lemma degree_forget_chains:
  "gs_chains (degree_forget j gs) c =
     (if c = j then (\<lambda>aid. None) else gs_chains gs c)"
  by (simp add: degree_forget_def)

text \<open>
  Demotion forgets, never invents: \<^term>\<open>degree_forget j gs\<close> is a blinding
  refinement of \<open>gs\<close> in the sense of the glue layer of \<^theory>\<open>Cross_Domain_State_Preservation.Functor_Laws\<close>.
  Every chain still known after demotion carries exactly the regulatory state
  it had before.  This is the state-level reading of the ADS blinding order
  \<^term>\<open>bo\<close> (\<^term>\<open>state_refines\<close>): degree demotion lands inside the partial-view
  preorder on which the authenticated layer is built, so the hierarchy sits on
  top of the functor laws rather than beside them.
\<close>

lemma degree_forget_refines: "state_refines (degree_forget j gs) gs"
  unfolding state_refines_def
proof (intro allI impI)
  fix aid c
  assume "c \<in> connected_chains (degree_forget j gs) aid"
  then have "asset_exists (degree_forget j gs) c aid"
    by (simp add: connected_chains_def)
  then have cne: "c \<noteq> j" and ce: "asset_exists gs c aid"
    by (simp_all add: degree_forget_exists)
  from ce have "c \<in> connected_chains gs aid" by (simp add: connected_chains_def)
  moreover have "get_reg_state (degree_forget j gs) c aid = get_reg_state gs c aid"
    using cne by (rule degree_forget_reg_eq)
  ultimately show
    "c \<in> connected_chains gs aid \<and>
     get_reg_state (degree_forget j gs) c aid = get_reg_state gs c aid"
    by blast
qed

text \<open>
  The degree-\<open>k\<close> transition step.  An operation \<^term>\<open>(act, aid)\<close> reads the hub
  chain's regulatory state for \<open>aid\<close>, fires the regulatory transition, and
  broadcasts the result across the chains coupled at degree \<open>k\<close>.  It is
  undefined exactly when the hub does not hold the asset or the regulatory
  action is not enabled there.
\<close>

definition deg_step ::
  "nat \<Rightarrow> (reg_action \<times> asset_id) \<Rightarrow> global_state \<Rightarrow> global_state option" where
  "deg_step k opn gs =
     (case opn of (act, aid) \<Rightarrow>
        (case get_reg_state gs 0 aid of
           None \<Rightarrow> None
         | Some s \<Rightarrow> (case reg_transition s act of
                        None \<Rightarrow> None
                      | Some s' \<Rightarrow> Some (broadcast_le k aid s' gs))))"

text \<open>The carrier of the degree-\<open>k\<close> functor: states supported on chains
  \<open>0..k\<close>, i.e. only chains within the degree's coupling reach hold assets.\<close>

definition deg_carrier :: "nat \<Rightarrow> global_state set" where
  "deg_carrier k = {gs. \<forall>c aid. asset_exists gs c aid \<longrightarrow> c \<le> k}"

text \<open>The carrier is inhabited --- a non-vacuity witness for the degree
  functors: every authenticated extraction supported on chains \<open>0..k\<close>
  lies in it.\<close>

lemma deg_carrier_inhabited:
  assumes "P \<subseteq> {0..k}"
  shows "auth_state r P \<in> deg_carrier k"
  using assms
  by (auto simp: deg_carrier_def asset_exists_def get_asset_state_def auth_state_def
           split: if_splits)


section \<open>Degree Functors and Their Natural Transformations\<close>

text \<open>
  We package each degree as the data of a transition functor: a set of states
  and an action-indexed family of partial transitions.  Reading the one-object
  action category into \<open>Set\<close>, a natural transformation between two such
  functors is a single state-component map whose naturality squares commute.
  The conditions below mirror, on \<^typ>\<open>global_state\<close>, the well-definedness and
  naturality conditions of \<^locale>\<open>state_preservation\<close> (with the action map the
  identity, since the regulatory action vocabulary is shared across degrees);
  this is the same commuting square that defines the morphisms of the functor
  in \<^theory>\<open>Cross_Domain_State_Preservation.Functor_Laws\<close>.
\<close>

record gobj =
  obj_states :: "global_state set"
  obj_step   :: "(reg_action \<times> asset_id) \<Rightarrow> global_state \<Rightarrow> global_state option"

definition F :: "nat \<Rightarrow> gobj" where
  "F k = \<lparr> obj_states = deg_carrier k, obj_step = deg_step k \<rparr>"

definition natural_transformation ::
  "gobj \<Rightarrow> gobj \<Rightarrow> (global_state \<Rightarrow> global_state) \<Rightarrow> bool" where
  "natural_transformation Fhi Flo \<eta> \<longleftrightarrow>
     (\<forall>gs. gs \<in> obj_states Fhi \<longrightarrow> \<eta> gs \<in> obj_states Flo)
   \<and> (\<forall>opn gs gs'. gs \<in> obj_states Fhi \<longrightarrow> obj_step Fhi opn gs = Some gs'
                  \<longrightarrow> obj_step Flo opn (\<eta> gs) = Some (\<eta> gs'))
   \<and> (\<forall>opn gs. gs \<in> obj_states Fhi \<longrightarrow> obj_step Fhi opn gs = None
              \<longrightarrow> obj_step Flo opn (\<eta> gs) = None)"

text \<open>
  Vertical composition of natural transformations is a natural transformation.
  This is the \<^typ>\<open>global_state\<close>-level analogue of @{thm [source] preservation_compose}:
  the naturality square of the lower transformation is stacked on that of the
  upper one, exactly as the second morphism's square is stacked on the first
  there.  It is the structural fact that makes the whole degree ladder cohere.
\<close>

lemma nt_vertical_compose:
  assumes hi: "natural_transformation A B \<eta>"
      and lo: "natural_transformation B C \<theta>"
  shows "natural_transformation A C (\<theta> \<circ> \<eta>)"
proof -
  from hi have
        hi1: "\<And>gs. gs \<in> obj_states A \<Longrightarrow> \<eta> gs \<in> obj_states B"
    and hi2: "\<And>opn gs gs'. gs \<in> obj_states A \<Longrightarrow> obj_step A opn gs = Some gs'
                \<Longrightarrow> obj_step B opn (\<eta> gs) = Some (\<eta> gs')"
    and hi3: "\<And>opn gs. gs \<in> obj_states A \<Longrightarrow> obj_step A opn gs = None
                \<Longrightarrow> obj_step B opn (\<eta> gs) = None"
    unfolding natural_transformation_def by blast+
  from lo have
        lo1: "\<And>gs. gs \<in> obj_states B \<Longrightarrow> \<theta> gs \<in> obj_states C"
    and lo2: "\<And>opn gs gs'. gs \<in> obj_states B \<Longrightarrow> obj_step B opn gs = Some gs'
                \<Longrightarrow> obj_step C opn (\<theta> gs) = Some (\<theta> gs')"
    and lo3: "\<And>opn gs. gs \<in> obj_states B \<Longrightarrow> obj_step B opn gs = None
                \<Longrightarrow> obj_step C opn (\<theta> gs) = None"
    unfolding natural_transformation_def by blast+
  show ?thesis
    unfolding natural_transformation_def
  proof (intro conjI allI impI)
    fix gs assume "gs \<in> obj_states A"
    then show "(\<theta> \<circ> \<eta>) gs \<in> obj_states C"
      using hi1 lo1 by (simp add: comp_def)
  next
    fix opn gs gs'
    assume a: "gs \<in> obj_states A" and s: "obj_step A opn gs = Some gs'"
    have "obj_step C opn (\<theta> (\<eta> gs)) = Some (\<theta> (\<eta> gs'))"
      using lo2[OF hi1[OF a] hi2[OF a s]] .
    then show "obj_step C opn ((\<theta> \<circ> \<eta>) gs) = Some ((\<theta> \<circ> \<eta>) gs')"
      by (simp add: comp_def)
  next
    fix opn gs
    assume a: "gs \<in> obj_states A" and s: "obj_step A opn gs = None"
    have "obj_step C opn (\<theta> (\<eta> gs)) = None"
      using lo3[OF hi1[OF a] hi3[OF a s]] .
    then show "obj_step C opn ((\<theta> \<circ> \<eta>) gs) = None"
      by (simp add: comp_def)
  qed
qed

text \<open>
  The key commutation: broadcasting at degree \<open>k\<close> after forgetting chain
  \<^term>\<open>Suc k\<close> equals forgetting chain \<^term>\<open>Suc k\<close> after broadcasting at degree
  \<^term>\<open>Suc k\<close>.  This is the heart of the naturality square: on chains \<open>c \<le> k\<close>
  both sides broadcast, on chain \<^term>\<open>Suc k\<close> both sides clear, and on higher
  chains both sides leave \<open>gs\<close> alone.
\<close>

lemma broadcast_forget_commute:
  "broadcast_le k aid v (degree_forget (Suc k) gs)
   = degree_forget (Suc k) (broadcast_le (Suc k) aid v gs)"
proof (rule global_state.equality, goal_cases chains locks more)
  case chains
  show ?case
  proof (intro ext)
    fix c aid'
    consider (le) "c \<le> k" | (top) "c = Suc k" | (gt) "Suc k < c" by linarith
    then show "gs_chains (broadcast_le k aid v (degree_forget (Suc k) gs)) c aid'
               = gs_chains (degree_forget (Suc k) (broadcast_le (Suc k) aid v gs)) c aid'"
    proof cases
      case le
      then have "c \<noteq> Suc k" and "c \<le> Suc k" by linarith+
      with le show ?thesis
        by (simp add: broadcast_le_chains degree_forget_chains)
    next
      case top
      then have "\<not> c \<le> k" by linarith
      with top show ?thesis
        by (simp add: broadcast_le_chains degree_forget_chains)
    next
      case gt
      then have "\<not> c \<le> k" and "\<not> c \<le> Suc k" and "c \<noteq> Suc k" by linarith+
      then show ?thesis
        by (simp add: broadcast_le_chains degree_forget_chains)
    qed
  qed
next
  case locks then show ?case by simp
next
  case more then show ?case by simp
qed

text \<open>
  The degree demotion \<^term>\<open>degree_forget (Suc k)\<close> is a natural transformation
  \<open>F (Suc k) \<Rightarrow> F k\<close>: it maps degree-\<^term>\<open>Suc k\<close> states to degree-\<open>k\<close> states,
  and its naturality square commutes (forget-after-step equals
  step-after-forget, in both the enabled and the disabled case).  Because the
  hub chain \<open>0\<close> is never the dropped chain \<^term>\<open>Suc k\<close>, demotion leaves the
  transition's enabling condition --- the hub's regulatory state --- untouched.
\<close>

theorem degree_natural_transformation:
  "natural_transformation (F (Suc k)) (F k) (degree_forget (Suc k))"
  unfolding natural_transformation_def
proof (intro conjI allI impI)
  fix gs assume gsin: "gs \<in> obj_states (F (Suc k))"
  show "degree_forget (Suc k) gs \<in> obj_states (F k)"
    using gsin by (fastforce simp: F_def deg_carrier_def degree_forget_exists)
next
  fix opn gs gs'
  assume "gs \<in> obj_states (F (Suc k))"
     and step: "obj_step (F (Suc k)) opn gs = Some gs'"
  obtain act aid where opn: "opn = (act, aid)" by (cases opn)
  from step opn have "deg_step (Suc k) (act, aid) gs = Some gs'"
    by (simp add: F_def)
  then obtain s s' where
        hub: "get_reg_state gs 0 aid = Some s"
    and tr: "reg_transition s act = Some s'"
    and gs': "gs' = broadcast_le (Suc k) aid s' gs"
    by (auto simp: deg_step_def split: option.splits)
  have hub': "get_reg_state (degree_forget (Suc k) gs) 0 aid = Some s"
    using hub by (simp add: degree_forget_reg_eq)
  have "obj_step (F k) opn (degree_forget (Suc k) gs)
        = Some (broadcast_le k aid s' (degree_forget (Suc k) gs))"
    using hub' tr by (simp add: F_def deg_step_def opn)
  also have "broadcast_le k aid s' (degree_forget (Suc k) gs)
             = degree_forget (Suc k) (broadcast_le (Suc k) aid s' gs)"
    by (rule broadcast_forget_commute)
  also have "\<dots> = degree_forget (Suc k) gs'" using gs' by simp
  finally show "obj_step (F k) opn (degree_forget (Suc k) gs)
                = Some (degree_forget (Suc k) gs')" .
next
  fix opn gs
  assume "gs \<in> obj_states (F (Suc k))"
     and step: "obj_step (F (Suc k)) opn gs = None"
  obtain act aid where opn: "opn = (act, aid)" by (cases opn)
  from step opn have none: "deg_step (Suc k) (act, aid) gs = None"
    by (simp add: F_def)
  have key: "get_reg_state (degree_forget (Suc k) gs) 0 aid = get_reg_state gs 0 aid"
    by (simp add: degree_forget_reg_eq)
  show "obj_step (F k) opn (degree_forget (Suc k) gs) = None"
  proof (cases "get_reg_state gs 0 aid")
    case None
    then show ?thesis using key by (simp add: F_def deg_step_def opn)
  next
    case (Some s)
    with none have "reg_transition s act = None"
      by (simp add: deg_step_def split: option.splits)
    with key Some show ?thesis by (simp add: F_def deg_step_def opn)
  qed
qed

text \<open>
  Natural transformations of degree functors compose.  The
  two-step demotion \<open>F (k+2) \<Rightarrow> F k\<close> is a natural transformation, obtained by
  vertically composing \<open>F (k+2) \<Rightarrow> F (k+1)\<close> with \<open>F (k+1) \<Rightarrow> F k\<close>.  This is
  what lifts the degree ladder from a point-to-point collection of forgetful
  maps to a structurally coherent tower: the whole chain
  \<open>S\<^sub>3 \<Rightarrow> S\<^sub>2 \<Rightarrow> S\<^sub>1 \<Rightarrow> S\<^sub>0\<close> is natural at once.  The degree functors share one
  action category as common source, so vertical composition is the only
  composition that arises for this tower; horizontal composition and
  whiskering do not typecheck here and are not claimed.  This is a layer
  that, to our knowledge, \<^verbatim>\<open>ADS_Functor\<close> does not develop: it closes functors
  under composition but does not build a hierarchy of functors with natural
  transformations between them.
\<close>

theorem nt_compose:
  "natural_transformation (F (Suc (Suc k))) (F k)
     (degree_forget (Suc k) \<circ> degree_forget (Suc (Suc k)))"
proof (rule nt_vertical_compose)
  show "natural_transformation (F (Suc (Suc k))) (F (Suc k)) (degree_forget (Suc (Suc k)))"
    using degree_natural_transformation[of "Suc k"] .
next
  show "natural_transformation (F (Suc k)) (F k) (degree_forget (Suc k))"
    using degree_natural_transformation[of k] .
qed


section \<open>Functoriality of the Degree Transition Functor on Action Words\<close>

text \<open>
  The natural-transformation results above operate on single regulatory
  operations.  For each fixed asset, we extend the transition step to action
  \<^emph>\<open>words\<close> and prove that it preserves the category structure (identity
  word and word concatenation).  The resulting fixed-asset action category is
  the free monoid of regulatory action sequences; its non-degenerate content
  is supplied by the regulatory transition relation, which composes the
  sequence into a single composite state.  This construction does not cover
  words whose generators mix asset identifiers.
\<close>

fun reg_run :: "reg_state \<Rightarrow> reg_action list \<Rightarrow> reg_state option" where
  "reg_run s [] = Some s"
| "reg_run s (a # w) =
     (case reg_transition s a of None \<Rightarrow> None | Some s' \<Rightarrow> reg_run s' w)"

text \<open>Regulatory composition: running a concatenated action word is running the
  first part and then, from the resulting state, the second.  This is the
  monoid structure the degree functor must transport.\<close>

lemma reg_run_append:
  "reg_run s (v @ w) = (case reg_run s v of None \<Rightarrow> None | Some s' \<Rightarrow> reg_run s' w)"
  by (induction v arbitrary: s) (auto split: option.splits)

fun deg_run ::
  "nat \<Rightarrow> asset_id \<Rightarrow> reg_action list \<Rightarrow> global_state \<Rightarrow> global_state option" where
  "deg_run k aid [] gs = Some gs"
| "deg_run k aid (a # w) gs =
     (case deg_step k (a, aid) gs of None \<Rightarrow> None | Some gs' \<Rightarrow> deg_run k aid w gs')"

text \<open>
  Broadcast overwrite: a second degree-\<open>k\<close> broadcast of the same asset
  obliterates the first.  This is not a free-monoid triviality --- it holds
  because the broadcast set is the chains that \<^emph>\<open>already\<close> hold the asset (which
  the first broadcast does not change) so the second writes over exactly the
  same chains.  It is the structural reason a word of synchronizations
  collapses to a single one.
\<close>

lemma broadcast_le_overwrite:
  "broadcast_le k aid v2 (broadcast_le k aid v1 gs) = broadcast_le k aid v2 gs"
proof (rule global_state.equality, goal_cases chains locks more)
  case chains
  show ?case
  proof (intro ext)
    fix c aid'
    show "gs_chains (broadcast_le k aid v2 (broadcast_le k aid v1 gs)) c aid'
          = gs_chains (broadcast_le k aid v2 gs) c aid'"
    proof (cases "c \<le> k")
      case True
      show ?thesis
        by (cases "aid' = aid"; cases "gs_chains gs c aid")
           (simp_all add: broadcast_le_chains True)
    next
      case False
      then show ?thesis by (simp add: broadcast_le_chains)
    qed
  qed
next
  case locks then show ?case by (simp add: broadcast_le_locks)
next
  case more then show ?case by simp
qed

text \<open>Hub tracking: because the hub chain \<open>0\<close> is always within the coupling
  reach (\<open>0 \<le> k\<close>), a broadcast that finds the asset at the hub leaves the hub
  carrying exactly the broadcast value, so the next step in a word reads the
  updated state.\<close>

lemma broadcast_le_hub:
  assumes "get_reg_state gs 0 aid = Some s0"
  shows "get_reg_state (broadcast_le k aid v gs) 0 aid = Some v"
  using assms broadcast_le_reg_in[of 0 k aid v gs] by simp

text \<open>
  The collapse, on an already-broadcast state.  Running an action word at
  degree \<open>k\<close> from a state of the form \<^term>\<open>broadcast_le k aid v gs\<close> reduces to
  the regulatory composite \<^term>\<open>reg_run v w\<close> broadcast once.  The induction is
  where the degree/broadcast structure does real work: each successive step
  reads the hub value left by the previous broadcast (\<open>broadcast_le_hub\<close>)
  and overwrites it (\<open>broadcast_le_overwrite\<close>).
\<close>

lemma deg_run_on_broadcast:
  assumes "asset_exists gs 0 aid"
  shows "deg_run k aid w (broadcast_le k aid v gs)
         = (case reg_run v w of None \<Rightarrow> None
            | Some sn \<Rightarrow> Some (broadcast_le k aid sn gs))"
  using assms
proof (induction w arbitrary: v)
  case Nil
  show ?case by simp
next
  case (Cons a w)
  have hub: "get_reg_state (broadcast_le k aid v gs) 0 aid = Some v"
  proof -
    from Cons.prems obtain ast where "get_asset_state gs 0 aid = Some ast"
      by (auto simp: asset_exists_def)
    then have "get_reg_state gs 0 aid = Some (as_reg_state ast)"
      by (simp add: get_reg_state_def)
    then show ?thesis by (rule broadcast_le_hub)
  qed
  show ?case
  proof (cases "reg_transition v a")
    case None
    then show ?thesis using hub by (simp add: deg_step_def)
  next
    case (Some v')
    have step: "deg_step k (a, aid) (broadcast_le k aid v gs)
                = Some (broadcast_le k aid v' gs)"
      using hub Some by (simp add: deg_step_def broadcast_le_overwrite)
    show ?thesis using Cons.IH[OF Cons.prems, of v'] Some by (simp add: step)
  qed
qed

text \<open>The general collapse: a non-empty word of degree-\<open>k\<close> synchronizations on an
  asset held at the hub equals broadcasting the composite regulatory state once.\<close>

lemma deg_run_collapse:
  assumes "get_reg_state gs 0 aid = Some s0"
  shows "deg_run k aid (a # w) gs
         = (case reg_run s0 (a # w) of None \<Rightarrow> None
            | Some sn \<Rightarrow> Some (broadcast_le k aid sn gs))"
proof -
  have ex: "asset_exists gs 0 aid"
    using assms by (auto simp: asset_exists_def get_reg_state_def get_asset_state_def
                         split: option.splits)
  show ?thesis
  proof (cases "reg_transition s0 a")
    case None
    then show ?thesis using assms by (simp add: deg_step_def)
  next
    case (Some s1)
    have "deg_step k (a, aid) gs = Some (broadcast_le k aid s1 gs)"
      using assms Some by (simp add: deg_step_def)
    then show ?thesis
      using deg_run_on_broadcast[OF ex, of k w s1] Some by simp
  qed
qed

text \<open>The degree-\<open>k\<close> step keeps a state inside the degree-\<open>k\<close> carrier: a
  broadcast rewrites regulatory values but never changes which chains hold the
  asset, so the support bound \<open>c \<le> k\<close> is preserved.\<close>

lemma deg_step_carrier:
  assumes "gs \<in> deg_carrier k" and "deg_step k (a, aid) gs = Some gs'"
  shows "gs' \<in> deg_carrier k"
proof -
  from assms(2) obtain s s' where
    "get_reg_state gs 0 aid = Some s" and "reg_transition s a = Some s'"
    and gs': "gs' = broadcast_le k aid s' gs"
    by (auto simp: deg_step_def split: option.splits)
  have "\<And>c aid''. asset_exists gs' c aid'' = asset_exists gs c aid''"
    unfolding gs' by (simp add: broadcast_le_exists)
  with assms(1) show ?thesis by (auto simp: deg_carrier_def)
qed

text \<open>
  Functor laws on action words.  The identity word acts as the identity, and a
  concatenation of words is the Kleisli composition of the two segment maps:
  \<^const>\<open>deg_run\<close> is a functor from the free monoid of regulatory action
  sequences into the Kleisli category of the option monad on
  \<^typ>\<open>global_state\<close>.  These two laws are the categorical skeleton; the
  semantic content that the functor is non-degenerate --- that its action on a
  word is the regulatory composite broadcast once, not an arbitrary fold --- is
  @{thm [source] deg_run_collapse}.
\<close>

lemma deg_run_Nil: "deg_run k aid [] = Some"
  by (simp add: fun_eq_iff)

lemma deg_run_append:
  "deg_run k aid (v @ w) gs = Option.bind (deg_run k aid v gs) (deg_run k aid w)"
  by (induction v arbitrary: gs) (auto split: option.splits)

text \<open>
  Non-degeneracy witness.  A genuine two-action regulatory word ---
  \<^term>\<open>FREEZE\<close> then \<^term>\<open>CONFISCATE\<close> --- composes to \<^term>\<open>CONFISCATED\<close>
  through the intermediate \<^term>\<open>FROZEN\<close>, and at the degree level its second
  synchronization overwrites the first: the word \<open>[FREEZE, CONFISCATE]\<close>
  broadcasts \<^term>\<open>CONFISCATED\<close> while its prefix \<open>[FREEZE]\<close> broadcasts
  \<^term>\<open>FROZEN\<close>.  The two differ, so the composition is not idempotent padding;
  the functor transports real regulatory content.
\<close>

lemma deg_run_nondegenerate:
  assumes "get_reg_state gs 0 0 = Some ACTIVE"
  shows "deg_run k 0 [FREEZE, CONFISCATE] gs = Some (broadcast_le k 0 CONFISCATED gs)"
    and "deg_run k 0 [FREEZE] gs = Some (broadcast_le k 0 FROZEN gs)"
    and "broadcast_le k 0 CONFISCATED gs \<noteq> broadcast_le k 0 FROZEN gs"
proof -
  have f1: "reg_transition ACTIVE FREEZE = Some FROZEN" by simp
  have f2: "reg_transition FROZEN CONFISCATE = Some CONFISCATED" by simp
  have rc: "reg_run ACTIVE [FREEZE, CONFISCATE] = Some CONFISCATED" using f1 f2 by simp
  have rf: "reg_run ACTIVE [FREEZE] = Some FROZEN" using f1 by simp
  show "deg_run k 0 [FREEZE, CONFISCATE] gs = Some (broadcast_le k 0 CONFISCATED gs)"
    using deg_run_collapse[OF assms, of k FREEZE "[CONFISCATE]"] rc by simp
  show "deg_run k 0 [FREEZE] gs = Some (broadcast_le k 0 FROZEN gs)"
    using deg_run_collapse[OF assms, of k FREEZE "[]"] rf by simp
  have c1: "get_reg_state (broadcast_le k 0 CONFISCATED gs) 0 0 = Some CONFISCATED"
    using assms by (simp add: broadcast_le_reg_in)
  have c2: "get_reg_state (broadcast_le k 0 FROZEN gs) 0 0 = Some FROZEN"
    using assms by (simp add: broadcast_le_reg_in)
  show "broadcast_le k 0 CONFISCATED gs \<noteq> broadcast_le k 0 FROZEN gs"
  proof
    assume "broadcast_le k 0 CONFISCATED gs = broadcast_le k 0 FROZEN gs"
    then have "get_reg_state (broadcast_le k 0 CONFISCATED gs) 0 0
             = get_reg_state (broadcast_le k 0 FROZEN gs) 0 0" by simp
    with c1 c2 show False by simp
  qed
qed


text \<open>
  The single-step naturality square of \<^theory_text>\<open>degree_natural_transformation\<close>,
  re-exposed at the level of \<^const>\<open>deg_step\<close> for use inside the word
  induction below.
\<close>

lemma deg_step_forget_some:
  assumes "gs \<in> deg_carrier (Suc k)" and "deg_step (Suc k) opn gs = Some gs'"
  shows "deg_step k opn (degree_forget (Suc k) gs) = Some (degree_forget (Suc k) gs')"
proof -
  obtain a b where opn: "opn = (a, b)" by (cases opn)
  show ?thesis
    using degree_natural_transformation[of k] assms
    unfolding opn natural_transformation_def F_def by auto
qed

lemma deg_step_forget_none:
  assumes "gs \<in> deg_carrier (Suc k)" and "deg_step (Suc k) opn gs = None"
  shows "deg_step k opn (degree_forget (Suc k) gs) = None"
proof -
  obtain a b where opn: "opn = (a, b)" by (cases opn)
  show ?thesis
    using degree_natural_transformation[of k] assms
    unfolding opn natural_transformation_def F_def by auto
qed

text \<open>
  Naturality on a fixed asset's action-word category.  The single-step square
  above lifts, by induction on the action word, to the statement that degree
  demotion commutes with running an \<^emph>\<open>entire\<close> fixed-asset word: forgetting the top chain
  and then running at degree \<open>k\<close> equals running at degree \<^term>\<open>Suc k\<close> and then
  forgetting.  Together with the functor laws @{thm [source] deg_run_Nil} and
  @{thm [source] deg_run_append}, this promotes
  @{thm [source] degree_natural_transformation} from a square on generators to
  a genuine natural transformation between the degree functors
  \<^term>\<open>F (Suc k)\<close> and \<^term>\<open>F k\<close> on that fixed-asset free action
  category.  Mixed-asset words are outside the theorem's scope.
\<close>

theorem degree_forget_natural_run:
  assumes "gs \<in> deg_carrier (Suc k)"
  shows "deg_run k aid w (degree_forget (Suc k) gs)
         = map_option (degree_forget (Suc k)) (deg_run (Suc k) aid w gs)"
  using assms
proof (induction w arbitrary: gs)
  case Nil
  show ?case by simp
next
  case (Cons a w)
  show ?case
  proof (cases "deg_step (Suc k) (a, aid) gs")
    case None
    then have "deg_step k (a, aid) (degree_forget (Suc k) gs) = None"
      using deg_step_forget_none[OF Cons.prems] by simp
    then show ?thesis using None by simp
  next
    case (Some gs')
    have "deg_step k (a, aid) (degree_forget (Suc k) gs) = Some (degree_forget (Suc k) gs')"
      using deg_step_forget_some[OF Cons.prems Some] .
    moreover have "gs' \<in> deg_carrier (Suc k)"
      using deg_step_carrier[OF Cons.prems Some] .
    ultimately show ?thesis using Cons.IH Some by simp
  qed
qed


section \<open>Degree Classes and Hierarchy Monotonicity\<close>

text \<open>
  Each asset carries a required coupling strength, its \<^emph>\<open>degree\<close>, ranging over
  the four classes \<open>S\<^sub>0\<close>..\<open>S\<^sub>3\<close>.  An asset belongs to the degree-\<open>k\<close> class when its
  required strength is at least \<open>k\<close>; since a requirement of at least \<^term>\<open>k'\<close>
  entails a requirement of at least any \<open>k \<le> k'\<close>, the classes are nested
  (\<^theory_text>\<open>reduction_containment\<close>).  A system, in turn, has a capability degree; it is
  the comparison of the asset's required degree with the system's capability
  degree that decides over- and under-provisioning.

  The assignment of degrees to assets is operational data, not structure: the
  whole degree-class layer below is therefore parametric in an arbitrary
  assignment \<open>asset_degree :: asset_id \<Rightarrow> nat\<close>, fixed in an anonymous context.
  Every theorem of the layer holds for every assignment; a concrete example
  assignment witnesses non-vacuity at the end of the section.
\<close>

text \<open>
  Processing an asset at system degree \<open>d\<close> reconciles it across the chains the
  system couples (those with index \<open>\<le> d\<close>): it broadcasts the hub chain's
  regulatory value over that reach.  Reconciling to the hub value is the
  state-level action of a degree-\<open>d\<close> synchronization.  The processing
  machinery is independent of the degree assignment, so it lives outside the
  parametric context.
\<close>

definition process_at_degree :: "nat \<Rightarrow> global_state \<Rightarrow> asset_id \<Rightarrow> global_state" where
  "process_at_degree d gs aid =
     (case get_reg_state gs 0 aid of
        None \<Rightarrow> gs
      | Some v \<Rightarrow> broadcast_le d aid v gs)"

text \<open>On a consistent state every chain holding the asset already agrees with
  the hub, so broadcasting the hub value over any reach leaves the state
  consistent.\<close>

lemma broadcast_le_consistent:
  assumes cons: "consistent_state gs" and hub: "get_reg_state gs 0 aid = Some v"
  shows "consistent_state (broadcast_le d aid v gs)"
  unfolding consistent_state_def
proof (intro allI impI)
  fix c1 c2 aid'' s1 s2
  assume g1: "get_reg_state (broadcast_le d aid v gs) c1 aid'' = Some s1"
     and g2: "get_reg_state (broadcast_le d aid v gs) c2 aid'' = Some s2"
  have val: "\<And>c s. get_reg_state (broadcast_le d aid v gs) c aid'' = Some s \<Longrightarrow> aid'' = aid \<Longrightarrow> s = v"
  proof -
    fix c s
    assume gc: "get_reg_state (broadcast_le d aid v gs) c aid'' = Some s" and eqaid: "aid'' = aid"
    show "s = v"
    proof (cases "c \<le> d")
      case True
      with gc eqaid have "(case get_reg_state gs c aid of None \<Rightarrow> None | Some _ \<Rightarrow> Some v) = Some s"
        by (simp add: broadcast_le_reg_in)
      then show "s = v" by (auto split: option.splits)
    next
      case False
      with gc eqaid have "get_reg_state gs c aid = Some s" by (simp add: broadcast_le_reg_out)
      with cons hub show "s = v" unfolding consistent_state_def by blast
    qed
  qed
  show "s1 = s2"
  proof (cases "aid'' = aid")
    case True
    from val[OF g1 True] val[OF g2 True] show ?thesis by simp
  next
    case False
    then have "get_reg_state gs c1 aid'' = Some s1" and "get_reg_state gs c2 aid'' = Some s2"
      using g1 g2 by (simp_all add: broadcast_le_reg_other_asset)
    then show ?thesis using cons unfolding consistent_state_def by blast
  qed
qed

text \<open>
  Validity preservation under processing holds with no reference to degrees
  at all: on a consistent state the broadcast value agrees with every chain
  it overwrites, and the broadcast touches no lock.  Isolating this as its
  own lemma records that the degree hypothesis of the over-provisioning
  headline below is not load-bearing for validity --- the regime-sensitive
  content, where over- and under-provisioning genuinely diverge, is the pair
  \<open>over_provisioning_guarantees\<close> / \<open>no_downward_safety\<close>.
\<close>

lemma processing_preserves_validity:
  assumes "valid_state gs"
  shows "valid_state (process_at_degree d gs aid)"
proof (cases "get_reg_state gs 0 aid")
  case None
  then show ?thesis using assms by (simp add: process_at_degree_def)
next
  case (Some v)
  from assms have c: "consistent_state gs" and nl: "no_locked_without_reason gs"
    by (simp_all add: valid_state_def)
  have "consistent_state (broadcast_le d aid v gs)"
    using broadcast_le_consistent[OF c Some] .
  moreover have "no_locked_without_reason (broadcast_le d aid v gs)"
    using nl by (simp add: no_locked_without_reason_def is_locked_def)
  ultimately show ?thesis using Some by (simp add: process_at_degree_def valid_state_def)
qed

text \<open>The timestamp order \<^verbatim>\<open>lamport_hb\<close> underlying the degree boundary is
  likewise independent of the degree assignment; it is a plain strict order on
  integer timestamps, not a distributed causal order.\<close>

definition lamport_hb :: "timestamp \<Rightarrow> timestamp \<Rightarrow> bool" where
  "lamport_hb t1 t2 \<longleftrightarrow> t1 < t2"

text \<open>
  The degree-class layer, parametric in the degree assignment.  Everything
  proved inside this context holds for an \<^emph>\<open>arbitrary\<close> assignment
  \<open>asset_degree\<close>; on export each constant and theorem generalises over the
  assignment.
\<close>

context
  fixes asset_degree :: "asset_id \<Rightarrow> nat"
begin

definition degree_capable :: "nat \<Rightarrow> asset_id \<Rightarrow> bool" where
  "degree_capable k aid \<longleftrightarrow> k \<le> asset_degree aid"

text \<open>Reduction containment: the degree classes form a descending chain, so
  membership in a higher class entails membership in every lower one.  This is
  the partial-order closure of the hierarchy.\<close>

theorem reduction_containment:
  "k \<le> k' \<Longrightarrow> degree_capable k' aid \<longrightarrow> degree_capable k aid"
  unfolding degree_capable_def by simp

text \<open>
  Validity preservation in the over-provisioning regime (auxiliary).  A system
  preserves global validity when it processes an asset.  This is a
  \<^emph>\<open>degree-free\<close> fact: its proof is exactly
  @{thm [source] processing_preserves_validity}, and it carries no provisioning
  hypothesis.  It is therefore recorded
  as an auxiliary lemma aliasing that fact, \<^emph>\<open>not\<close> the headline monotonicity
  result.  The genuinely
  degree-sensitive, one-directional monotonicity is carried by
  \<open>over_provisioning_guarantees\<close> together with \<open>no_downward_safety\<close> below,
  where the provisioning hypothesis is load-bearing.
\<close>

lemma hierarchy_monotonicity:
  assumes "valid_state gs"
  shows "valid_state (process_at_degree system_degree gs aid)"
  using assms by (rule processing_preserves_validity)

text \<open>
  The coupling guarantee a degree-\<open>d\<close> system actually delivers: after
  processing, all of the asset's \<^emph>\<open>required\<close> chains --- those within its degree
  class, index \<open>\<le> asset_degree aid\<close> --- that hold the asset agree on its
  regulatory state.
\<close>

definition guarantees_preservation :: "nat \<Rightarrow> global_state \<Rightarrow> asset_id \<Rightarrow> bool" where
  "guarantees_preservation d gs aid \<longleftrightarrow>
     (\<forall>c1 c2. c1 \<le> asset_degree aid \<longrightarrow> c2 \<le> asset_degree aid
        \<longrightarrow> get_reg_state (process_at_degree d gs aid) c1 aid \<noteq> None
        \<longrightarrow> get_reg_state (process_at_degree d gs aid) c2 aid \<noteq> None
        \<longrightarrow> get_reg_state (process_at_degree d gs aid) c1 aid
            = get_reg_state (process_at_degree d gs aid) c2 aid)"

text \<open>Under over-provisioning the guarantee is met: every required chain lies
  within the system's coupling reach (\<open>\<le> asset_degree aid \<le> d\<close>), so all are
  driven to the single hub value.\<close>

theorem over_provisioning_guarantees:
  assumes deg: "asset_degree aid \<le> d" and val: "valid_state gs"
  shows "guarantees_preservation d gs aid"
proof (cases "get_reg_state gs 0 aid")
  case None
  then have proc: "process_at_degree d gs aid = gs" by (simp add: process_at_degree_def)
  show ?thesis
    unfolding guarantees_preservation_def proc
  proof (intro allI impI)
    fix c1 c2
    assume "c1 \<le> asset_degree aid" and "c2 \<le> asset_degree aid"
       and "get_reg_state gs c1 aid \<noteq> None" and "get_reg_state gs c2 aid \<noteq> None"
    then obtain s1 s2 where
      s1: "get_reg_state gs c1 aid = Some s1" and s2: "get_reg_state gs c2 aid = Some s2"
      by auto
    have "s1 = s2" using val s1 s2 unfolding valid_state_def consistent_state_def by blast
    with s1 s2 show "get_reg_state gs c1 aid = get_reg_state gs c2 aid" by simp
  qed
next
  case (Some v)
  then have proc: "process_at_degree d gs aid = broadcast_le d aid v gs"
    by (simp add: process_at_degree_def)
  show ?thesis
    unfolding guarantees_preservation_def
  proof (intro allI impI)
    fix c1 c2
    assume c1d: "c1 \<le> asset_degree aid" and c2d: "c2 \<le> asset_degree aid"
       and d1: "get_reg_state (process_at_degree d gs aid) c1 aid \<noteq> None"
       and d2: "get_reg_state (process_at_degree d gs aid) c2 aid \<noteq> None"
    from c1d deg have l1: "c1 \<le> d" by simp
    from c2d deg have l2: "c2 \<le> d" by simp
    have "get_reg_state (process_at_degree d gs aid) c1 aid = Some v"
      using l1 d1 unfolding proc by (auto simp: broadcast_le_reg_in split: option.splits)
    moreover have "get_reg_state (process_at_degree d gs aid) c2 aid = Some v"
      using l2 d2 unfolding proc by (auto simp: broadcast_le_reg_in split: option.splits)
    ultimately show "get_reg_state (process_at_degree d gs aid) c1 aid
                     = get_reg_state (process_at_degree d gs aid) c2 aid" by simp
  qed
qed

text \<open>
  The degree hypothesis is load-bearing in its own right: from an
  \<^emph>\<open>arbitrary\<close> hub-defined state --- with no validity assumption, so the
  chains may well disagree beforehand --- over-provisioning alone drives
  every required chain to the hub value.  Without it, \<open>no_downward_safety\<close>
  below exhibits the failure on exactly such a disagreeing state, so the
  contrast pair is matched: both directions speak about arbitrary states.
\<close>

theorem over_provisioning_reconciles:
  assumes deg: "asset_degree aid \<le> d"
    and hub: "get_reg_state gs 0 aid = Some v"
  shows "guarantees_preservation d gs aid"
proof -
  have proc: "process_at_degree d gs aid = broadcast_le d aid v gs"
    using hub by (simp add: process_at_degree_def)
  show ?thesis
    unfolding guarantees_preservation_def
  proof (intro allI impI)
    fix c1 c2
    assume c1d: "c1 \<le> asset_degree aid" and c2d: "c2 \<le> asset_degree aid"
       and d1: "get_reg_state (process_at_degree d gs aid) c1 aid \<noteq> None"
       and d2: "get_reg_state (process_at_degree d gs aid) c2 aid \<noteq> None"
    from c1d deg have l1: "c1 \<le> d" by simp
    from c2d deg have l2: "c2 \<le> d" by simp
    have "get_reg_state (process_at_degree d gs aid) c1 aid = Some v"
      using l1 d1 unfolding proc by (auto simp: broadcast_le_reg_in split: option.splits)
    moreover have "get_reg_state (process_at_degree d gs aid) c2 aid = Some v"
      using l2 d2 unfolding proc by (auto simp: broadcast_le_reg_in split: option.splits)
    ultimately show "get_reg_state (process_at_degree d gs aid) c1 aid
                     = get_reg_state (process_at_degree d gs aid) c2 aid" by simp
  qed
qed

text \<open>
  No downward safety.  Under-provisioning carries no preservation guarantee:
  if the asset's required degree exceeds the system's capability, then some
  state defeats every preservation claim.  The witness places the hub at
  \<^const>\<open>ACTIVE\<close> and a required chain just beyond the system's reach (index
  \<^term>\<open>Suc system_degree\<close>) at \<^const>\<open>FROZEN\<close>; processing reconciles only the
  chains within reach, leaving the out-of-reach required chain in
  disagreement.  This is the formal counterpart of over-provisioning safety:
  the monotonicity is genuinely one-directional.
\<close>

theorem no_downward_safety:
  assumes "asset_degree aid > system_degree"
  shows "\<not> (\<forall>gs. guarantees_preservation system_degree gs aid)"
proof -
  define ast0 where "ast0 = \<lparr> as_reg_state = ACTIVE \<rparr>"
  define ast1 where "ast1 = \<lparr> as_reg_state = FROZEN \<rparr>"
  define gs0 where "gs0 =
     \<lparr> gs_chains = (\<lambda>c. if c = 0 then (\<lambda>a. if a = aid then Some ast0 else None)
                         else if c = Suc system_degree then (\<lambda>a. if a = aid then Some ast1 else None)
                         else (\<lambda>a. None)),
        gs_locks = (\<lambda>a. False) \<rparr>"
  have c0: "get_reg_state gs0 0 aid = Some ACTIVE"
    by (simp add: gs0_def get_reg_state_def get_asset_state_def ast0_def)
  have c1: "get_reg_state gs0 (Suc system_degree) aid = Some FROZEN"
    by (simp add: gs0_def get_reg_state_def get_asset_state_def ast1_def)
  have proc: "process_at_degree system_degree gs0 aid = broadcast_le system_degree aid ACTIVE gs0"
    using c0 by (simp add: process_at_degree_def)
  have p0: "get_reg_state (process_at_degree system_degree gs0 aid) 0 aid = Some ACTIVE"
    using proc c0 by (simp add: broadcast_le_reg_in)
  have p1: "get_reg_state (process_at_degree system_degree gs0 aid) (Suc system_degree) aid = Some FROZEN"
    using proc c1 by (simp add: broadcast_le_reg_out)
  have le0: "(0::nat) \<le> asset_degree aid" by simp
  have le1: "Suc system_degree \<le> asset_degree aid" using assms by simp
  have "\<not> guarantees_preservation system_degree gs0 aid"
  proof
    assume "guarantees_preservation system_degree gs0 aid"
    then have "get_reg_state (process_at_degree system_degree gs0 aid) 0 aid
               = get_reg_state (process_at_degree system_degree gs0 aid) (Suc system_degree) aid"
      unfolding guarantees_preservation_def using le0 le1 p0 p1 by blast
    with p0 p1 show False by simp
  qed
  then show ?thesis by blast
qed

text \<open>
  The timestamp-order degree boundary.  The classes \<open>S\<^sub>1\<close> and
  \<open>S\<^sub>2\<close> are separated by a degree-2 threshold.  The legacy identifiers
  \<open>requires_causal\<close> and \<open>causal_consistent_at\<close> label that threshold, but
  the formal relation is only the strict order on integer timestamps, not a
  distributed happened-before relation.  We show the boundary is
  well-defined on \<open>(asset, system)\<close> pairs: the requirement is a single-valued
  function of the asset's degree, it is met whenever the system over-provisions
  the asset, and the underlying happened-before relation is a strict partial
  order (irreflexive and asymmetric; in fact linear, as timestamps are
  linearly ordered), so the timestamp-order boundary is well-formed.
\<close>

text \<open>
  The degree index corresponds to the product's synchronization-degree
  hierarchy \<open>S\<^sub>0\<close>..\<open>S\<^sub>3\<close>: \<open>F k\<close> formalizes the \<^emph>\<open>coupling breadth\<close> of degree
  \<open>k\<close> --- the containment and monotonicity structure of the ladder --- while
  the per-degree synchronization semantics itself (static, unidirectional
  observation, bidirectional coupling, atomic state binding) is abstracted.
  The timestamp-order boundary sits at \<open>k = 2\<close>, the S1/S2 transition below.
\<close>

definition requires_causal :: "asset_id \<Rightarrow> bool" where
  "requires_causal aid \<longleftrightarrow> 2 \<le> asset_degree aid"

definition causal_consistent_at :: "asset_id \<Rightarrow> nat \<Rightarrow> bool" where
  "causal_consistent_at aid d \<longleftrightarrow> (requires_causal aid \<longrightarrow> 2 \<le> d)"

theorem boundary_well_defined:
  "(causal_consistent_at aid d \<longleftrightarrow> (2 \<le> asset_degree aid \<longrightarrow> 2 \<le> d))
   \<and> (asset_degree aid \<le> d \<longrightarrow> causal_consistent_at aid d)
   \<and> (\<forall>t1 t2. lamport_hb t1 t2 \<longrightarrow> \<not> lamport_hb t2 t1)
   \<and> (\<forall>t. \<not> lamport_hb t t)
   \<and> (\<forall>t1 t2 t3. lamport_hb t1 t2 \<longrightarrow> lamport_hb t2 t3 \<longrightarrow> lamport_hb t1 t3)"
  by (auto simp: causal_consistent_at_def requires_causal_def lamport_hb_def)

end

text \<open>
  Non-vacuity of the parametric layer: a concrete example assignment, cycling
  the four degree classes over asset identifiers.  The over-provisioning
  guarantee instantiates to it directly.
\<close>

definition example_degree :: "asset_id \<Rightarrow> nat" where
  "example_degree aid = aid mod 4"

corollary example_degree_over_provisioning:
  "example_degree aid \<le> d \<Longrightarrow> valid_state gs
   \<Longrightarrow> guarantees_preservation example_degree d gs aid"
  by (rule over_provisioning_guarantees)

text \<open>
  Static promotion safety.  A promotion re-assigns an asset's required
  degree; statically --- between synchronizations --- the change is just a
  different assignment parameter, so as long as the promoted degree stays
  within the system's capability, the over-provisioning guarantee transfers
  verbatim to the new assignment.  In-flight promotion (a re-assignment
  crossing a live synchronization) is out of scope for this entry; subsequent
  work on retry-queue semantics covers it.
\<close>

corollary static_promotion_safety:
  assumes "asset_degree' aid \<le> system_degree" and "valid_state gs"
  shows "guarantees_preservation asset_degree' system_degree gs aid"
  using assms by (rule over_provisioning_guarantees)

end
