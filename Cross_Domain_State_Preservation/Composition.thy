(*
  Title:      Cross_Domain_State_Preservation/Composition.thy
  Author:     Jinwook Kim (Jay) <jay@oraclizer.io>
  Maintainer: Jinwook Kim (Jay) <jay@oraclizer.io>
  License:    BSD

  Compositional Integration of Safety and Liveness — Generic Theory

  This theory provides reusable, system-independent locales for composing a
  guarded safety invariant with an eventual-progress (liveness) scheduler,
  and for deriving guarded bounded convergence: starting from an arbitrary
  carrier state — not assumed to satisfy the invariant — the system reaches
  an invariant-satisfying state within a bounded number of evolution steps.

  The development is deliberately abstract.  It speaks only of carriers,
  steps, operations, invariants, guards, schedules, dischargers and a
  realization map; it commits to no concrete application vocabulary.  The
  three core locales (guarded_invariant, eventual_discharger,
  safety_liveness_composition) and the convergence extension are intended to
  be instantiated by any guarded transition system equipped with a
  bounded-fair progress scheduler.
*)

theory Composition
  imports State_Preservation
begin

section \<open>Guarded Invariants\<close>

text \<open>
  A guarded transition system: a carrier set closed under stepping, together
  with an invariant that is preserved by every \emph{guarded} step.  The
  guard isolates exactly the operations that may fire while maintaining the
  invariant.
\<close>

locale guarded_invariant =
  fixes carrier :: "'s set"
    and step :: "'s \<Rightarrow> 'op \<Rightarrow> 's option"
    and ops :: "'op set"
    and inv :: "'s \<Rightarrow> bool"
    and guard :: "'s \<Rightarrow> 'op \<Rightarrow> bool"
  assumes step_closed:
      "\<lbrakk> s \<in> carrier; opn \<in> ops; step s opn = Some s' \<rbrakk> \<Longrightarrow> s' \<in> carrier"
    and guarded_preservation:
      "\<lbrakk> s \<in> carrier; opn \<in> ops; inv s; guard s opn; step s opn = Some s' \<rbrakk>
       \<Longrightarrow> inv s'"


section \<open>Eventual Dischargers\<close>

text \<open>
  A scheduler that, within every window of length \<^term>\<open>window\<close>, produces at
  least one discharging event.  This is a bounded-fairness abstraction:
  progress-bearing events are never starved beyond \<^term>\<open>window\<close> time units.
\<close>

locale eventual_discharger =
  fixes schedule :: "nat \<Rightarrow> 'event"
    and discharges :: "'event \<Rightarrow> bool"
    and window :: "nat"
  assumes bounded_occurrence:
      "\<forall>t. \<exists>t'. t \<le> t' \<and> t' < t + window \<and> discharges (schedule t')"
begin

text \<open>Window positivity is implied by bounded occurrence: the window starting
  at any time index must be non-empty to contain a discharging slot.  It is
  therefore derived rather than assumed.\<close>

lemma window_positive: "window > 0"
proof -
  obtain t' where "(0::nat) \<le> t'" and "t' < 0 + window"
    using bounded_occurrence by blast
  then show ?thesis by simp
qed

end


section \<open>Compositional Safety and Liveness\<close>

text \<open>
  The composition couples a guarded invariant with an eventual discharger
  through a realization map \<^term>\<open>realize\<close> that turns a discharging event, in
  the current state, into an operation.  The coupling assumption states that
  any realized operation is admissible and guarded; invariant preservation
  along a trajectory then follows from the guard, and progress is supplied by
  the measure discharge of the converging extension below.
\<close>

locale safety_liveness_composition =
  safe: guarded_invariant carrier step ops inv guard +
  live: eventual_discharger schedule discharges window
  for carrier :: "'s set"
    and step :: "'s \<Rightarrow> 'op \<Rightarrow> 's option"
    and ops :: "'op set"
    and inv :: "'s \<Rightarrow> bool"
    and guard :: "'s \<Rightarrow> 'op \<Rightarrow> bool"
    and schedule :: "nat \<Rightarrow> 'event"
    and discharges :: "'event \<Rightarrow> bool"
    and window :: "nat" +
  fixes realize :: "'event \<Rightarrow> 's \<Rightarrow> 'op option"
  assumes realize_discharges:
      "\<lbrakk> s \<in> carrier; discharges ev; realize ev s = Some opn \<rbrakk>
       \<Longrightarrow> opn \<in> ops \<and> guard s opn"
begin

text \<open>
  One evolution step at absolute time index \<^term>\<open>t\<close>: a scheduled discharging
  event is realized and applied; any non-discharging event (or a realization
  that does not enable a step) stutters, leaving the state unchanged.
\<close>

definition evolve_step :: "nat \<Rightarrow> 's \<Rightarrow> 's" where
  "evolve_step t s =
     (if discharges (schedule t) then
        (case realize (schedule t) s of
           None \<Rightarrow> s
         | Some opn \<Rightarrow> (case step s opn of None \<Rightarrow> s | Some s' \<Rightarrow> s'))
      else s)"

text \<open>The trajectory of length \<^term>\<open>n\<close> started at time index \<^term>\<open>k\<close>.\<close>

fun run_from :: "nat \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> 's" where
  "run_from k s 0 = s"
| "run_from k s (Suc n) = evolve_step (k + n) (run_from k s n)"

text \<open>The trajectory started at time \<^term>\<open>0\<close>, and the induced evolution relation.\<close>

definition run :: "'s \<Rightarrow> nat \<Rightarrow> 's" where
  "run s n = run_from 0 s n"

definition evolves_to :: "'s \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> bool" where
  "evolves_to s t s' \<longleftrightarrow> run s t = s'"

text \<open>Trajectories compose: continuing for \<^term>\<open>b\<close> more steps re-roots the
  schedule index by \<^term>\<open>a\<close>.\<close>

lemma run_from_add:
  "run_from k s (a + b) = run_from (k + a) (run_from k s a) b"
proof (induction b)
  case 0
  show ?case by simp
next
  case (Suc b)
  have "run_from k s (a + Suc b) = evolve_step (k + (a + b)) (run_from k s (a + b))"
    by simp
  also have "\<dots> = evolve_step (k + (a + b)) (run_from (k + a) (run_from k s a) b)"
    using Suc.IH by simp
  also have "\<dots> = run_from (k + a) (run_from k s a) (Suc b)"
    by (simp add: add.assoc)
  finally show ?case .
qed

lemma evolve_step_stutter:
  "\<not> discharges (schedule t) \<Longrightarrow> evolve_step t s = s"
  by (simp add: evolve_step_def)

text \<open>A single evolution step keeps the carrier.\<close>

lemma evolve_step_carrier:
  assumes "s \<in> carrier"
  shows "evolve_step t s \<in> carrier"
proof (cases "discharges (schedule t)")
  case False
  then show ?thesis using assms by (simp add: evolve_step_def)
next
  case True
  show ?thesis
  proof (cases "realize (schedule t) s")
    case None
    with assms True show ?thesis by (simp add: evolve_step_def)
  next
    case (Some opn)
    note r = this
    show ?thesis
    proof (cases "step s opn")
      case None
      with assms True r show ?thesis by (simp add: evolve_step_def)
    next
      case (Some s')
      note st = this
      have op_in: "opn \<in> ops" using realize_discharges[OF assms True r] by simp
      have "s' \<in> carrier" using safe.step_closed[OF assms op_in st] .
      with True r st show ?thesis by (simp add: evolve_step_def)
    qed
  qed
qed

text \<open>A single evolution step preserves the invariant on the carrier.\<close>

lemma evolve_step_inv:
  assumes "s \<in> carrier" and "inv s"
  shows "inv (evolve_step t s)"
proof (cases "discharges (schedule t)")
  case False
  then show ?thesis using assms by (simp add: evolve_step_def)
next
  case True
  show ?thesis
  proof (cases "realize (schedule t) s")
    case None
    with assms True show ?thesis by (simp add: evolve_step_def)
  next
    case (Some opn)
    note r = this
    show ?thesis
    proof (cases "step s opn")
      case None
      with assms True r show ?thesis by (simp add: evolve_step_def)
    next
      case (Some s')
      note st = this
      have c: "opn \<in> ops \<and> guard s opn" using realize_discharges[OF assms(1) True r] .
      have "inv s'"
        using safe.guarded_preservation[OF assms(1) conjunct1[OF c] assms(2) conjunct2[OF c] st] .
      with True r st show ?thesis by (simp add: evolve_step_def)
    qed
  qed
qed

lemma run_from_carrier:
  assumes "s \<in> carrier"
  shows "run_from k s n \<in> carrier"
proof (induction n)
  case 0
  show ?case using assms by simp
next
  case (Suc n)
  show ?case using evolve_step_carrier[OF Suc.IH] by simp
qed

lemma run_from_inv:
  assumes "s \<in> carrier" and "inv s"
  shows "inv (run_from k s n)"
proof (induction n)
  case 0
  show ?case using assms(2) by simp
next
  case (Suc n)
  have car: "run_from k s n \<in> carrier" using run_from_carrier[OF assms(1)] .
  have "inv (evolve_step (k + n) (run_from k s n))" using evolve_step_inv[OF car Suc.IH] .
  then show ?case by simp
qed

text \<open>If no discharging event occurs in the first \<^term>\<open>n\<close> slots from \<^term>\<open>k\<close>,
  the state is unchanged.\<close>

lemma run_from_stutter:
  assumes "\<forall>j<n. \<not> discharges (schedule (k + j))"
  shows "run_from k s n = s"
  using assms
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "\<forall>j<n. \<not> discharges (schedule (k + j))" using Suc.prems by simp
  then have ih: "run_from k s n = s" using Suc.IH by simp
  have "\<not> discharges (schedule (k + n))" using Suc.prems by simp
  then have "evolve_step (k + n) (run_from k s n) = run_from k s n"
    by (simp add: evolve_step_stutter)
  then show ?case using ih by simp
qed

text \<open>
  Invariant preservation along the whole trajectory: from an invariant
  carrier state, every reachable state still satisfies the invariant and
  stays in the carrier.
\<close>

lemma invariant_preserved:
  assumes "s \<in> carrier" and "inv s"
  shows "inv (run s t) \<and> run s t \<in> carrier"
proof -
  have "inv (run_from 0 s t)" using run_from_inv[OF assms] .
  moreover have "run_from 0 s t \<in> carrier" using run_from_carrier[OF assms(1)] .
  ultimately show ?thesis by (simp add: run_def)
qed

end


section \<open>Guarded Bounded Convergence\<close>

text \<open>
  \<^locale>\<open>safety_liveness_composition\<close> is extended with a natural-number progress
  measure whose zero set is contained in the invariant (\<^term>\<open>measure_zero_inv\<close>)
  and which every discharging step strictly decreases while the invariant
  fails (\<^term>\<open>discharge_progresses\<close>).  This is exactly the ``well-founded
  measure connecting non-invariant states to invariant states via discharging
  events'' that drives convergence; well-foundedness is supplied by the
  natural-number order (\<^term>\<open>measure progress_measure\<close>).

  Together with bounded fairness this yields convergence to the invariant
  within \<^term>\<open>progress_measure s * window\<close> steps from an arbitrary carrier
  state, with \emph{no} assumption that the invariant holds initially.
\<close>

locale converging_composition =
  safety_liveness_composition carrier step ops inv guard schedule discharges window realize
  for carrier :: "'s set"
    and step :: "'s \<Rightarrow> 'op \<Rightarrow> 's option"
    and ops :: "'op set"
    and inv :: "'s \<Rightarrow> bool"
    and guard :: "'s \<Rightarrow> 'op \<Rightarrow> bool"
    and schedule :: "nat \<Rightarrow> 'event"
    and discharges :: "'event \<Rightarrow> bool"
    and window :: "nat"
    and realize :: "'event \<Rightarrow> 's \<Rightarrow> 'op option" +
  fixes progress_measure :: "'s \<Rightarrow> nat"
  assumes discharge_progresses:
      "\<lbrakk> s \<in> carrier; \<not> inv s; discharges ev \<rbrakk>
       \<Longrightarrow> \<exists>opn s'. realize ev s = Some opn \<and> step s opn = Some s'
                   \<and> progress_measure s' < progress_measure s"
begin

text \<open>The zero set of the measure lies inside the invariant --- derived
  rather than assumed: at measure zero a failing invariant would admit a
  discharging step whose target measure lies strictly below zero.\<close>

lemma measure_zero_inv:
  assumes "s \<in> carrier" and "progress_measure s = 0"
  shows "inv s"
proof (rule ccontr)
  assume ninv: "\<not> inv s"
  obtain t where "discharges (schedule t)"
    using live.bounded_occurrence by blast
  then obtain opn s' where "progress_measure s' < progress_measure s"
    using discharge_progresses[OF assms(1) ninv] by blast
  with assms(2) show False by simp
qed

definition convergence_bound :: "'s \<Rightarrow> nat" where
  "convergence_bound s = progress_measure s * window"

text \<open>
  The core convergence lemma, by strong induction on the measure.  From any
  carrier state with measure \<^term>\<open>m\<close>, an invariant state is reached within
  \<^term>\<open>m * window\<close> steps, regardless of the starting time index \<^term>\<open>k\<close>.
\<close>

lemma convergence_bound_reachable:
  "progress_measure s = m \<Longrightarrow> s \<in> carrier
     \<Longrightarrow> \<exists>t \<le> m * window. inv (run_from k s t)"
proof (induction m arbitrary: s k rule: less_induct)
  case (less m)
  show ?case
  proof (cases "inv s")
    case True
    have "inv (run_from k s 0)" using True by simp
    moreover have "(0::nat) \<le> m * window" by simp
    ultimately show ?thesis by blast
  next
    case False
    have m_eq: "progress_measure s = m" using less.prems(1) .
    have car: "s \<in> carrier" using less.prems(2) .
    \<comment> \<open>Locate the least discharging offset within the fairness window.\<close>
    obtain t' where t'1: "k \<le> t'" and t'2: "t' < k + window"
      and t'3: "discharges (schedule t')"
      using live.bounded_occurrence by blast
    define Q where "Q = (\<lambda>j. j < window \<and> discharges (schedule (k + j)))"
    have w: "t' - k < window" using t'1 t'2 by linarith
    have kk: "k + (t' - k) = t'" using t'1 by simp
    have Qwit: "Q (t' - k)" unfolding Q_def using w t'3 kk by simp
    define j0 where "j0 = (LEAST j. Q j)"
    have Qj0: "Q j0" unfolding j0_def using Qwit by (rule LeastI[where P = Q])
    have j0w: "j0 < window" using Qj0 unfolding Q_def by simp
    have disc0: "discharges (schedule (k + j0))" using Qj0 unfolding Q_def by simp
    have before: "\<forall>j<j0. \<not> discharges (schedule (k + j))"
    proof (intro allI impI)
      fix j assume jl: "j < j0"
      have lt: "j < Least Q" using jl by (simp add: j0_def)
      have nQ: "\<not> Q j" using not_less_Least[OF lt] .
      have jw: "j < window" using jl j0w by simp
      show "\<not> discharges (schedule (k + j))" using nQ jw by (simp add: Q_def)
    qed
    have stut: "run_from k s j0 = s" using run_from_stutter[OF before] .
    \<comment> \<open>The discharging step at offset \<^term>\<open>j0\<close> strictly decreases the measure.\<close>
    obtain opn s' where r: "realize (schedule (k + j0)) s = Some opn"
      and st: "step s opn = Some s'"
      and dec: "progress_measure s' < progress_measure s"
      using discharge_progresses[OF car False disc0] by blast
    have op_in: "opn \<in> ops" using realize_discharges[OF car disc0 r] by simp
    have s'_car: "s' \<in> carrier" using safe.step_closed[OF car op_in st] .
    have ev: "run_from k s (Suc j0) = s'"
    proof -
      have "run_from k s (Suc j0) = evolve_step (k + j0) (run_from k s j0)" by simp
      also have "\<dots> = evolve_step (k + j0) s" using stut by simp
      also have "\<dots> = s'" using disc0 r st by (simp add: evolve_step_def)
      finally show ?thesis .
    qed
    have decm: "progress_measure s' < m" using dec m_eq by simp
    \<comment> \<open>Apply the induction hypothesis to the smaller-measure state \<^term>\<open>s'\<close>.\<close>
    have "\<exists>t \<le> progress_measure s' * window. inv (run_from (k + Suc j0) s' t)"
      using less.IH[OF decm refl s'_car] by blast
    then obtain t2 where t2b: "t2 \<le> progress_measure s' * window"
      and inv2: "inv (run_from (k + Suc j0) s' t2)" by blast
    have comp: "run_from k s (Suc j0 + t2) = run_from (k + Suc j0) s' t2"
    proof -
      have "run_from k s (Suc j0 + t2)
              = run_from (k + Suc j0) (run_from k s (Suc j0)) t2"
        by (rule run_from_add)
      also have "\<dots> = run_from (k + Suc j0) s' t2" by (simp only: ev)
      finally show ?thesis .
    qed
    have inv_fin: "inv (run_from k s (Suc j0 + t2))" using comp inv2 by simp
    have "Suc j0 + t2 \<le> window + progress_measure s' * window"
      using j0w t2b by linarith
    also have "\<dots> = (1 + progress_measure s') * window"
      by (simp add: add_mult_distrib)
    also have "\<dots> \<le> m * window"
    proof -
      have "1 + progress_measure s' \<le> m" using decm by linarith
      then show ?thesis by (rule mult_le_mono1)
    qed
    finally have "Suc j0 + t2 \<le> m * window" .
    then show ?thesis using inv_fin by blast
  qed
qed

text \<open>
  Guarded bounded convergence.  From an arbitrary carrier state —
  with no assumption that the invariant holds — the system reaches, within
  \<^term>\<open>convergence_bound s\<close> evolution steps, a state satisfying the invariant.
\<close>

theorem bounded_convergence_from_arbitrary:
  assumes "s \<in> carrier"
  shows "\<exists>t \<le> convergence_bound s. \<exists>s'. evolves_to s t s' \<and> inv s'"
proof -
  obtain t where tb: "t \<le> progress_measure s * window"
    and inv_t: "inv (run_from 0 s t)"
    using convergence_bound_reachable[OF refl assms] by blast
  have "evolves_to s t (run s t)" by (simp add: evolves_to_def)
  with tb inv_t show ?thesis
    by (auto simp: convergence_bound_def run_def evolves_to_def)
qed

end

end
