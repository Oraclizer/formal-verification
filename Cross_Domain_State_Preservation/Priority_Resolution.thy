(*
  Title:      Cross_Domain_State_Preservation/Priority_Resolution.thy
  Author:     Jinwook Kim (Jay) <jay@oraclizer.io>
  Maintainer: Jinwook Kim (Jay) <jay@oraclizer.io>
  License:    BSD

  Priority Resolution and Liveness — Generic Theory

  This theory defines generic locales for priority-based deterministic
  selection and starvation freedom under fair leader scheduling. These
  are reusable, domain-independent abstractions for the order- and
  bound-theoretic content of these two liveness concerns: a total order
  on priorities yields a deterministic choice, and a fairness bound
  yields bounded progress. The locales are stated over abstract carriers;
  they do not themselves model concurrent execution, message interleaving,
  or network failure, and the synchronization model underlying their
  instantiation (Regulatory_Instance.thy, instantiated in
  DQuencer_Instance.thy) is atomic.

  Each concern — deterministic ordering and bounded-fairness progress —
  is captured by a minimal locale with clean assumptions, enabling
  domain-independent proofs that any conforming system can instantiate.

  This theory is domain-independent. The D-quencer regulatory consensus
  in DQuencer_Instance.thy provides a concrete instantiation of both
  locales, but they apply to any system with linearly ordered
  priorities and periodic honest leader scheduling.

  Methodological lineage:
    State_Preservation.thy in this entry abstracts cross-domain state
    preservation into composable locales. This theory follows the same
    methodology on the liveness side, providing the order- and
    bound-theoretic abstractions intended to support a future lift of the
    atomic-sync model toward a partially synchronous, fault-tolerant
    deployment (left to subsequent entries).
*)

theory Priority_Resolution
  imports Main
begin

section \<open>Priority-Based Deterministic Selection\<close>

text \<open>
  A system where messages carry priorities from a linear order.
  Given a finite non-empty set of messages with injective priorities,
  there exists a unique highest-priority message, and selection is
  deterministic.

  The injectivity assumption models tiebreaking: in practice, a
  composite key (e.g., authority level, timestamp, severity, node ID)
  ensures no two distinct messages share the same priority.
\<close>

locale priority_system =
  fixes priority :: "'m \<Rightarrow> 'k::linorder"
  assumes priority_injective:
    "\<lbrakk> priority m1 = priority m2 \<rbrakk> \<Longrightarrow> m1 = m2"
begin

text \<open>
  In a finite non-empty set with injective priorities, there exists
  a unique element with the maximum priority.
\<close>

lemma highest_priority_exists:
  assumes "finite S" and "S \<noteq> {}"
  shows "\<exists>!m. m \<in> S \<and> (\<forall>m' \<in> S. priority m' \<le> priority m)"
proof -
  have fin_img: "finite (priority ` S)" using assms(1) by simp
  have ne_img: "priority ` S \<noteq> {}" using assms(2) by simp
  obtain m where m_in: "m \<in> S" and m_pri: "priority m = Max (priority ` S)"
    using Max_in[OF fin_img ne_img] by auto
  have m_max: "\<forall>m' \<in> S. priority m' \<le> priority m"
  proof
    fix m' assume "m' \<in> S"
    hence "priority m' \<in> priority ` S" by simp
    hence "priority m' \<le> Max (priority ` S)" using Max_ge[OF fin_img] by simp
    thus "priority m' \<le> priority m" using m_pri by simp
  qed
  show ?thesis
  proof (rule ex1I[of _ m])
    show "m \<in> S \<and> (\<forall>m' \<in> S. priority m' \<le> priority m)"
      using m_in m_max by auto
  next
    fix m2 assume "m2 \<in> S \<and> (\<forall>m' \<in> S. priority m' \<le> priority m2)"
    then have m2_in: "m2 \<in> S" and m2_max: "\<forall>m' \<in> S. priority m' \<le> priority m2" by auto
    from m_max m2_in have "priority m2 \<le> priority m" by auto
    from m2_max m_in have "priority m \<le> priority m2" by auto
    then have "priority m = priority m2" using \<open>priority m2 \<le> priority m\<close> by auto
    then show "m2 = m" using priority_injective by auto
  qed
qed

definition select_highest :: "'m set \<Rightarrow> 'm option" where
  "select_highest S =
    (if S = {} then None
     else Some (THE m. m \<in> S \<and> (\<forall>m' \<in> S. priority m' \<le> priority m)))"

theorem select_highest_deterministic:
  assumes ne: "S \<noteq> {}"
  shows "\<exists>!m. select_highest S = Some m"
proof -
  from ne obtain v where hv: "select_highest S = Some v"
    unfolding select_highest_def by simp
  show ?thesis
  proof (rule ex1I[of _ v])
    show "select_highest S = Some v" by (rule hv)
  next
    fix w assume "select_highest S = Some w"
    with hv show "w = v" by simp
  qed
qed

theorem select_highest_in_set:
  assumes fin: "finite S" and sel: "select_highest S = Some m"
  shows "m \<in> S"
proof -
  from sel have ne: "S \<noteq> {}"
    unfolding select_highest_def by (simp split: if_splits)
  from highest_priority_exists[OF fin ne] have uniq:
    "\<exists>!x. x \<in> S \<and> (\<forall>m' \<in> S. priority m' \<le> priority x)" .
  from theI'[OF uniq] have the_in:
    "(THE x. x \<in> S \<and> (\<forall>m' \<in> S. priority m' \<le> priority x)) \<in> S" by auto
  from sel ne have "m = (THE x. x \<in> S \<and> (\<forall>m' \<in> S. priority m' \<le> priority x))"
    unfolding select_highest_def by simp
  with the_in show ?thesis by simp
qed

theorem select_highest_is_max:
  assumes fin: "finite S" and ne: "S \<noteq> {}" and sel: "select_highest S = Some m"
  shows "\<forall>m' \<in> S. priority m' \<le> priority m"
proof -
  from highest_priority_exists[OF fin ne] have uniq:
    "\<exists>!x. x \<in> S \<and> (\<forall>m' \<in> S. priority m' \<le> priority x)" .
  from theI'[OF uniq] have the_max:
    "\<forall>m' \<in> S. priority m' \<le>
      priority (THE x. x \<in> S \<and> (\<forall>m' \<in> S. priority m' \<le> priority x))"
    by auto
  from sel ne have "m = (THE x. x \<in> S \<and> (\<forall>m' \<in> S. priority m' \<le> priority x))"
    unfolding select_highest_def by simp
  with the_max show ?thesis by simp
qed

end


section \<open>Fair Leader Starvation Freedom\<close>

text \<open>
  A leader-based system where an honest leader always processes at
  least one pending request, and a fairness assumption guarantees
  that honest leaders appear periodically.

  The fairness assumption is a sufficient condition that abstracts
  over the probabilistic guarantees of VRF-based leader election.
  Under \<^term>\<open>f < n/3\<close> Byzantine faults, the probability that a
  Byzantine leader is elected k consecutive times is \<^term>\<open>(f/n)^k\<close>,
  which decreases exponentially. The fairness bound k captures this
  as a deterministic assumption.

  The key theorem: under the fairness assumption, any pending request
  is processed within a bounded number of epochs.
\<close>

locale fair_leader_system =
  fixes leader_at :: "nat \<Rightarrow> 'n"
    and is_honest :: "'n \<Rightarrow> bool"
    and pending :: "nat \<Rightarrow> nat"
    and fairness_bound :: nat
  assumes fair_leader:
      "\<forall>epoch. \<exists>e. epoch \<le> e \<and> e < epoch + fairness_bound \<and> is_honest (leader_at e)"
    and honest_progress:
      "\<lbrakk> is_honest (leader_at e); pending e > 0 \<rbrakk> \<Longrightarrow> pending (Suc e) < pending e"
    and non_honest_bounded:
      "pending (Suc e) \<le> pending e"
begin

text \<open>Positivity of the fairness bound is implied by fairness itself: the
  window starting at any epoch must be non-empty to contain an honest slot.
  It is therefore derived rather than assumed.\<close>

lemma fairness_bound_positive: "fairness_bound > 0"
proof -
  obtain e where "(0::nat) \<le> e" and "e < 0 + fairness_bound"
    using fair_leader by blast
  then show ?thesis by simp
qed

text \<open>
  Pending count is monotonically non-increasing.
\<close>

lemma pending_monotone:
  assumes "e1 \<le> e2"
  shows "pending e2 \<le> pending e1"
  using assms
proof (induction rule: inc_induct)
  case base
  then show ?case by simp
next
  case (step e)
  have "pending e2 \<le> pending (Suc e)" by (rule step.IH)
  also have "pending (Suc e) \<le> pending e" using non_honest_bounded by auto
  finally show ?case .
qed

text \<open>
  If there are pending requests, within \<^term>\<open>fairness_bound\<close> epochs
  at least one will be processed (the pending count strictly decreases).
\<close>

theorem starvation_bound:
  assumes pos: "pending epoch > 0"
  shows "\<exists>e. epoch \<le> e \<and> e < epoch + fairness_bound \<and> pending (Suc e) < pending e"
proof -
  from fair_leader obtain h where
    h_range: "epoch \<le> h" "h < epoch + fairness_bound" and
    h_honest: "is_honest (leader_at h)"
    by auto
  show ?thesis
  proof (cases "pending h > 0")
    case True
    with h_honest have "pending (Suc h) < pending h" using honest_progress by auto
    with h_range show ?thesis by auto
  next
    case False
    then have ph0: "pending h = 0" by simp
    \<comment> \<open>pending dropped from >0 (at epoch) to 0 (at h): find a strict decrease step\<close>
    have key: "\<forall>n. 0 < n \<longrightarrow> pending (epoch + n) = 0 \<longrightarrow>
        (\<exists>e. epoch \<le> e \<and> e < epoch + n \<and> pending (Suc e) < pending e)"
    proof (rule allI)
      fix n
      show "0 < n \<longrightarrow> pending (epoch + n) = 0 \<longrightarrow>
          (\<exists>e. epoch \<le> e \<and> e < epoch + n \<and> pending (Suc e) < pending e)"
      proof (induction n)
        case 0 show ?case by simp
      next
        case (Suc k)
        show ?case
        proof (intro impI)
          assume hpk: "pending (epoch + Suc k) = 0"
          show "\<exists>e. epoch \<le> e \<and> e < epoch + Suc k \<and> pending (Suc e) < pending e"
          proof (cases "k = 0")
            case True
            from hpk True have "pending (Suc epoch) < pending epoch" using pos by simp
            thus ?thesis by (intro exI[of _ epoch]) auto
          next
            case False
            then have kpos: "0 < k" by simp
            show ?thesis
            proof (cases "pending (epoch + k) = 0")
              case True
              then have pk0: "pending (epoch + k) = 0" .
              from Suc.IH[THEN mp, OF kpos, THEN mp, OF pk0]
              obtain e' where "epoch \<le> e'" "e' < epoch + k" "pending (Suc e') < pending e'"
                by auto
              thus ?thesis by auto
            next
              case False
              from False hpk have "pending (epoch + Suc k) < pending (epoch + k)" by simp
              thus ?thesis by (intro exI[of _ "epoch + k"]) auto
            qed
          qed
        qed
      qed
    qed
    have dpos: "0 < h - epoch"
    proof -
      have "h \<noteq> epoch" using ph0 pos by auto
      with h_range(1) show ?thesis by arith
    qed
    have pd: "pending (epoch + (h - epoch)) = 0"
    proof -
      have "epoch + (h - epoch) = h" using h_range(1) by arith
      with ph0 show ?thesis by simp
    qed
    from key[rule_format, OF dpos, OF pd]
    obtain e' where he': "epoch \<le> e'" "e' < epoch + (h - epoch)" "pending (Suc e') < pending e'"
      by auto
    have "epoch + (h - epoch) \<le> h" using h_range(1) by arith
    with he' h_range(2) show ?thesis by auto
  qed
qed

text \<open>
  Corollary: all pending requests are eventually processed.
  By induction on the pending count (which is a natural number
  and thus a well-founded decreasing measure), repeated application
  of \<^verbatim>\<open>starvation_bound\<close> drives the count to zero.
\<close>

theorem eventual_completion:
  shows "\<exists>e_final. pending e_final = 0"
proof -
  define P where
    "P n \<equiv> \<forall>epoch. pending epoch = n \<longrightarrow> (\<exists>e_final. pending e_final = 0)"
    for n :: nat
  have all_P: "\<And>n. P n"
  proof -
    fix n show "P n"
      unfolding P_def
    proof (induction n rule: less_induct)
      case (less n)
      show "\<forall>epoch. pending epoch = n \<longrightarrow> (\<exists>e_final. pending e_final = 0)"
      proof (intro allI impI)
        fix epoch assume eq: "pending epoch = n"
        show "\<exists>e_final. pending e_final = 0"
        proof (cases "n = 0")
          case True thus ?thesis using eq by auto
        next
          case False
          have pos: "pending epoch > 0" using eq False by auto
          from starvation_bound[OF pos] obtain e where
            e_ge: "epoch \<le> e" and e_dec: "pending (Suc e) < pending e"
            by auto
          have lt: "pending (Suc e) < n"
            using pending_monotone[OF e_ge] eq e_dec by simp
          from less.IH[OF lt] show ?thesis
            unfolding P_def by blast
        qed
      qed
    qed
  qed
  from all_P[of "pending 0"] show ?thesis
    unfolding P_def by blast
qed

end

end
