theory Recovery_Progress
  imports Operational_Trace_Contracts.Operational_Trace_Contracts
begin

definition accounts_for ::
  "('s \<Rightarrow> 'id set) \<Rightarrow> ('s \<Rightarrow> 'id set) \<Rightarrow>
   (('s, 'a, 'r) transition \<Rightarrow> 'id set) \<Rightarrow>
   (('s, 'a, 'r) transition \<Rightarrow> 'id set) \<Rightarrow>
   ('s, 'a, 'r) transition \<Rightarrow> bool"
where
  "accounts_for pending completed admitted finished e \<longleftrightarrow>
     finite (pending (source_state e)) \<and>
     pending (source_state e) \<inter> completed (source_state e) = {} \<and>
     admitted e \<inter> (pending (source_state e) \<union> completed (source_state e)) = {} \<and>
     finished e \<subseteq> pending (source_state e) \<and>
     pending (target_state e) =
       (pending (source_state e) \<union> admitted e) - finished e \<and>
     completed (target_state e) = completed (source_state e) \<union> finished e"

lemma dosp_tail_order:
  fixes f :: "nat \<Rightarrow> 'a::order"
  assumes step: "\<And>i. start \<le> i \<Longrightarrow> f i \<le> f (Suc i)"
    and tail: "start \<le> i" "i \<le> j"
  shows "f i \<le> f j"
  using tail(2)
proof (induction j)
  case 0
  then show ?case by simp
next
  case (Suc j)
  show ?case
  proof (cases "i \<le> j")
    case True
    then have "f i \<le> f j" by (rule Suc.IH)
    moreover have "f j \<le> f (Suc j)"
      using tail(1) True by (meson le_trans step)
    ultimately show ?thesis by (rule order_trans)
  next
    case False
    with Suc.prems have "i = Suc j" by simp
    then show ?thesis by simp
  qed
qed

theorem eventual_completion_under_finite_interference:
  fixes events :: "nat \<Rightarrow> ('s, 'a, 'r) transition"
    and pending completed :: "'s \<Rightarrow> 'id set"
    and admitted finished :: "('s, 'a, 'r) transition \<Rightarrow> 'id set"
    and interfering :: "('s, 'a, 'r) transition \<Rightarrow> bool"
  assumes run: "infinite_run step initial carrier events"
    and balance: "\<And>i. accounts_for pending completed admitted finished (events i)"
    and admits: "\<And>i. admitted (events i) \<noteq> {} \<Longrightarrow> interfering (events i)"
    and finite_interference: "finite {i. interfering (events i)}"
    and scheduled_repair:
      "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> interfering (events j)) \<Longrightarrow>
       pending (source_state (events i)) \<noteq> {} \<Longrightarrow>
       \<exists>j\<ge>i. finished (events j) \<noteq> {}"
  shows "\<exists>n. \<forall>i\<ge>n.
    pending (source_state (events i)) = {} \<and>
    (\<forall>j\<le>i. pending (source_state (events j)) \<union> completed (source_state (events j))
      \<subseteq> completed (source_state (events i)))"
proof -
  let ?s = "\<lambda>i. source_state (events i)"
  let ?P = "\<lambda>i. pending (?s i)"
  let ?D = "\<lambda>i. completed (?s i)"
  let ?W = "\<lambda>i. ?P i \<union> ?D i"
  let ?R = "\<lambda>i. card (?P i)"
  have linked: "\<And>i. target_state (events i) = ?s (Suc i)"
    using run by (simp add: infinite_run_def)
  have pending_eq: "\<And>i. ?P (Suc i) =
        (?P i \<union> admitted (events i)) - finished (events i)"
    using balance by (simp add: accounts_for_def linked)
  have completed_eq: "\<And>i. ?D (Suc i) = ?D i \<union> finished (events i)"
    using balance by (simp add: accounts_for_def linked)
  have finite_pending: "\<And>i. finite (?P i)"
    using balance by (simp add: accounts_for_def)
  have finished_subset: "\<And>i. finished (events i) \<subseteq> ?P i"
    using balance by (simp add: accounts_for_def)
  have carried: "\<And>i. ?W i \<subseteq> ?W (Suc i)"
    by (auto simp add: pending_eq completed_eq)
  define k where "k = Suc (Max {i. interfering (events i)})"
  have quiet: "\<And>i. k \<le> i \<Longrightarrow> \<not> interfering (events i)"
  proof -
    fix i assume tail: "k \<le> i"
    show "\<not> interfering (events i)"
    proof
      assume "interfering (events i)"
      then have "i \<le> Max {j. interfering (events j)}"
        by (intro Max_ge[OF finite_interference]) simp
      with tail show False by (simp add: k_def)
    qed
  qed
  have no_birth: "\<And>i. k \<le> i \<Longrightarrow> admitted (events i) = {}"
    using admits quiet by blast
  have pending_tail: "\<And>i. k \<le> i \<Longrightarrow> ?P (Suc i) = ?P i - finished (events i)"
    by (simp add: pending_eq no_birth)
  have rank_tail: "\<And>i. k \<le> i \<Longrightarrow> ?R (Suc i) \<le> ?R i"
  proof -
    fix i assume "k \<le> i"
    then have "?P (Suc i) \<subseteq> ?P i" by (simp add: pending_tail)
    then show "?R (Suc i) \<le> ?R i" by (rule card_mono[OF finite_pending])
  qed
  have rank_anti: "\<And>i j. k \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> ?R j \<le> ?R i"
  proof -
    fix i j assume ki: "k \<le> i" and ij: "i \<le> j"
    show "?R j \<le> ?R i"
      using ij
    proof (induction j)
      case 0
      then show ?case by simp
    next
      case (Suc j)
      show ?case
      proof (cases "i \<le> j")
        case True
        then have "?R j \<le> ?R i" by (rule Suc.IH)
        moreover have "?R (Suc j) \<le> ?R j"
          using ki True by (meson le_trans rank_tail)
        ultimately show ?thesis by simp
      next
        case False
        with Suc.prems have "i = Suc j" by simp
        then show ?thesis by simp
      qed
    qed
  qed
  have at_k: "?R k \<in> image ?R {k..}" by simp
  obtain n where n_tail: "k \<le> n" and n_least: "?R n = (LEAST x. x \<in> image ?R {k..})"
    using LeastI[where P="\<lambda>x. x \<in> image ?R {k..}", OF at_k] by auto
  have equal_tail: "\<And>i. n \<le> i \<Longrightarrow> ?R i = ?R n"
  proof -
    fix i assume ni: "n \<le> i"
    have "?R n \<le> ?R i"
      unfolding n_least using n_tail ni by (intro Least_le) auto
    moreover have "?R i \<le> ?R n" by (rule rank_anti[OF n_tail ni])
    ultimately show "?R i = ?R n" by simp
  qed
  have drain: "\<And>i. n \<le> i \<Longrightarrow> ?P i = {}"
  proof -
    fix i assume ni: "n \<le> i"
    show "?P i = {}"
    proof (rule ccontr)
      assume todo: "?P i \<noteq> {}"
      have quiet_i: "\<And>j. i \<le> j \<Longrightarrow> \<not> interfering (events j)"
        using quiet n_tail ni by (meson le_trans)
      obtain j where ij: "i \<le> j" and act: "finished (events j) \<noteq> {}"
        using scheduled_repair[OF quiet_i todo] by blast
      have nj: "n \<le> j" using ni ij by (rule le_trans)
      have ns: "n \<le> Suc j" using nj by simp
      have kj: "k \<le> j" using n_tail ni ij by (meson le_trans)
      have strict: "?P (Suc j) \<subset> ?P j"
        using finished_subset[of j] act by (auto simp add: pending_tail[OF kj])
      have "?R (Suc j) < ?R j" by (rule psubset_card_mono[OF finite_pending strict])
      moreover have "?R (Suc j) = ?R j"
        by (simp only: equal_tail[OF ns] equal_tail[OF nj])
      ultimately show False by simp
    qed
  qed
  have covered_at: "\<And>i j. n \<le> i \<Longrightarrow> j \<le> i \<Longrightarrow> ?W j \<subseteq> ?D i"
  proof -
    fix i j assume ni: "n \<le> i" and ji: "j \<le> i"
    have "?W j \<subseteq> ?W i"
      by (rule dosp_tail_order[where f="?W" and start=0, OF _ zero_le ji]) (rule carried)
    then show "?W j \<subseteq> ?D i" by (simp add: drain[OF ni])
  qed
  show ?thesis using drain covered_at by (intro exI[of _ n]) blast
qed

end
