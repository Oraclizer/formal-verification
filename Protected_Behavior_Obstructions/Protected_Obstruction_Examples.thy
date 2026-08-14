theory Protected_Obstruction_Examples
  imports Protected_Stochastic_Morphism "HOL.Nitpick"
begin

section \<open>Finite witnesses and bounded mutation models\<close>

datatype q2 = Source2 | Hit2 | Trap2
datatype q3 = Source3 | Left3 | Right3

definition m2_hit :: "q2 \<Rightarrow> real" where
  "m2_hit q = (if q = Source2 then 1/2 else if q = Hit2 then 1 else 0)"

definition m3_first :: "q3 \<Rightarrow> real" where
  "m3_first q = (if q = Left3 \<or> q = Right3 then 1/2 else 0)"

lemma M2_positive_not_almost_sure:
  "0 < m2_hit Source2 \<and> m2_hit Source2 \<noteq> 1"
  by (simp add: m2_hit_def)

lemma M3_two_positive_endpoints:
  "0 < m3_first Left3 \<and> 0 < m3_first Right3 \<and> Left3 \<noteq> Right3"
  by (simp add: m3_first_def)

lemma quotient_coarsening_countermodel:
  "\<exists>S :: q3 \<Rightarrow> q3 \<Rightarrow> bool.
      S Left3 Right3 \<and> Left3 \<noteq> Right3"
  nitpick [satisfy, expect = genuine]
  by (rule exI[of _ "\<lambda>_ _. True"], simp)

lemma initial_coverage_countermodel:
  "\<exists>(I :: bool set) (J :: bool set) (f :: bool \<Rightarrow> bool).
      (\<forall>x. x \<in> I \<longrightarrow> f x \<in> J) \<and>
      (\<exists>y \<in> J. y \<notin> f ` I)"
  nitpick [satisfy, expect = genuine]
  by (rule exI[of _ "{False}"], rule exI[of _ UNIV], rule exI[of _ id], auto)

lemma initial_reflection_countermodel:
  "\<exists>(I :: bool set) (J :: bool set) (f :: bool \<Rightarrow> bool).
      f ` I \<subseteq> J \<and> (\<exists>x. f x \<in> J \<and> x \<notin> I)"
  nitpick [satisfy, expect = genuine]
  by (rule exI[of _ "{False}"], rule exI[of _ UNIV], rule exI[of _ id], auto)

lemma one_step_composition_countermodel:
  "\<exists>r :: nat \<Rightarrow> nat \<Rightarrow> bool.
      r 0 1 \<and> r 1 2 \<and> \<not> r 0 2"
  nitpick [satisfy, card nat = 3, expect = genuine]
  by (rule exI[of _ "\<lambda>x y. (x = 0 \<and> y = 1) \<or> (x = 1 \<and> y = 2)"], simp)

lemma zero_weight_breaks_full_support_packaging:
  fixes p :: "bool \<Rightarrow> real"
  assumes "p False = 1" "p True = 0"
  shows "(\<exists>x. 0 < p x) \<and>
    (\<Sum>x\<in>UNIV. (if x then 1 else 0) * p x) = 0"
proof -
  have hex: "\<exists>x. 0 < p x"
  proof
    show "0 < p False" using assms(1) by simp
  qed
  have hsum: "(\<Sum>x\<in>UNIV. (if x then 1 else 0) * p x) = 0"
    using assms by (simp add: UNIV_bool)
  show ?thesis using hex hsum by blast
qed

end
