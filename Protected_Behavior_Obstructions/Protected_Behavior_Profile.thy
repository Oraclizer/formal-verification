theory Protected_Behavior_Profile
  imports Complex_Main
begin

section \<open>Source-quantified protected behavior profiles\<close>

locale protected_profile =
  fixes P :: "'o set"
    and initial :: "'o \<Rightarrow> 'q set"
    and target :: "'o \<Rightarrow> 'q set"
    and hit :: "'q \<Rightarrow> 'o \<Rightarrow> real"
    and first_hit :: "'q \<Rightarrow> 'o \<Rightarrow> 'q \<Rightarrow> real"
    and silent :: "'q \<Rightarrow> 'q \<Rightarrow> bool"
    and closed_trap :: "'q \<Rightarrow> 'o \<Rightarrow> 'q set \<Rightarrow> bool"
  assumes P_nonempty: "P \<noteq> {}"
    and initial_nonempty: "b \<in> P \<Longrightarrow> initial b \<noteq> {}"
    and hit_pos_iff_endpoint:
      "\<lbrakk>b \<in> P; x \<in> initial b\<rbrakk> \<Longrightarrow>
       0 < hit x b \<longleftrightarrow> (\<exists>c. 0 < first_hit x b c)"
    and first_hit_target:
      "0 < first_hit x b c \<Longrightarrow> c \<in> target b"
    and hit_one_iff_no_closed_trap:
      "\<lbrakk>b \<in> P; x \<in> initial b\<rbrakk> \<Longrightarrow>
       hit x b = 1 \<longleftrightarrow> \<not> (\<exists>U. closed_trap x b U)"
begin

definition L0 :: "'o set" where
  "L0 = {b \<in> P. target b \<noteq> {}}"

definition L1 :: "'o set" where
  "L1 = {b \<in> L0. \<exists>x \<in> initial b. 0 < hit x b}"

definition L2 :: "'o set" where
  "L2 = {b \<in> L1. \<forall>x \<in> initial b. hit x b = 1}"

definition endpoint_union_cert :: "'o \<Rightarrow> bool" where
  "endpoint_union_cert b \<longleftrightarrow>
    (\<exists>c0. (\<exists>x \<in> initial b. 0 < first_hit x b c0) \<and>
      (\<forall>x \<in> initial b. \<forall>c. 0 < first_hit x b c \<longrightarrow> silent c c0))"

definition L3 :: "'o set" where
  "L3 = {b \<in> L2. endpoint_union_cert b}"

definition D0 :: "'o set" where "D0 = P - L0"
definition D1 :: "'o set" where "D1 = L0 - L1"
definition D2 :: "'o set" where "D2 = L1 - L2"
definition D3 :: "'o set" where "D3 = L2 - L3"

lemma nested_layers: "L3 \<subseteq> L2 \<and> L2 \<subseteq> L1 \<and> L1 \<subseteq> L0 \<and> L0 \<subseteq> P"
  by (auto simp: L0_def L1_def L2_def L3_def)

lemma T0_partition: "P = D0 \<union> D1 \<union> D2 \<union> D3 \<union> L3"
  using nested_layers by (auto simp: D0_def D1_def D2_def D3_def)

lemma T0_pairwise:
  "pairwise (\<lambda>A B. A \<inter> B = {}) {D0, D1, D2, D3, L3}"
  using nested_layers by (auto simp: pairwise_def D0_def D1_def D2_def D3_def)

lemma T1_empty_fiber: "b \<in> P \<Longrightarrow> (b \<in> D0 \<longleftrightarrow> target b = {})"
  by (auto simp: D0_def L0_def)

lemma T2_positive_endpoint:
  assumes "b \<in> P"
  shows "b \<in> L1 \<longleftrightarrow>
    target b \<noteq> {} \<and> (\<exists>x \<in> initial b. \<exists>c. 0 < first_hit x b c)"
proof
  assume "b \<in> L1"
  then obtain x where bx: "b \<in> P" "target b \<noteq> {}" "x \<in> initial b" "0 < hit x b"
    by (auto simp: L0_def L1_def)
  from hit_pos_iff_endpoint[OF bx(1,3)] bx(4)
  show "target b \<noteq> {} \<and> (\<exists>x \<in> initial b. \<exists>c. 0 < first_hit x b c)"
    using bx by blast
next
  assume rhs: "target b \<noteq> {} \<and> (\<exists>x \<in> initial b. \<exists>c. 0 < first_hit x b c)"
  then obtain x c where xi: "x \<in> initial b" and hc: "0 < first_hit x b c" by blast
  then have hp: "0 < hit x b" using hit_pos_iff_endpoint[OF assms xi] by blast
  have "b \<in> L0" using rhs assms by (auto simp: L0_def)
  with xi hp show "b \<in> L1" by (auto simp: L1_def)
qed

lemma T3_all_sources_no_closed_trap:
  assumes "b \<in> P"
  shows "b \<in> L2 \<longleftrightarrow>
    b \<in> L1 \<and> (\<forall>x \<in> initial b. \<not> (\<exists>U. closed_trap x b U))"
  using hit_one_iff_no_closed_trap[OF assms]
  by (auto simp: L2_def)

lemma T4_endpoint_union:
  "b \<in> L3 \<longleftrightarrow> b \<in> L2 \<and> endpoint_union_cert b"
  by (auto simp: L3_def)

lemma T5_observable_determination:
  assumes det: "\<And>b c d. \<lbrakk>b \<in> P; c \<in> target b; d \<in> target b\<rbrakk> \<Longrightarrow> silent c d"
  shows "L2 = L3"
proof
  show "L2 \<subseteq> L3"
  proof
    fix b assume b2: "b \<in> L2"
    then have bP: "b \<in> P" by (auto simp: L2_def L1_def L0_def)
    from b2 obtain x where xi: "x \<in> initial b" and hp: "0 < hit x b"
      by (auto simp: L2_def L1_def)
    from hit_pos_iff_endpoint[OF bP xi] hp obtain c0 where c0: "0 < first_hit x b c0" by blast
    have cert: "endpoint_union_cert b"
      unfolding endpoint_union_cert_def
    proof (rule exI[of _ c0], rule conjI)
      show "\<exists>x\<in>initial b. 0 < first_hit x b c0" using xi c0 by blast
      show "\<forall>y\<in>initial b. \<forall>c. 0 < first_hit y b c \<longrightarrow> silent c c0"
      proof (intro ballI allI impI)
        fix y c assume yi: "y \<in> initial b" and hc: "0 < first_hit y b c"
        have ct: "c \<in> target b" using first_hit_target[OF hc] .
        have c0t: "c0 \<in> target b" using first_hit_target[OF c0] .
        show "silent c c0" using det[OF bP ct c0t] .
      qed
    qed
    with b2 show "b \<in> L3" by (auto simp: L3_def)
  qed
  show "L3 \<subseteq> L2" by (auto simp: L3_def)
qed

end

end
