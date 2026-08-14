theory Protected_Stochastic_Morphism
  imports Protected_Behavior_Profile
begin

section \<open>Set-level qualitative exact morphisms\<close>

definition exact_morphism ::
  "'o set \<Rightarrow> ('o \<Rightarrow> 'q set) \<Rightarrow> ('o \<Rightarrow> 'q set) \<Rightarrow>
   ('q \<Rightarrow> 'q \<Rightarrow> bool) \<Rightarrow>
   'p set \<Rightarrow> ('p \<Rightarrow> 'r set) \<Rightarrow> ('p \<Rightarrow> 'r set) \<Rightarrow>
   ('r \<Rightarrow> 'r \<Rightarrow> bool) \<Rightarrow>
   ('q \<Rightarrow> 'r) \<Rightarrow> ('o \<Rightarrow> 'p) \<Rightarrow> bool" where
  "exact_morphism P I T S P' I' T' S' f g \<longleftrightarrow>
    (\<forall>b. b \<in> P \<longleftrightarrow> g b \<in> P') \<and>
    (\<forall>d \<in> P'. \<exists>b \<in> P. g b = d) \<and>
    (\<forall>b \<in> P. \<forall>x. x \<in> I b \<longleftrightarrow> f x \<in> I' (g b)) \<and>
    (\<forall>b \<in> P. \<forall>y \<in> I' (g b). \<exists>x \<in> I b. f x = y) \<and>
    (\<forall>b \<in> P. \<forall>x. x \<in> T b \<longleftrightarrow> f x \<in> T' (g b)) \<and>
    (\<forall>b \<in> P. \<forall>y \<in> T' (g b). \<exists>x \<in> T b. f x = y) \<and>
    (\<forall>c d. S c d \<longleftrightarrow> S' (f c) (f d))"

lemma exact_morphism_id:
  "exact_morphism P I T S P I T S id id"
  by (auto simp: exact_morphism_def)

lemma exact_morphism_comp:
  assumes F: "exact_morphism P I T S P' I' T' S' f g"
    and G: "exact_morphism P' I' T' S' P'' I'' T'' S'' f' g'"
  shows "exact_morphism P I T S P'' I'' T'' S'' (f' \<circ> f) (g' \<circ> g)"
proof -
  have FP: "\<forall>b. b \<in> P \<longleftrightarrow> g b \<in> P'" and
       FPc: "\<forall>d \<in> P'. \<exists>b \<in> P. g b = d" and
       FI: "\<forall>b \<in> P. \<forall>x. x \<in> I b \<longleftrightarrow> f x \<in> I' (g b)" and
       FIc: "\<forall>b \<in> P. \<forall>y \<in> I' (g b). \<exists>x \<in> I b. f x = y" and
       FT: "\<forall>b \<in> P. \<forall>x. x \<in> T b \<longleftrightarrow> f x \<in> T' (g b)" and
       FTc: "\<forall>b \<in> P. \<forall>y \<in> T' (g b). \<exists>x \<in> T b. f x = y" and
       FS: "\<forall>c d. S c d \<longleftrightarrow> S' (f c) (f d)"
    using F unfolding exact_morphism_def by auto
  have GP: "\<forall>b. b \<in> P' \<longleftrightarrow> g' b \<in> P''" and
       GPc: "\<forall>d \<in> P''. \<exists>b \<in> P'. g' b = d" and
       GI: "\<forall>b \<in> P'. \<forall>x. x \<in> I' b \<longleftrightarrow> f' x \<in> I'' (g' b)" and
       GIc: "\<forall>b \<in> P'. \<forall>y \<in> I'' (g' b). \<exists>x \<in> I' b. f' x = y" and
       GT: "\<forall>b \<in> P'. \<forall>x. x \<in> T' b \<longleftrightarrow> f' x \<in> T'' (g' b)" and
       GTc: "\<forall>b \<in> P'. \<forall>y \<in> T'' (g' b). \<exists>x \<in> T' b. f' x = y" and
       GS: "\<forall>c d. S' c d \<longleftrightarrow> S'' (f' c) (f' d)"
    using G unfolding exact_morphism_def by auto
  show ?thesis
    unfolding exact_morphism_def comp_def
  proof (intro conjI)
    show "\<forall>b. b \<in> P \<longleftrightarrow> g' (g b) \<in> P''" using FP GP by blast
    show "\<forall>d \<in> P''. \<exists>b \<in> P. g' (g b) = d"
    proof (intro ballI)
      fix d assume "d \<in> P''"
      then obtain c where cP: "c \<in> P'" and gc: "g' c = d" using GPc by blast
      then obtain b where bP: "b \<in> P" and gb: "g b = c" using FPc by blast
      show "\<exists>b \<in> P. g' (g b) = d" using bP gb gc by blast
    qed
    show "\<forall>b \<in> P. \<forall>x. x \<in> I b \<longleftrightarrow> f' (f x) \<in> I'' (g' (g b))"
      using FP FI GI by blast
    show "\<forall>b \<in> P. \<forall>y \<in> I'' (g' (g b)). \<exists>x \<in> I b. f' (f x) = y"
    proof (intro ballI allI impI)
      fix b y assume bP: "b \<in> P" and yI: "y \<in> I'' (g' (g b))"
      have gbP: "g b \<in> P'" using FP bP by blast
      obtain z where zI: "z \<in> I' (g b)" and fz: "f' z = y" using GIc gbP yI by blast
      obtain x where xI: "x \<in> I b" and fx: "f x = z" using FIc bP zI by blast
      show "\<exists>x \<in> I b. f' (f x) = y" using xI fx fz by blast
    qed
    show "\<forall>b \<in> P. \<forall>x. x \<in> T b \<longleftrightarrow> f' (f x) \<in> T'' (g' (g b))"
      using FP FT GT by blast
    show "\<forall>b \<in> P. \<forall>y \<in> T'' (g' (g b)). \<exists>x \<in> T b. f' (f x) = y"
    proof (intro ballI allI impI)
      fix b y assume bP: "b \<in> P" and yT: "y \<in> T'' (g' (g b))"
      have gbP: "g b \<in> P'" using FP bP by blast
      obtain z where zT: "z \<in> T' (g b)" and fz: "f' z = y" using GTc gbP yT by blast
      obtain x where xT: "x \<in> T b" and fx: "f x = z" using FTc bP zT by blast
      show "\<exists>x \<in> T b. f' (f x) = y" using xT fx fz by blast
    qed
    show "\<forall>c d. S c d \<longleftrightarrow> S'' (f' (f c)) (f' (f d))"
      using FS GS by blast
  qed
qed

definition profile_LE :: "(nat \<Rightarrow> 'v \<Rightarrow> 'o set) \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "profile_LE cuts i j \<longleftrightarrow> (\<forall>k<4. cuts k i \<subseteq> cuts k j)"

definition profile_LT :: "(nat \<Rightarrow> 'v \<Rightarrow> 'o set) \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "profile_LT cuts i j \<longleftrightarrow>
    profile_LE cuts i j \<and> (\<exists>k<4. cuts k i \<subseteq> cuts k j \<and> \<not> cuts k j \<subseteq> cuts k i)"

lemma profile_LE_refl: "profile_LE cuts i i"
  by (auto simp: profile_LE_def)

lemma profile_LE_trans:
  "\<lbrakk>profile_LE cuts i j; profile_LE cuts j k\<rbrakk> \<Longrightarrow> profile_LE cuts i k"
  by (auto simp: profile_LE_def)

lemma profile_correspondence:
  assumes exact: "\<And>n b. n < 4 \<Longrightarrow> (b \<in> cutA n i \<longleftrightarrow> g b \<in> cutB n j)"
  shows "\<forall>n<4. g ` (cutA n i) = cutB n j \<inter> range g"
  using exact by auto

end
