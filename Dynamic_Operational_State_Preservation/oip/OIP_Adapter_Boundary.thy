theory OIP_Adapter_Boundary
  imports OIP_Successor_Fact
begin

definition successor_source_check :: "'src set \<Rightarrow> 'src set \<Rightarrow> bool" where
  "successor_source_check old new \<longleftrightarrow> \<not> successor_requires_same_sources \<or> old = new"

lemma distinct_members_have_distinct_source_sets:
  "\<lbrakk>inj project; X \<noteq> Y\<rbrakk> \<Longrightarrow> image project X \<noteq> image project Y"
  by (meson inj_image_eq_iff)

theorem direct_membership_projection_rejects_dynamic_join:
  assumes "inj project"
    "recovery_step grants governance s (Activate (Join_Domain d job) epoch boundary root_time)
      (Accepted (Joined d job)) t"
  shows "\<not> successor_source_check (image project (active_domains s)) (image project (active_domains t))"
proof -
  have "active_domains s \<noteq> active_domains t"
    using assms(2) by (cases rule: recovery_step.cases) auto
  then show ?thesis
    using distinct_members_have_distinct_source_sets[OF assms(1)]
    by (simp add: successor_source_check_def successor_requires_same_sources_def)
qed

theorem direct_membership_projection_rejects_dynamic_leave:
  assumes "inj project"
    "recovery_step grants governance s (Activate (Leave_Domain d receiver) epoch boundary root_time)
      (Accepted (Left d receiver)) t"
  shows "\<not> successor_source_check (image project (active_domains s)) (image project (active_domains t))"
proof -
  have "active_domains s \<noteq> active_domains t"
    using assms(2) by (cases rule: recovery_step.cases) auto
  then show ?thesis
    using distinct_members_have_distinct_source_sets[OF assms(1)]
    by (simp add: successor_source_check_def successor_requires_same_sources_def)
qed

end
