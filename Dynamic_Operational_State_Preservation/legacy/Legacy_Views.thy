theory Legacy_Views
  imports DOSP_Degree.Operational_Degree
    DOSP_Recovery.Domain_Recovery
    Cross_Domain_State_Preservation.Hierarchy
    Regulatory_Action_Composition.Regulatory_Action_Composition
begin

definition encode_regulatory_view :: "(reg_state \<Rightarrow> nat) \<Rightarrow> asset_id \<Rightarrow> global_state \<Rightarrow> nat flow_state"
where
  "encode_regulatory_view encode asset gs =
    \<lparr>committed = (\<lambda>d. case get_reg_state gs d asset of None \<Rightarrow> 0 | Some x \<Rightarrow> Suc (encode x)),
      observation_cache = (\<lambda>_. 0)\<rparr>"

lemma hierarchy_forget_projects_to_operational_cells:
  "encode_regulatory_view encode asset (degree_forget d gs) =
    forget_outside (UNIV - {d}) (encode_regulatory_view encode asset gs)"
proof -
  have erased: "get_reg_state (degree_forget d gs) d asset = None"
    by (simp add: get_reg_state_def get_asset_state_def degree_forget_chains)
  show ?thesis
    by (simp add: encode_regulatory_view_def forget_outside_def fun_eq_iff erased degree_forget_reg_eq)
qed

theorem inherited_fixed_asset_naturality_in_operational_view:
  assumes "gs \<in> deg_carrier (Suc k)"
  shows "map_option (encode_regulatory_view encode asset) (deg_run k asset actions (degree_forget (Suc k) gs)) =
    map_option (forget_outside (UNIV - {Suc k}) \<circ> encode_regulatory_view encode asset)
      (deg_run (Suc k) asset actions gs)"
  unfolding degree_forget_natural_run[OF assms]
  by (cases "deg_run (Suc k) asset actions gs") (simp_all add: hierarchy_forget_projects_to_operational_cells)

definition terminal_domains :: "(nat \<Rightarrow> reg_state) \<Rightarrow> nat set" where
  "terminal_domains states = {d. states d = CONFISCATED}"

theorem recovery_and_legacy_legal_word_preserve_terminal_observation:
  assumes "recovery_step grants governance s a result t"
    and "irreversible_facts s = terminal_domains states"
    and "d \<in> terminal_domains states"
  shows "d \<in> irreversible_facts t \<and> run_word legal_word (states d) = CONFISCATED"
proof -
  have "d \<in> irreversible_facts t"
    using assms(2,3) recovery_never_changes_irreversible_facts[OF assms(1)] by simp
  moreover have "states d = CONFISCATED" using assms(3) by (simp add: terminal_domains_def)
  ultimately show ?thesis by (simp add: confiscated_word_absorbing)
qed

end
