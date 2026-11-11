theory Wire_Code_Finite_Maps
  imports Wire_Code_Funded_Source_Projection
begin

definition code_finite_delete :: "'key \<Rightarrow> ('key \<times> 'cell) list \<Rightarrow> ('key \<times> 'cell) list" where
  "code_finite_delete key rows = filter (\<lambda>entry. fst entry \<noteq> key) rows"

definition code_finite_put :: "'key \<Rightarrow> 'cell \<Rightarrow> ('key \<times> 'cell) list \<Rightarrow> ('key \<times> 'cell) list" where
  "code_finite_put key cell rows = (key,cell) # code_finite_delete key rows"

definition code_finite_alter :: "'key \<Rightarrow> ('cell \<Rightarrow> 'cell) \<Rightarrow> ('key \<times> 'cell) list \<Rightarrow> ('key \<times> 'cell) list" where
  "code_finite_alter key change rows =
    (case map_of rows key of None \<Rightarrow> rows | Some old \<Rightarrow> code_finite_put key (change old) rows)"

definition code_finite_nat_default :: "('key \<times> nat) list \<Rightarrow> 'key \<Rightarrow> nat" where
  "code_finite_nat_default rows key = (case map_of rows key of None \<Rightarrow> 0 | Some cell \<Rightarrow> cell)"

lemma finite_delete_is_exactly_a_total_map_none_update:
  "map_of (code_finite_delete key rows) = (map_of rows)(key := None)"
  by (rule ext; induction rows) (auto simp: code_finite_delete_def fun_upd_def split: prod.splits)

lemma finite_put_is_exactly_a_total_map_some_update:
  "map_of (code_finite_put key cell rows) = (map_of rows)(key := Some cell)"
  by (simp add: code_finite_put_def finite_delete_is_exactly_a_total_map_none_update)

lemma finite_alter_preserves_absence_and_changes_only_the_selected_value:
  "map_of (code_finite_alter key change rows) = (map_of rows)(key := map_option change (map_of rows key))"
  by (cases "map_of rows key")
     (auto simp: code_finite_alter_def finite_put_is_exactly_a_total_map_some_update fun_eq_iff)

lemma finite_zero_default_put_is_the_exact_frozen_nat_function_update:
  "code_finite_nat_default (code_finite_put key cell rows) = (code_finite_nat_default rows)(key := cell)"
  by (rule ext)
     (auto simp: code_finite_nat_default_def finite_put_is_exactly_a_total_map_some_update
       split: option.splits if_splits)

lemma an_absent_finite_nat_entry_has_the_explicit_zero_default:
  "map_of rows key = None \<Longrightarrow> code_finite_nat_default rows key = 0"
  by (simp add: code_finite_nat_default_def)

text \<open>
  Interpretation uses map_of's first-row lookup. Native BTreeMap input must
  supply distinct keys; no duplicate-key source configuration is admitted
  merely because the HOL interpretation is total. The update equalities
  hold even before that source-domain restriction. None is the option-map
  default, and zero is the financial natural-function default. Sparse zero
  rows need not make the representation injective.
\<close>

end
