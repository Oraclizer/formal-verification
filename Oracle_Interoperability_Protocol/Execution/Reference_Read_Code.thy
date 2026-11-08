theory Reference_Read_Code
  imports "OIP_Reference_Profile.Reference_Cache_Consumption"
begin

definition native_resize_read_prefixes where
  "native_resize_read_prefixes revision snapshot prefixes =
    (if revision < length prefixes then prefixes
     else prefixes @ replicate (Suc revision - length prefixes) snapshot)"

definition native_read_history_related where
  "native_read_history_related epoch revision prefixes model \<longleftrightarrow>
    prefixes \<noteq> [] \<and> length prefixes = Suc revision \<and>
    reference_history_epoch model = epoch \<and> reference_history_prefixes model = prefixes"

theorem recording_a_native_ledger_change_matches_the_reference_read_history:
  assumes related: "native_read_history_related epoch revision prefixes model"
    and positive: "steps > 0"
  shows "native_read_history_related next_epoch (revision + steps)
     (native_resize_read_prefixes (revision + steps) snapshot prefixes)
     (record_reference_advance next_epoch steps snapshot model)"
proof -
  have length: "length prefixes = Suc revision" using related by (simp add: native_read_history_related_def)
  have bound: "\<not> revision + steps < length prefixes" using length positive by arith
  show ?thesis using related positive bound
    by (simp add: native_read_history_related_def native_resize_read_prefixes_def record_reference_advance_def)
qed

lemma an_effectless_native_record_keeps_the_exact_reference_history:
  assumes "native_read_history_related epoch revision prefixes model"
  shows "native_read_history_related epoch revision
      (native_resize_read_prefixes revision snapshot prefixes)
      (record_reference_advance epoch 0 snapshot model)"
  using assms by (simp add: native_read_history_related_def native_resize_read_prefixes_def record_reference_advance_def)

definition native_current_read_value where
  "native_current_read_value permitted read expected epoch revision prefixes =
    (if permitted \<and> cut_authority_epoch expected = epoch \<and> cut_revision expected = revision \<and> prefixes \<noteq> []
     then Some (expected, read (last prefixes)) else None)"

definition native_history_read_value where
  "native_history_read_value permitted read position prefixes =
    (if permitted \<and> position < length prefixes
     then Some (position, read (prefixes ! position)) else None)"

theorem the_native_cut_and_its_selected_prefixes_give_the_same_model_values:
  assumes related: "native_read_history_related epoch revision prefixes model"
  shows "native_current_read_value permitted read expected epoch revision prefixes =
      current_reference_observation permitted read expected model"
    "native_history_read_value permitted read position prefixes =
      historical_reference_observation permitted read position model"
proof -
  have cut: "reference_observed_cut model = \<lparr>cut_authority_epoch = epoch, cut_revision = revision\<rparr>"
    using related by (simp add: reference_observed_cut_def native_read_history_related_def)
  show "native_current_read_value permitted read expected epoch revision prefixes =
      current_reference_observation permitted read expected model"
    using related by (cases expected) (simp add: native_current_read_value_def current_reference_observation_def cut
      native_read_history_related_def)
  show "native_history_read_value permitted read position prefixes =
      historical_reference_observation permitted read position model"
    using related by (simp add: native_history_read_value_def historical_reference_observation_def native_read_history_related_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms recording_a_native_ledger_change_matches_the_reference_read_history
      an_effectless_native_record_keeps_the_exact_reference_history the_native_cut_and_its_selected_prefixes_give_the_same_model_values})
  then () else error "Unexpected oracle in reference read code"
\<close>

end
