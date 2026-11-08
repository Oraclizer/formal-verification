theory Reference_Read_Cuts
  imports "OIP_Product.Reads_Cache"
begin

record 'projection reference_read_history =
  reference_history_epoch :: nat
  reference_history_prefixes :: "'projection list"

definition initialize_reference_history where
  "initialize_reference_history epoch initial =
    \<lparr>reference_history_epoch = epoch, reference_history_prefixes = [initial]\<rparr>"

definition reference_observed_cut where
  "reference_observed_cut history =
    \<lparr>cut_authority_epoch = reference_history_epoch history,
     cut_revision = length (reference_history_prefixes history) - 1\<rparr>"

definition record_reference_advance where
  "record_reference_advance epoch steps snapshot history =
    (if steps = 0 then history else history\<lparr>reference_history_epoch := epoch,
       reference_history_prefixes := reference_history_prefixes history @ replicate steps snapshot\<rparr>)"

definition current_reference_observation where
  "current_reference_observation authorized read expected history =
    (if authorized \<and> expected = reference_observed_cut history \<and> reference_history_prefixes history \<noteq> []
     then Some (expected, read (last (reference_history_prefixes history))) else None)"

definition historical_reference_observation where
  "historical_reference_observation authorized read revision history =
    (if authorized \<and> revision < length (reference_history_prefixes history)
     then Some (revision, read (reference_history_prefixes history ! revision)) else None)"

lemma an_effectless_record_does_not_advance_the_ledger_read_cut:
  "record_reference_advance epoch 0 snapshot history = history"
  by (simp add: record_reference_advance_def)

lemma an_accepted_batch_advances_by_its_number_of_contexts:
  assumes "reference_history_prefixes history \<noteq> []" "0 < steps"
  shows "cut_revision (reference_observed_cut (record_reference_advance epoch steps snapshot history)) =
    cut_revision (reference_observed_cut history) + steps"
  using assms
  by (cases "reference_history_prefixes history"; cases steps)
     (simp_all add: reference_observed_cut_def record_reference_advance_def add.assoc)

lemma recording_an_advance_preserves_each_exact_prior_observation:
  assumes "revision < length (reference_history_prefixes history)"
  shows "historical_reference_observation authorized read revision (record_reference_advance epoch steps snapshot history) =
    historical_reference_observation authorized read revision history"
  using assms by (cases steps) (simp_all add: record_reference_advance_def historical_reference_observation_def nth_append)

lemma every_position_of_one_installed_batch_has_the_same_snapshot:
  assumes "index < steps"
  shows "historical_reference_observation True read (length (reference_history_prefixes history) + index)
      (record_reference_advance epoch steps snapshot history) =
    Some (length (reference_history_prefixes history) + index, read snapshot)"
proof -
  have nonzero: "steps \<noteq> 0" using assms by arith
  show ?thesis using assms nonzero
    by (simp add: record_reference_advance_def historical_reference_observation_def nth_append nth_replicate)
qed

lemma an_authorized_current_reply_consumes_its_exact_ledger_cut:
  assumes "current_reference_observation authorized read expected history = Some (actual, value)"
  shows "authorized \<and> actual = expected \<and> actual = reference_observed_cut history \<and>
    value = read (last (reference_history_prefixes history))"
  using assms by (auto simp: current_reference_observation_def split: if_splits)

lemma an_unchanged_value_does_not_keep_an_older_current_cut_valid:
  fixes read before after epoch snapshot
  defines "before \<equiv> initialize_reference_history epoch snapshot"
    and "after \<equiv> record_reference_advance epoch 1 snapshot before"
  shows "historical_reference_observation True read 0 after = Some (0, read snapshot)"
    "historical_reference_observation True read 1 after = Some (1, read snapshot)"
    "current_reference_observation True read (reference_observed_cut before) after = None"
  by (simp_all add: before_def after_def initialize_reference_history_def record_reference_advance_def
      historical_reference_observation_def current_reference_observation_def reference_observed_cut_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms an_effectless_record_does_not_advance_the_ledger_read_cut
      an_accepted_batch_advances_by_its_number_of_contexts recording_an_advance_preserves_each_exact_prior_observation
      every_position_of_one_installed_batch_has_the_same_snapshot an_authorized_current_reply_consumes_its_exact_ledger_cut
      an_unchanged_value_does_not_keep_an_older_current_cut_valid})
  then () else error "Unexpected oracle in exact reference read history"
\<close>

end
