theory Product_Model_Refutation
  imports "Evidence_Atomic_Binding.Finality_Recovery"
    "Evidence_Atomic_Binding.Finality_Refinement"
begin

section \<open>Recovery must preserve the authoritative result\<close>

abbreviation refutation_call_id :: client_call_id where
  "refutation_call_id \<equiv> (7,1)"

definition refutation_lose_result where
  "refutation_lose_result = call_example_once\<lparr>call_authority_results := (\<lambda>_. None)\<rparr>"

definition refutation_collect_and_complete where
  "refutation_collect_and_complete m = sample.finality_calls.run_calls
    [Collect_Response refutation_call_id call_example_command, Complete_Call refutation_call_id] m"

lemma refutation_mutant_preserves_financial_projection:
  "finality_alpha (call_authority_state refutation_lose_result) =
    finality_alpha (call_authority_state call_example_once)"
  by (simp add: refutation_lose_result_def)

lemma refutation_collector_observes_durable_result:
  "call_completions (refutation_collect_and_complete call_example_once) refutation_call_id =
    Some (Protocol_Response Descendant_Executed)"
  by (simp add: refutation_collect_and_complete_def call_example_once_fields
      sample.finality_calls.collect_client_response_def sample.finality_calls.complete_client_call_def)

lemma refutation_collector_observes_missing_result:
  "call_completions (refutation_collect_and_complete refutation_lose_result) refutation_call_id = None"
  by (simp add: refutation_collect_and_complete_def refutation_lose_result_def call_example_once_fields
      sample.finality_calls.collect_client_response_def sample.finality_calls.complete_client_call_def)

theorem financial_projection_alone_does_not_simulate_collection:
  "finality_alpha (call_authority_state refutation_lose_result) =
     finality_alpha (call_authority_state call_example_once) \<and>
   call_completions (refutation_collect_and_complete refutation_lose_result) refutation_call_id \<noteq>
     call_completions (refutation_collect_and_complete call_example_once) refutation_call_id"
  by (simp only: refutation_mutant_preserves_financial_projection refutation_collector_observes_durable_result
      refutation_collector_observes_missing_result option.distinct simp_thms)

theorem refutation_recovered_endpoint_can_complete:
  "call_completions call_example_after_crash refutation_call_id =
    Some (Protocol_Response Descendant_Executed) \<and>
   completion_ids (call_history call_example_after_crash) = [refutation_call_id] \<and>
   destination_units (machine_state (core_parent (call_authority_state call_example_after_crash)))
     (2,17,4) = 1"
  by (rule crash_recovery_completes_the_old_result_once)

section \<open>Asset separation does not imply exchange\<close>

text \<open>
  The probe includes the replies attributed to each request. An epoch is shared
  even when each action names a different asset. A successful write updates its
  own asset. Rotation updates the shared authorization read by the write.
\<close>

record exchange_probe_state =
  probe_epoch :: nat
  probe_values :: "nat \<Rightarrow> nat"

definition probe_put :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> exchange_probe_state
    \<Rightarrow> exchange_probe_state \<times> bool" where
  "probe_put asset expected value s =
    (if expected = probe_epoch s then (s\<lparr>probe_values := (probe_values s)(asset := value)\<rparr>, True)
     else (s, False))"

definition probe_rotate :: "nat \<Rightarrow> exchange_probe_state \<Rightarrow> exchange_probe_state" where
  "probe_rotate asset s = s\<lparr>probe_epoch := Suc (probe_epoch s)\<rparr>"

definition exchange_probe_initial :: exchange_probe_state where
  "exchange_probe_initial = \<lparr>probe_epoch = 0, probe_values = (\<lambda>_. 0)\<rparr>"

theorem different_assets_do_not_imply_the_same_reply:
  "(1::nat) \<noteq> 2 \<and>
   snd (probe_put 1 0 4 exchange_probe_initial) \<and>
   \<not> snd (probe_put 1 0 4 (probe_rotate 2 exchange_probe_initial)) \<and>
   probe_values (probe_rotate 2 (fst (probe_put 1 0 4 exchange_probe_initial))) 1 = 4 \<and>
   probe_values (fst (probe_put 1 0 4 (probe_rotate 2 exchange_probe_initial))) 1 = 0"
  by (simp add: probe_put_def probe_rotate_def exchange_probe_initial_def)

theorem separate_writes_with_shared_epoch_reads_exchange:
  assumes "a \<noteq> b"
  shows "fst (probe_put b eb vb (fst (probe_put a ea va s))) =
           fst (probe_put a ea va (fst (probe_put b eb vb s))) \<and>
    snd (probe_put a ea va s) = snd (probe_put a ea va (fst (probe_put b eb vb s))) \<and>
    snd (probe_put b eb vb s) = snd (probe_put b eb vb (fst (probe_put a ea va s)))"
  using assms by (simp add: probe_put_def fun_upd_twist split: if_splits)

end
