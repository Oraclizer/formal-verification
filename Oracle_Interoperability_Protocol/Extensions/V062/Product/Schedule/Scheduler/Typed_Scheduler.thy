theory Typed_Scheduler
  imports "OIP_Schedule_Core.Schedule_Core"
begin

datatype 'reply sp_reply = SP_Queue_Result sp_queue_reply | SP_Other_Result 'reply | SP_Maintenance_Refused

definition sp_track_key where
  "sp_track_key key keys = (if key \<in> set keys then keys else keys @ [key])"

definition sp_queue_action where
  "sp_queue_action operation state =
    (let result = sp_step_jobs operation (sp_jobs state); key = sp_cell_key operation
     in (state\<lparr>sp_jobs := fst result,sp_known_keys := sp_track_key key (sp_known_keys state)\<rparr>,
         SP_Queue_Result (snd result)))"

definition sp_execute where
  "sp_execute can_maintain other_step action state =
    (case action of SP_Enqueue_Action token origin \<Rightarrow>
       if \<not> can_maintain token (sp_data state) then (state,SP_Maintenance_Refused)
       else (case map_of (sp_publications state) origin of None \<Rightarrow> (state,SP_Queue_Result (SP_Enqueued None))
         | Some pub \<Rightarrow> sp_queue_action (SP_Enqueue_Cell pub (sp_target state)) state)
     | SP_Dispatch_Action token key \<Rightarrow>
         if can_maintain token (sp_data state) then sp_queue_action (SP_Dispatch_Cell key) state
         else (state,SP_Maintenance_Refused)
     | SP_Fail_Action token key \<Rightarrow>
         if can_maintain token (sp_data state) then sp_queue_action (SP_Fail_Cell key) state
         else (state,SP_Maintenance_Refused)
     | SP_Other_Action other \<Rightarrow> map_prod id SP_Other_Result (other_step other state))"

lemma sp_queue_execution_preserves_current_data_and_publications:
  "sp_data (fst (sp_queue_action operation state)) = sp_data state"
  "sp_publications (fst (sp_queue_action operation state)) = sp_publications state"
  "sp_target (fst (sp_queue_action operation state)) = sp_target state"
  by (simp_all add: sp_queue_action_def Let_def)

lemma sp_queue_run_keeps_every_current_classification:
  "sp_classify can_maintain classify_other action (fst (sp_queue_action operation state)) =
    sp_classify can_maintain classify_other action state"
  by (simp add: sp_queue_action_def sp_queue_rows_do_not_supply_or_rewrite_the_classifier Let_def)

definition sp_reply_put where
  "sp_reply_put index reply rows = (index,reply) # filter (\<lambda>(old,value). old \<noteq> index) rows"

definition sp_swap_indices where
  "sp_swap_indices left order = order[left := order ! Suc left, Suc left := order ! left]"

definition sp_exchange_at where
  "sp_exchange_at require_compatibility can_maintain classify_other events start finish state attempt accum =
    (case attempt of (attempt_index,left) \<Rightarrow> case accum of (order,choices) \<Rightarrow>
      if left < start \<or> Suc left \<ge> finish then (order,choices)
      else let first = sp_classify can_maintain classify_other (snd (events ! (order ! left))) state;
               second = sp_classify can_maintain classify_other (snd (events ! (order ! Suc left))) state
           in if \<not> require_compatibility \<or> sp_compatible first second
              then (sp_swap_indices left order,choices[attempt_index := True]) else (order,choices))"

fun sp_execute_indices where
  "sp_execute_indices can_maintain other_step events [] state replies = (state,replies)"
| "sp_execute_indices can_maintain other_step events (index # rest) state replies =
    (let (label,action) = events ! index; result = sp_execute can_maintain other_step action state
     in sp_execute_indices can_maintain other_step events rest (fst result)
          (sp_reply_put index (label,snd result) replies))"

definition sp_run_end where
  "sp_run_end can_maintain classify_other events order start state =
    (if sp_classify can_maintain classify_other (snd (events ! (order ! start))) state = SP_Serial_Class
     then Suc start
     else start + length (takeWhile (\<lambda>index.
       sp_classify can_maintain classify_other (snd (events ! index)) state \<noteq> SP_Serial_Class) (drop start order)))"

fun sp_schedule_runs where
  "sp_schedule_runs 0 require_compatibility can_maintain classify_other other_step events adjacent order start state choices replies =
    (state,order,choices,replies)"
| "sp_schedule_runs (Suc fuel) require_compatibility can_maintain classify_other other_step events adjacent order start state choices replies =
    (if start \<ge> length order then (state,order,choices,replies)
     else let finish = sp_run_end can_maintain classify_other events order start state;
              changed = fold (sp_exchange_at require_compatibility can_maintain classify_other events start finish state)
                (zip [0..<length adjacent] adjacent) (order,choices);
              execution = sp_execute_indices can_maintain other_step events
                (take (finish - start) (drop start (fst changed))) state replies
          in sp_schedule_runs fuel require_compatibility can_maintain classify_other other_step events adjacent
               (fst changed) finish (fst execution) (snd changed) (snd execution))"

definition sp_valid_plan where
  "sp_valid_plan events adjacent \<longleftrightarrow> distinct (map fst events) \<and>
    list_all (\<lambda>left. Suc left < length events) adjacent"

definition sp_schedule where
  "sp_schedule require_compatibility can_maintain classify_other other_step events adjacent state =
    (if \<not> sp_valid_plan events adjacent then None
     else let (final,order,choices,replies) = sp_schedule_runs (length events) require_compatibility
             can_maintain classify_other other_step events adjacent [0..<length events] 0 state
             (replicate (length adjacent) False) []
          in Some (final,order,choices,map (\<lambda>index. map_of replies index) [0..<length events]))"

lemma sp_invalid_plan_has_no_scheduled_result:
  "\<not> sp_valid_plan events adjacent \<Longrightarrow>
    sp_schedule require_compatibility can_maintain classify_other other_step events adjacent state = None"
  by (simp add: sp_schedule_def)

lemma sp_exchange_guard_never_crosses_the_current_run_boundary:
  assumes "left < start \<or> Suc left \<ge> finish"
  shows "sp_exchange_at flag can_maintain classify_other events start finish state
    (attempt,left) (order,choices) = (order,choices)"
  using assms by (simp add: sp_exchange_at_def)

definition sp_choose_slot_pair where
  "sp_choose_slot_pair require_compatibility requested first second jobs =
    (let exchange = requested \<and> (\<not> require_compatibility \<or>
         sp_compatible (SP_Slot_Class (sp_cell_key first) None) (SP_Slot_Class (sp_cell_key second) None))
     in (exchange,sp_slot_pair exchange first second jobs))"

lemma sp_same_slot_consumer_guard_is_the_only_removed_condition:
  "sp_choose_slot_pair True True (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs =
    (False,sp_slot_pair False (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs)"
  "sp_choose_slot_pair False True (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs =
    (True,sp_slot_pair True (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs)"
  by (simp_all add: sp_choose_slot_pair_def sp_slot_compatibility_is_exact_full_key_inequality Let_def)

theorem sp_phase_free_same_slot_witness_changes_labeled_reply_not_final_slot:
  fixes key :: sp_key and job :: sp_job
  assumes phase: "sp_job_status job \<noteq> Secondary_Completed"
    and bound: "sp_job_attempts job + 2 < 2^64"
  defines "jobs \<equiv> (\<lambda>_. None)(key := Some job)"
  shows "snd (sp_choose_slot_pair True True (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs) \<noteq>
      snd (sp_choose_slot_pair False True (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs)"
    "fst (snd (sp_choose_slot_pair True True (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs)) =
      fst (snd (sp_choose_slot_pair False True (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs))"
proof -
  have core_fact: "sp_slot_pair False (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) ((\<lambda>_. None)(key := Some job)) \<noteq>
      sp_slot_pair True (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) ((\<lambda>_. None)(key := Some job))"
    using sp_same_slot_attempts_are_observable_per_occurrence[OF phase bound, where key=key] .
  have distinct_replies: "sp_slot_pair False (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs \<noteq>
      sp_slot_pair True (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs"
    unfolding jobs_def by (rule core_fact)
  show "snd (sp_choose_slot_pair True True (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs) \<noteq>
      snd (sp_choose_slot_pair False True (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs)"
    using distinct_replies by (simp add: sp_same_slot_consumer_guard_is_the_only_removed_condition)
  show "fst (snd (sp_choose_slot_pair True True (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs)) =
      fst (snd (sp_choose_slot_pair False True (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs))"
    by (simp add: sp_same_slot_consumer_guard_is_the_only_removed_condition sp_slot_pair_def Let_def split_def)
qed

lemma sp_queue_pair_is_the_public_labeled_pair:
  "sp_slot_pair False first second jobs = service_ordered_pair sp_step_jobs first second jobs"
  "sp_slot_pair True first second jobs = service_exchanged_pair sp_step_jobs first second jobs"
  by (simp_all add: sp_slot_pair_def service_ordered_pair_def service_exchanged_pair_def Let_def split_def)

theorem sp_finite_distinct_slot_exchanges_preserve_all_occurrence_replies:
  assumes "rtranclp (verified_adjacent_swap sp_step_jobs (\<lambda>first second state.
      sp_cell_key first \<noteq> sp_cell_key second) initial) original reordered"
  shows "run_occurrences sp_step_jobs original initial (\<lambda>_. None) =
    run_occurrences sp_step_jobs reordered initial (\<lambda>_. None)"
proof (rule finite_adjacent_exchanges_preserve_product_effects_and_replies[OF assms])
  fix first second state
  assume distinct: "sp_cell_key first \<noteq> sp_cell_key second"
  show "service_ordered_pair sp_step_jobs first second state = service_exchanged_pair sp_step_jobs first second state"
    using sp_distinct_slot_pair_keeps_labels_in_original_order[OF distinct, of state]
    by (simp add: sp_queue_pair_is_the_public_labeled_pair)
qed

text \<open>
  This is the typed schedule_at loop: one current-state classification per
  nonserial run, requested swaps on the evolving permutation, and replies
  stored by original index. The other-step/classifier functions are proof
  interfaces, not caller-submitted closures. The fixed executable layer must
  supply closed typed operations, not observed outcomes. Its nonserial
  observations must preserve current data/publication; serial actions begin a
  new run and are revalidated at the reached state. Signed scheduling's extra
  image/reply comparison and confirmed release are separate consumers.
\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sp_queue_run_keeps_every_current_classification
      sp_invalid_plan_has_no_scheduled_result
      sp_exchange_guard_never_crosses_the_current_run_boundary
      sp_same_slot_consumer_guard_is_the_only_removed_condition
      sp_phase_free_same_slot_witness_changes_labeled_reply_not_final_slot
      sp_finite_distinct_slot_exchanges_preserve_all_occurrence_replies})
  then () else error "Unexpected oracle in typed scheduler composition"
\<close>

end
