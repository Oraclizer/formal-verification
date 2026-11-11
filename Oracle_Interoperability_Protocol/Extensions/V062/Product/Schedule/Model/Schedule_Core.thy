theory Schedule_Core
  imports "OIP_Reference_Execution.Reference_Typed_Schedule_Operands"
    "OIP_Reference_Profile.Reference_Wire_Schedule_Classifier"
    "OIP_Product.Parallel_Trace"
begin

type_synonym sp_key = "source_key \<times> nat \<times> nat"

record sp_publication =
  sp_publication_model :: product_publication
  sp_publication_commit_epoch :: nat
  sp_publication_owner :: nat

definition sp_key_of where
  "sp_key_of pub = (publication_origin (sp_publication_model pub),sp_publication_commit_epoch pub,
    origin_commit_position (publication_decision (sp_publication_model pub)))"

definition sp_abstract_key where
  "sp_abstract_key key = (case key of (sp_origin,sp_epoch,sp_position) \<Rightarrow> (sp_origin,sp_position))"

record sp_job =
  sp_job_publication :: sp_publication
  sp_job_target :: nat
  sp_job_attempts :: nat
  sp_job_status :: secondary_status

definition sp_model_job where
  "sp_model_job job = \<lparr>secondary_publication = sp_publication_model (sp_job_publication job),
    secondary_target = sp_job_target job,secondary_attempts = sp_job_attempts job,secondary_state = sp_job_status job\<rparr>"

datatype sp_cell_action = SP_Enqueue_Cell sp_publication nat | SP_Dispatch_Cell sp_key | SP_Fail_Cell sp_key
datatype sp_queue_reply = SP_Enqueued "sp_key option" | SP_Dispatched "sp_job option" | SP_Changed bool

fun sp_cell_key where
  "sp_cell_key (SP_Enqueue_Cell pub target) = sp_key_of pub"
| "sp_cell_key (SP_Dispatch_Cell key) = key"
| "sp_cell_key (SP_Fail_Cell key) = key"

fun sp_model_action where
  "sp_model_action (SP_Enqueue_Cell pub target) = Slot_Enqueue (sp_publication_model pub) target"
| "sp_model_action (SP_Dispatch_Cell key) = Slot_Dispatch (sp_abstract_key key)"
| "sp_model_action (SP_Fail_Cell key) = Slot_Fail (sp_abstract_key key)"

fun sp_model_reply where
  "sp_model_reply (SP_Enqueued key) = Settlement_Enqueued (map_option sp_abstract_key key)"
| "sp_model_reply (SP_Dispatched job) = Settlement_Dispatched (map_option sp_model_job job)"
| "sp_model_reply (SP_Changed changed) = Settlement_Changed changed"

fun sp_step_cell where
  "sp_step_cell (SP_Enqueue_Cell pub target) old =
    ((case old of None \<Rightarrow> Some \<lparr>sp_job_publication = pub,sp_job_target = target,
        sp_job_attempts = 0,sp_job_status = Secondary_Waiting\<rparr> | Some job \<Rightarrow> old),
     SP_Enqueued (Some (sp_key_of pub)))"
| "sp_step_cell (SP_Dispatch_Cell key) old =
    (case old of None \<Rightarrow> (None,SP_Dispatched None)
     | Some job \<Rightarrow> if sp_job_status job = Secondary_Completed \<or> sp_job_attempts job \<ge> 2^64 - 1
       then (old,SP_Dispatched None)
       else let next = job\<lparr>sp_job_attempts := Suc (sp_job_attempts job),sp_job_status := Secondary_In_Flight\<rparr>
         in (Some next,SP_Dispatched (Some next)))"
| "sp_step_cell (SP_Fail_Cell key) old =
    (case old of None \<Rightarrow> (None,SP_Changed False)
     | Some job \<Rightarrow> if sp_job_status job = Secondary_In_Flight
       then (Some (job\<lparr>sp_job_status := Secondary_Waiting\<rparr>),SP_Changed True)
       else (old,SP_Changed False))"

theorem sp_native_cell_uses_the_existing_checked_slot_operation:
  "map_prod (map_option sp_model_job) sp_model_reply (sp_step_cell action old) =
    step_one_slot verified (sp_model_action action) (map_option sp_model_job old)"
  by (cases action; cases old)
    (auto simp: sp_model_job_def sp_key_of_def sp_abstract_key_def settlement_key_def Let_def split: if_splits)

definition sp_step_jobs where
  "sp_step_jobs action jobs =
    (let key = sp_cell_key action; result = sp_step_cell action (jobs key)
     in (jobs(key := fst result),snd result))"

lemma sp_unrelated_full_native_key_is_untouched:
  "key \<noteq> sp_cell_key action \<Longrightarrow> fst (sp_step_jobs action jobs) key = jobs key"
  by (simp add: sp_step_jobs_def Let_def)

theorem sp_distinct_full_native_slots_exchange_state_and_each_reply:
  assumes "sp_cell_key first \<noteq> sp_cell_key second"
  shows "fst (sp_step_jobs second (fst (sp_step_jobs first jobs))) =
      fst (sp_step_jobs first (fst (sp_step_jobs second jobs)))"
    "snd (sp_step_jobs first jobs) = snd (sp_step_jobs first (fst (sp_step_jobs second jobs)))"
    "snd (sp_step_jobs second jobs) = snd (sp_step_jobs second (fst (sp_step_jobs first jobs)))"
  using assms by (simp_all add: sp_step_jobs_def Let_def fun_upd_twist)

datatype sp_dependency = SP_Authority | SP_Revision | SP_Completion | SP_Read_Provider
  | SP_Origin source_key | SP_Publication source_key | SP_Slot sp_key

datatype sp_class = SP_Observation_Class "source_key option" "source_key option"
  | SP_Slot_Class sp_key "source_key option" | SP_Serial_Class

fun sp_footprint where
  "sp_footprint (SP_Observation_Class origin publication) =
    ({SP_Authority,SP_Revision,SP_Completion,SP_Read_Provider} \<union>
       (case origin of None \<Rightarrow> {} | Some key \<Rightarrow> {SP_Origin key}) \<union>
       (case publication of None \<Rightarrow> {} | Some key \<Rightarrow> {SP_Publication key}),{})"
| "sp_footprint (SP_Slot_Class key publication) =
    ({SP_Authority,SP_Slot key} \<union>
       (case publication of None \<Rightarrow> {} | Some origin \<Rightarrow> {SP_Publication origin}),{SP_Slot key})"
| "sp_footprint SP_Serial_Class =
    ({SP_Authority,SP_Revision,SP_Completion,SP_Read_Provider},
     {SP_Authority,SP_Revision,SP_Completion,SP_Read_Provider})"

definition sp_compatible where
  "sp_compatible first second \<longleftrightarrow>
    (let (read_a,write_a) = sp_footprint first; (read_b,write_b) = sp_footprint second
     in write_a \<inter> read_b = {} \<and> write_b \<inter> read_a = {} \<and> write_a \<inter> write_b = {})"

lemma sp_slot_compatibility_is_exact_full_key_inequality:
  "sp_compatible (SP_Slot_Class first pub_a) (SP_Slot_Class second pub_b) = (first \<noteq> second)"
  by (auto simp: sp_compatible_def Let_def split: option.splits)

lemma sp_shared_authority_writer_is_always_serial:
  "\<not> sp_compatible SP_Serial_Class other" "\<not> sp_compatible other SP_Serial_Class"
  by (cases other; auto simp: sp_compatible_def Let_def split: option.splits)+

lemma sp_observation_and_queue_slot_are_compatible:
  "sp_compatible (SP_Observation_Class origin publication) (SP_Slot_Class key dependency)"
  "sp_compatible (SP_Slot_Class key dependency) (SP_Observation_Class origin publication)"
  by (auto simp: sp_compatible_def Let_def split: option.splits)

record 'data sp_state =
  sp_data :: 'data
  sp_publications :: "(source_key \<times> sp_publication) list"
  sp_jobs :: "sp_key \<Rightarrow> sp_job option"
  sp_known_keys :: "sp_key list"
  sp_target :: nat

datatype ('token,'other) sp_action = SP_Enqueue_Action 'token source_key
  | SP_Dispatch_Action 'token sp_key | SP_Fail_Action 'token sp_key | SP_Other_Action 'other

definition sp_classify where
  "sp_classify can_maintain classify_other action state =
    (case action of SP_Enqueue_Action token origin \<Rightarrow>
       if can_maintain token (sp_data state) then
         (case map_of (sp_publications state) origin of None \<Rightarrow> SP_Observation_Class None (Some origin)
          | Some pub \<Rightarrow> SP_Slot_Class (sp_key_of pub) (Some origin)) else SP_Serial_Class
     | SP_Dispatch_Action token key \<Rightarrow>
         if can_maintain token (sp_data state) then SP_Slot_Class key None else SP_Serial_Class
     | SP_Fail_Action token key \<Rightarrow>
         if can_maintain token (sp_data state) then SP_Slot_Class key None else SP_Serial_Class
     | SP_Other_Action other \<Rightarrow> classify_other other (sp_data state))"

lemma sp_queue_rows_do_not_supply_or_rewrite_the_classifier:
  "sp_classify can_maintain classify_other action (state\<lparr>sp_jobs := jobs,sp_known_keys := keys\<rparr>) =
    sp_classify can_maintain classify_other action state"
  by (cases action) (simp_all add: sp_classify_def)

lemma sp_absent_publication_is_a_dependency_not_a_supplied_slot:
  assumes "can_maintain token (sp_data state)" "map_of (sp_publications state) origin = None"
  shows "sp_classify can_maintain classify_other (SP_Enqueue_Action token origin) state =
    SP_Observation_Class None (Some origin)"
  using assms by (simp add: sp_classify_def)

definition sp_slot_pair where
  "sp_slot_pair swapped first second jobs =
    (if swapped then let (middle,reply_b) = sp_step_jobs second jobs; (final,reply_a) = sp_step_jobs first middle
       in (final,reply_a,reply_b)
     else let (middle,reply_a) = sp_step_jobs first jobs; (final,reply_b) = sp_step_jobs second middle
       in (final,reply_a,reply_b))"

theorem sp_distinct_slot_pair_keeps_labels_in_original_order:
  assumes "sp_cell_key first \<noteq> sp_cell_key second"
  shows "sp_slot_pair False first second jobs = sp_slot_pair True first second jobs"
  using sp_distinct_full_native_slots_exchange_state_and_each_reply[OF assms]
  by (simp add: sp_slot_pair_def Let_def split_def prod_eq_iff)

lemma sp_same_slot_attempts_are_observable_per_occurrence:
  fixes key :: sp_key and job :: sp_job
  assumes "sp_job_status job \<noteq> Secondary_Completed" "sp_job_attempts job + 2 < 2^64"
  defines "jobs \<equiv> (\<lambda>_. None)(key := Some job)"
  shows "sp_slot_pair False (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs \<noteq>
         sp_slot_pair True (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs"
proof -
  let ?first = "job\<lparr>sp_job_attempts := Suc (sp_job_attempts job),sp_job_status := Secondary_In_Flight\<rparr>"
  let ?second = "job\<lparr>sp_job_attempts := Suc (Suc (sp_job_attempts job)),sp_job_status := Secondary_In_Flight\<rparr>"
  have bounds: "sp_job_attempts job < 2^64 - 1" "Suc (sp_job_attempts job) < 2^64 - 1"
    using assms(2) by arith+
  have first_order: "sp_slot_pair False (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs =
      (jobs(key := Some ?second),SP_Dispatched (Some ?first),SP_Dispatched (Some ?second))"
    using assms(1) bounds by (simp add: jobs_def sp_slot_pair_def sp_step_jobs_def Let_def)
  have second_order: "sp_slot_pair True (SP_Dispatch_Cell key) (SP_Dispatch_Cell key) jobs =
      (jobs(key := Some ?second),SP_Dispatched (Some ?second),SP_Dispatched (Some ?first))"
    using assms(1) bounds by (simp add: jobs_def sp_slot_pair_def sp_step_jobs_def Let_def)
  have different: "?first \<noteq> ?second"
  proof
    assume "?first = ?second"
    then have "sp_job_attempts ?first = sp_job_attempts ?second" by simp
    then show False by simp
  qed
  show ?thesis by (simp add: first_order second_order different)
qed

lemmas sp_public_finite_exchange_closure = finite_adjacent_exchanges_preserve_product_effects_and_replies
lemmas sp_public_stale_release_guard = a_new_authority_cut_cannot_release_the_old_schedule_replies

context source_attestation
begin
lemmas sp_public_reference_exchange = compatible_actions_exchange_in_the_actual_reference_service
lemmas sp_public_product_finite_closure = the_actual_product_finite_exchange_closure
lemmas sp_public_signed_transport_exchange = compatible_authenticated_wire_actions_keep_the_product_transport_and_labeled_replies
end

text \<open>
  The native full key retains commit epoch and owner in its publication image.
  Exact full-key lookup precedes the reused public one-slot operation; a wrong
  native epoch cannot alias an existing row through the abstract key projection.
  Classification is evaluated against current data and stable publication,
  not a caller-provided footprint. ACK/Current signed classifiers and release
  checks remain separately named public interfaces, not a typed-scheduler alias.
\<close>

end
