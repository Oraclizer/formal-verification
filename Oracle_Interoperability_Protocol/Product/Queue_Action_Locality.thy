theory Queue_Action_Locality
  imports Recovery_Commit
begin

section \<open>The exact settlement operation and its product response\<close>

datatype resolved_settlement_action =
    Slot_Enqueue product_publication nat
  | Slot_Dispatch settlement_identity
  | Slot_Fail settlement_identity
  | Slot_Ack product_secondary_ack

datatype settlement_action_reply =
    Settlement_Enqueued "settlement_identity option"
  | Settlement_Dispatched "product_secondary_job option"
  | Settlement_Changed bool

fun resolved_slot where
  "resolved_slot (Slot_Enqueue publication target) = settlement_key publication"
| "resolved_slot (Slot_Dispatch key) = key"
| "resolved_slot (Slot_Fail key) = key"
| "resolved_slot (Slot_Ack ack) = ack_settlement_key ack"

fun queue_action_at where
  "queue_action_at (Exact_Enqueue origin) s = map_option (\<lambda>publication. Slot_Enqueue publication (settlement_target s))
    (primary_publication (settlement_primary s) origin)"
| "queue_action_at (Exact_Dispatch_Secondary key) s = Some (Slot_Dispatch key)"
| "queue_action_at (Exact_Secondary_Failed key) s = Some (Slot_Fail key)"
| "queue_action_at (Exact_Acknowledge ack) s = Some (Slot_Ack ack)"
| "queue_action_at action s = None"

fun is_settlement_action where
  "is_settlement_action (Exact_Enqueue origin) = True"
| "is_settlement_action (Exact_Dispatch_Secondary key) = True"
| "is_settlement_action (Exact_Secondary_Failed key) = True"
| "is_settlement_action (Exact_Acknowledge ack) = True"
| "is_settlement_action action = False"

fun step_one_slot where
  "step_one_slot verified (Slot_Enqueue publication target) old =
    ((case old of Some job \<Rightarrow> old | None \<Rightarrow> Some
       \<lparr>secondary_publication = publication, secondary_target = target, secondary_attempts = 0,
        secondary_state = Secondary_Waiting\<rparr>), Settlement_Enqueued (Some (settlement_key publication)))"
| "step_one_slot verified (Slot_Dispatch key) old =
    (case old of None \<Rightarrow> (None, Settlement_Dispatched None)
     | Some job \<Rightarrow> if secondary_state job = Secondary_Completed \<or> secondary_attempts job \<ge> 2^64 - 1
       then (old, Settlement_Dispatched None)
       else let next_job = job\<lparr>secondary_attempts := Suc (secondary_attempts job), secondary_state := Secondary_In_Flight\<rparr>
         in (Some next_job, Settlement_Dispatched (Some next_job)))"
| "step_one_slot verified (Slot_Fail key) old =
    (case old of None \<Rightarrow> (None, Settlement_Changed False)
     | Some job \<Rightarrow> if secondary_state job = Secondary_In_Flight
       then (Some (job\<lparr>secondary_state := Secondary_Waiting\<rparr>), Settlement_Changed True)
       else (old, Settlement_Changed False))"
| "step_one_slot verified (Slot_Ack ack) old =
    (case old of None \<Rightarrow> (None, Settlement_Changed False)
     | Some job \<Rightarrow> if verified ack \<and> exact_secondary_ack ack job \<and> secondary_attempts job > 0
       then (Some (job\<lparr>secondary_state := Secondary_Completed\<rparr>), Settlement_Changed True)
       else (old, Settlement_Changed False))"

definition step_settlement_slot where
  "step_settlement_slot verified action jobs =
    (let key = resolved_slot action; result = step_one_slot verified action (jobs key)
     in (jobs(key := fst result), snd result))"

lemma unrelated_settlement_slot_is_untouched:
  assumes "key \<noteq> resolved_slot action"
  shows "fst (step_settlement_slot verified action jobs) key = jobs key"
  using assms by (simp add: step_settlement_slot_def Let_def)

lemma different_actual_settlement_slots_exchange:
  assumes "resolved_slot a \<noteq> resolved_slot b"
  shows "fst (step_settlement_slot verified b (fst (step_settlement_slot verified a jobs))) =
         fst (step_settlement_slot verified a (fst (step_settlement_slot verified b jobs)))"
    "snd (step_settlement_slot verified a jobs) =
       snd (step_settlement_slot verified a (fst (step_settlement_slot verified b jobs)))"
    "snd (step_settlement_slot verified b jobs) =
       snd (step_settlement_slot verified b (fst (step_settlement_slot verified a jobs)))"
  using assms by (simp_all add: step_settlement_slot_def Let_def fun_upd_twist)

lemma enqueue_reads_publication_even_when_no_job_exists:
  "queue_action_at (Exact_Enqueue origin) s =
    map_option (\<lambda>publication. Slot_Enqueue publication (settlement_target s))
      (primary_publication (settlement_primary s) origin)"
  by simp

lemma queue_resolution_does_not_read_another_job:
  "queue_action_at action (s\<lparr>settlement_jobs := jobs\<rparr>) = queue_action_at action s"
  by (cases action) simp_all

definition execute_settlement_action where
  "execute_settlement_action verified action s =
    (case queue_action_at action s of None \<Rightarrow> (s, Settlement_Enqueued None)
     | Some resolved \<Rightarrow> let result = step_settlement_slot verified resolved (settlement_jobs s)
       in (s\<lparr>settlement_jobs := fst result\<rparr>, snd result))"

lemma exact_queue_step_keeps_the_authoritative_primary_and_target [simp]:
  "settlement_primary (fst (execute_settlement_action verified action s)) = settlement_primary s"
  "settlement_target (fst (execute_settlement_action verified action s)) = settlement_target s"
  by (simp_all add: execute_settlement_action_def Let_def split: option.splits)

lemma exact_queue_effect_is_the_existing_endpoint_effect:
  "fst (execute_settlement_action verified (Exact_Enqueue origin) s) = enqueue_secondary origin s"
  "fst (execute_settlement_action verified (Exact_Secondary_Failed key) s) = fail_secondary key s"
  "fst (execute_settlement_action verified (Exact_Acknowledge ack) s) = acknowledge_secondary verified ack s"
  by (simp_all add: execute_settlement_action_def step_settlement_slot_def enqueue_secondary_def fail_secondary_def
       acknowledge_secondary_def update_secondary_job_def Let_def fun_upd_idem split: option.splits if_splits)

lemma exact_dispatch_uses_the_existing_endpoint_up_to_its_counter_bound:
  assumes "settlement_jobs s key = Some job" "secondary_attempts job < 2^64 - 1"
  shows "fst (execute_settlement_action verified (Exact_Dispatch_Secondary key) s) = dispatch_secondary key s"
  using assms by (simp add: execute_settlement_action_def step_settlement_slot_def dispatch_secondary_def
    update_secondary_job_def Let_def fun_upd_idem split: if_splits)

end
