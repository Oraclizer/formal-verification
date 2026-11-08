theory Recovery_Queue_Reply_Binding
  imports "OIP_Product.Queue_Action_Locality"
begin

text \<open>These source-bound lemmas establish the settlement-branch reply condition. The complete
  retained-service cross-constructor result additionally consumes the execution and control projections.\<close>

lemma one_slot_reply_is_determined_by_its_changed_image:
  assumes changed: "fst (step_one_slot verified a old) \<noteq> old"
    and same: "fst (step_one_slot verified a old) = fst (step_one_slot verified b old)"
  shows "snd (step_one_slot verified a old) = snd (step_one_slot verified b old)"
proof (cases old)
  case None
  then show ?thesis using changed same by (cases a; cases b; auto simp: Let_def)
next
  case (Some job)
  show ?thesis
    using changed same Some
    by (cases job; cases a; cases b; auto simp: Let_def split: if_splits)
qed

lemma queue_slot_reply_is_determined_by_its_changed_map:
  assumes changed: "fst (step_settlement_slot verified a jobs) \<noteq> jobs"
    and same: "fst (step_settlement_slot verified a jobs) = fst (step_settlement_slot verified b jobs)"
  shows "snd (step_settlement_slot verified a jobs) = snd (step_settlement_slot verified b jobs)"
proof -
  let ?ka = "resolved_slot a"
  let ?kb = "resolved_slot b"
  let ?ra = "step_one_slot verified a (jobs ?ka)"
  let ?rb = "step_one_slot verified b (jobs ?kb)"
  have changed_item: "fst ?ra \<noteq> jobs ?ka"
    using changed by (auto simp: step_settlement_slot_def Let_def)
  have same_item: "(jobs(?ka := fst ?ra)) ?ka = (jobs(?kb := fst ?rb)) ?ka"
    using fun_cong[OF same, of ?ka] by (simp add: step_settlement_slot_def Let_def)
  have keys: "?ka = ?kb"
    using changed_item same_item by (cases "?ka = ?kb") auto
  have effects: "fst (step_one_slot verified a (jobs ?ka)) = fst (step_one_slot verified b (jobs ?ka))"
    using same_item keys by simp
  have replies: "snd (step_one_slot verified a (jobs ?ka)) = snd (step_one_slot verified b (jobs ?ka))"
    by (rule one_slot_reply_is_determined_by_its_changed_image[OF changed_item effects])
  show ?thesis using replies keys by (simp add: step_settlement_slot_def Let_def)
qed

lemma settlement_reply_is_determined_by_the_changed_world:
  assumes changed: "fst (execute_settlement_action verified a state) \<noteq> state"
    and same: "fst (execute_settlement_action verified a state) = fst (execute_settlement_action verified b state)"
  shows "snd (execute_settlement_action verified a state) = snd (execute_settlement_action verified b state)"
proof (cases "queue_action_at a state")
  case None
  then show ?thesis using changed by (simp add: execute_settlement_action_def)
next
  case (Some first)
  have first_at: "queue_action_at a state = Some first" by (rule Some)
  show ?thesis
  proof (cases "queue_action_at b state")
    case None
    then show ?thesis using changed same by (simp add: execute_settlement_action_def)
  next
    case (Some second)
    let ?jobs = "settlement_jobs state"
    have second_at: "queue_action_at b state = Some second" by (rule Some)
    have changed_map: "fst (step_settlement_slot verified first ?jobs) \<noteq> ?jobs"
      using changed first_at by (auto simp: execute_settlement_action_def Let_def)
    have maps: "fst (step_settlement_slot verified first ?jobs) = fst (step_settlement_slot verified second ?jobs)"
      using arg_cong[OF same, of settlement_jobs] first_at second_at
      by (simp add: execute_settlement_action_def Let_def)
    have replies: "snd (step_settlement_slot verified first ?jobs) = snd (step_settlement_slot verified second ?jobs)"
      by (rule queue_slot_reply_is_determined_by_its_changed_map[OF changed_map maps])
    show ?thesis using replies first_at second_at by (simp add: execute_settlement_action_def Let_def)
  qed
qed

lemma queue_changed_image_premise_is_inhabited:
  "fst (step_one_slot verified (Slot_Enqueue publication target) None) \<noteq> None"
  "snd (step_one_slot verified (Slot_Enqueue publication target) None) =
     Settlement_Enqueued (Some (settlement_key publication))"
  by simp_all

definition reply_only_queue_mutant where
  "reply_only_queue_mutant verified choose_reply a old =
    (fst (step_one_slot verified a old),
      if choose_reply then snd (step_one_slot verified a old) else Settlement_Changed False)"

lemma changing_only_the_reply_breaks_the_same_effect_property:
  "fst (reply_only_queue_mutant verified True (Slot_Enqueue publication target) None) =
     fst (reply_only_queue_mutant verified False (Slot_Enqueue publication target) None)"
  "fst (reply_only_queue_mutant verified True (Slot_Enqueue publication target) None) \<noteq> None"
  "snd (reply_only_queue_mutant verified True (Slot_Enqueue publication target) None) \<noteq>
     snd (reply_only_queue_mutant verified False (Slot_Enqueue publication target) None)"
  by (simp_all add: reply_only_queue_mutant_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms one_slot_reply_is_determined_by_its_changed_image
      queue_slot_reply_is_determined_by_its_changed_map settlement_reply_is_determined_by_the_changed_world
      queue_changed_image_premise_is_inhabited changing_only_the_reply_breaks_the_same_effect_property})
  then () else error "Unexpected oracle in source-bound queue reply target"
\<close>

end
