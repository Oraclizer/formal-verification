theory Mixed_Service_Example
  imports REOS_Scheduler_Controls.Scheduler_Examples Mixed_Service_Fixture
begin

definition ordinary_input :: packet where
  "ordinary_input = ordinary_packet\<lparr>packet_identity := fixture_ordinary_identity,
    packet_contents := Ordinary_Work fixture_ordinary_digest,
    packet_authority_epoch := fixture_authority, packet_policy_epoch := fixture_ordinary_epoch\<rparr>"

definition regulation_a :: packet where
  "regulation_a = urgent_packet\<lparr>packet_identity := fixture_actor_a,
    packet_contents := Raise_Level fixture_case_a fixture_raise_a,
    packet_authority_epoch := fixture_authority, packet_policy_epoch := fixture_epoch_a,
    packet_order := fixture_priority_a\<rparr>"

definition regulation_b :: packet where
  "regulation_b = urgent_packet\<lparr>packet_identity := fixture_actor_b,
    packet_contents := Raise_Level fixture_case_b fixture_raise_b,
    packet_authority_epoch := fixture_authority, packet_policy_epoch := fixture_epoch_b,
    packet_order := fixture_priority_b\<rparr>"

definition rotate :: "nat \<Rightarrow> scheduler_action" where
  "rotate policy = Rotate_Context fixture_time_at_start fixture_authority fixture_case_a policy"

definition start :: scheduler_state where
  "start = scheduler_example\<lparr>rollback_context := fixture\<lparr>
    authority_epoch := fixture_authority, consensus_time := fixture_time_at_start,
    policy_epoch := (\<lambda>k. if k = fixture_case_a then fixture_epoch_a
      else if k = fixture_case_b then fixture_epoch_b else fixture_ordinary_epoch)\<rparr>,
    signed_packets := {ordinary_input, regulation_a, regulation_b},
    regulatory_grants := {regulation_a, regulation_b},
    severity_now := (\<lambda>k. if k = fixture_case_a then fixture_level_a else fixture_level_b),
    severity_limit := (\<lambda>k. if k = fixture_case_a then fixture_limit_a else fixture_limit_b),
    verified_context_updates := {
      (fixture_time_at_start, fixture_authority, fixture_case_a, fixture_new_epoch_a),
      (fixture_time_at_start, fixture_authority, fixture_case_a, fixture_race_epoch_a)}\<rparr>"

definition ordinary_admitted :: scheduler_state where
  "ordinary_admitted = snd (admit start ordinary_input)"

definition a_admitted :: scheduler_state where
  "a_admitted = snd (admit ordinary_admitted regulation_a)"

definition all_admitted :: scheduler_state where
  "all_admitted = snd (admit a_admitted regulation_b)"

definition first_update :: scheduler_state where
  "first_update = snd (run_scheduler all_admitted (rotate fixture_new_epoch_a))"

definition second_update :: scheduler_state where
  "second_update = snd (run_scheduler first_update (rotate fixture_race_epoch_a))"

definition b_served :: scheduler_state where
  "b_served = snd (schedule second_update)"

definition ordinary_served :: scheduler_state where
  "ordinary_served = snd (schedule b_served)"

lemmas mixed_steps = ordinary_input_def regulation_a_def regulation_b_def rotate_def start_def
  ordinary_admitted_def a_admitted_def all_admitted_def first_update_def second_update_def b_served_def
  ordinary_served_def scheduler_reduction scheduler_example_def fixture_def ordinary_packet_def
  urgent_packet_def regulatory_effect_def packet_fresh_def admit_def enqueue_packet_def
  ready_regulation_def next_regulation_def fixture_authority_def fixture_time_at_start_def
  fixture_ordinary_epoch_def fixture_ordinary_identity_def fixture_case_a_def fixture_case_b_def
  fixture_actor_a_def fixture_actor_b_def fixture_epoch_a_def fixture_epoch_b_def fixture_raise_a_def
  fixture_raise_b_def fixture_priority_a_def fixture_priority_b_def fixture_level_a_def fixture_level_b_def
  fixture_limit_a_def fixture_limit_b_def fixture_new_epoch_a_def fixture_race_epoch_a_def Let_def

lemma signed_inputs_reach_the_mixed_queue:
  "scheduler_step start (Submit ordinary_input) (Accepted fixture_ordinary_identity) ordinary_admitted"
  "scheduler_step ordinary_admitted (Submit regulation_a) (Accepted fixture_actor_a) a_admitted"
  "scheduler_step a_admitted (Submit regulation_b) (Accepted fixture_actor_b) all_admitted"
  "next_regulation all_admitted = Some regulation_a"
  by (simp_all add: mixed_steps)

lemma two_case_updates_preserve_the_peer_and_the_admitted_ordinary:
  "scheduler_step all_admitted (rotate fixture_new_epoch_a) (Internal Snapshot_Changed) first_update"
  "scheduler_step first_update (rotate fixture_race_epoch_a) (Internal Snapshot_Changed) second_update"
  "\<not> ready_regulation second_update regulation_a"
  "next_regulation second_update = Some regulation_b"
  "ordinary_queue second_update = [ordinary_input]"
  by (simp_all add: mixed_steps)

lemma the_mixed_service_records_effect_and_following_fifo_service:
  "scheduler_step second_update Honest_Service
     (Internal (Served_Regulation fixture_actor_b fixture_case_b)) b_served"
  "severity_now b_served fixture_case_b = fixture_served_level_b"
  "severity_now b_served fixture_case_a = fixture_served_level_a"
  "regulation_receipts b_served fixture_priority_receipt_identity = Some regulation_b"
  "regulation_receipts b_served fixture_actor_a = None"
  "scheduler_step b_served Honest_Service (Internal (Served_Ordinary fixture_ordinary_identity)) ordinary_served"
  "ordinary_receipts ordinary_served fixture_delivered_identity = Some ordinary_input"
  by (simp_all add: mixed_steps fixture_served_level_a_def fixture_served_level_b_def
      fixture_priority_receipt_identity_def fixture_delivered_identity_def)

lemma the_mixed_fixture_records_rotation_and_service_order:
  "fixture_before_selected = fixture_actor_a \<and> fixture_after_selected = fixture_actor_b \<and>
    fixture_epoch_b = fixture_new_epoch_b \<and> fixture_level_a = fixture_served_level_a \<and>
    fixture_level_b < fixture_served_level_b \<and> fixture_a_receipt_absent \<and>
    fixture_a_status = [1] \<and>
    fixture_conflict = [2] \<and>
    fixture_recovery = [3] \<and>
    fixture_replay = [4] \<and>
    fixture_first_lane = [5] \<and>
    fixture_second_lane = [6] \<and>
    fixture_ordinary_bytes = fixture_delivered_bytes \<and> fixture_receipts_match"
  by (simp add: fixture_before_selected_def fixture_after_selected_def fixture_actor_a_def fixture_actor_b_def
      fixture_epoch_b_def fixture_new_epoch_b_def fixture_level_a_def fixture_served_level_a_def
      fixture_level_b_def fixture_served_level_b_def fixture_a_receipt_absent_def fixture_a_status_def
      fixture_conflict_def fixture_recovery_def fixture_replay_def fixture_first_lane_def fixture_second_lane_def
      fixture_ordinary_bytes_def fixture_delivered_bytes_def fixture_receipts_match_def
      fixture_exact_regulation_receipt_def fixture_recovery_receipt_def
      fixture_replay_receipt_def fixture_reopened_regulation_receipt_def)

text \<open>Reconciliation and replay report the result of an earlier commit.
  An observation with the exact saved packet is a read of the committed state.
  It contributes no additional service event to the abstract run.\<close>

definition read_ordinary_receipt :: "scheduler_state \<Rightarrow> packet \<Rightarrow> scheduler_state \<Rightarrow> bool" where
  "read_ordinary_receipt s p t \<longleftrightarrow> (t = s \<and> ordinary_receipts s (packet_identity p) = Some p)"

lemma an_exact_receipt_can_be_returned_without_another_service:
  "read_ordinary_receipt ordinary_served ordinary_input ordinary_served"
  "\<And>t. read_ordinary_receipt ordinary_served ordinary_input t \<Longrightarrow> t = ordinary_served"
  using the_mixed_service_records_effect_and_following_fifo_service(7)
  by (simp_all add: read_ordinary_receipt_def ordinary_input_def fixture_ordinary_identity_def fixture_delivered_identity_def)

definition permanently_stale :: "scheduler_state \<Rightarrow> packet \<Rightarrow> bool" where
  "permanently_stale s p \<longleftrightarrow>
     packet_authority_epoch p < authority_epoch (rollback_context s) \<or>
     packet_policy_epoch p < policy_epoch (rollback_context s) (regulatory_case (packet_contents p))"

lemma later_nondecreasing_epochs_cannot_revalidate_a_retired_packet:
  assumes "permanently_stale s p"
    and "authority_epoch (rollback_context s) \<le> authority_epoch (rollback_context t)"
    and "policy_epoch (rollback_context s) (regulatory_case (packet_contents p))
        \<le> policy_epoch (rollback_context t) (regulatory_case (packet_contents p))"
  shows "\<not> ready_regulation t p"
  using assms by (auto simp: permanently_stale_def ready_regulation_def regulatory_effect_def packet_fresh_def)

lemma a_strictly_monotone_case_cannot_reopen_an_already_reached_raise:
  assumes body: "packet_contents p = Raise_Level k level"
    and reached: "level \<le> severity_now s k"
    and monotone: "severity_now s k \<le> severity_now t k"
  shows "\<not> ready_regulation t p"
  using assms by (auto simp: ready_regulation_def regulatory_effect_def)

lemma retaining_identity_while_retiring_stale_entries_preserves_priority_slots:
  "priority_slots (s\<lparr>regulatory_queue := filter (\<lambda>p. \<not> permanently_stale s p) (regulatory_queue s)\<rparr>)
    = priority_slots s"
proof -
  have scope: "ready_regulation (s\<lparr>regulatory_queue := qs\<rparr>) p = ready_regulation s p" for qs p
    by (cases "packet_contents p")
       (auto simp: ready_regulation_def regulatory_effect_def packet_fresh_def
         split: prod.splits transition_result.splits if_splits)
  have fresh: "\<And>p. ready_regulation s p \<Longrightarrow> \<not> permanently_stale s p"
    by (auto simp: ready_regulation_def regulatory_effect_def permanently_stale_def packet_fresh_def)
  have prune: "filter (ready_regulation s) (filter (\<lambda>p. \<not> permanently_stale s p) ps)
      = filter (ready_regulation s) ps" for ps
    by (induction ps) (auto dest: fresh)
  have predicate: "ready_regulation (s\<lparr>regulatory_queue :=
      filter (\<lambda>p. \<not> permanently_stale s p) (regulatory_queue s)\<rparr>) = ready_regulation s"
    by (rule ext) (rule scope)
  have "priority_slots (s\<lparr>regulatory_queue :=
         filter (\<lambda>p. \<not> permanently_stale s p) (regulatory_queue s)\<rparr>)
      = length (filter (ready_regulation s) (filter (\<lambda>p. \<not> permanently_stale s p)
          (regulatory_queue s)))"
    by (simp add: priority_slots_def predicate)
  also have "\<dots> = length (filter (ready_regulation s) (regulatory_queue s))"
    by (simp only: prune)
  finally show ?thesis by (simp only: priority_slots_def)
qed

record service_turn =
  turn_actor :: nat
  turn_authority :: nat
  turn_id :: nat

definition qualified_turn ::
  "(nat \<Rightarrow> nat option) \<Rightarrow> service_turn set \<Rightarrow> scheduler_state \<Rightarrow> service_turn \<Rightarrow> bool"
where
  "qualified_turn signer verified s turn \<longleftrightarrow>
    (turn \<in> verified \<and> turn_authority turn = authority_epoch (rollback_context s)
      \<and> signer (turn_authority turn) = Some (turn_actor turn))"

definition execute_turn ::
  "(nat \<Rightarrow> nat option) \<Rightarrow> service_turn set \<Rightarrow> scheduler_state \<Rightarrow> service_turn
   \<Rightarrow> scheduler_result \<times> scheduler_state"
where
  "execute_turn signer verified s turn =
    run_scheduler s (if qualified_turn signer verified s turn then Honest_Service else Unproductive_Turn)"

text \<open>The signer table and observed verified turns are supplied facts.
Invalid turns preserve pending obligations. Recurrence of effective service
is still required when applying the public request-progress theorem.\<close>

lemma an_unqualified_turn_cannot_create_effect_or_receipt:
  assumes "\<not> qualified_turn signer verified s turn"
  shows "execute_turn signer verified s turn = (Operational_Failure No_Effective_Opportunity, s)"
  using assms by (simp add: execute_turn_def)

definition current_turn :: service_turn where
  "current_turn = \<lparr>turn_actor = 2, turn_authority = fixture_authority, turn_id = 19\<rparr>"

definition old_turn :: service_turn where
  "old_turn = current_turn\<lparr>turn_authority := fixture_authority - 1\<rparr>"

definition foreign_turn :: service_turn where
  "foreign_turn = current_turn\<lparr>turn_actor := 3\<rparr>"

lemma selected_stale_or_foreign_signer_cannot_consume_the_mixed_slot:
  "execute_turn (\<lambda>_. Some 2) {old_turn} second_update old_turn
    = (Operational_Failure No_Effective_Opportunity, second_update)"
  "execute_turn (\<lambda>_. Some 2) {foreign_turn} second_update foreign_turn
    = (Operational_Failure No_Effective_Opportunity, second_update)"
  "execute_turn (\<lambda>_. Some 2) {} second_update current_turn
    = (Operational_Failure No_Effective_Opportunity, second_update)"
  "execute_turn (\<lambda>_. Some 2) {current_turn} second_update current_turn
    = (Internal (Served_Regulation fixture_actor_b fixture_case_b), b_served)"
  by (simp_all add: execute_turn_def qualified_turn_def current_turn_def old_turn_def foreign_turn_def mixed_steps)

end
