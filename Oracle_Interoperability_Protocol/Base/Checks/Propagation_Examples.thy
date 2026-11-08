theory Propagation_Examples
  imports "../Exactly_Once" Lock_Terminal_Entries
begin

definition queue_example_decision where
  "queue_example_decision = \<lparr>origin_binding = sample_binding 17, origin_kind = Confirmed_Decision,
    origin_epoch = 9, origin_commit_position = 0\<rparr>"

definition queue_example_publication where
  "queue_example_publication = \<lparr>publication_origin = (0,17), publication_decision = queue_example_decision\<rparr>"

definition queue_example_primary where
  "queue_example_primary core = (initial_origin_world (terminal_example_world core))\<lparr>
    origin_decisions := (\<lambda>_. None)((0,17) := Some queue_example_decision)\<rparr>"

definition queue_example_world where
  "queue_example_world core = initial_settlement_world 99 (queue_example_primary core)"

definition queue_example_job where
  "queue_example_job = \<lparr>secondary_publication = queue_example_publication, secondary_target = 99,
    secondary_attempts = 0, secondary_state = Secondary_Waiting\<rparr>"

lemma a_committed_but_unpublished_terminal_cannot_enqueue:
  "enqueue_secondary (0,17) (queue_example_world (finality_sample_recorded 17)) = queue_example_world (finality_sample_recorded 17)"
  by (rule no_secondary_job_before_primary_publication)
    (simp add: queue_example_world_def initial_settlement_world_def queue_example_primary_def initial_origin_world_def
      terminal_example_world_def initial_outcome_world_def initial_call_machine_def primary_publication_def
      finality_recording_is_not_primary_publication Let_def split: option.splits)

lemma checked_primary_commitment_opens_one_secondary_job:
  "settlement_jobs (enqueue_secondary (0,17) (queue_example_world call_example_ready)) ((0,17),0) = Some queue_example_job"
proof -
  have primary: "primary_publication (queue_example_primary call_example_ready) (0,17) = Some queue_example_publication"
    by (simp add: primary_publication_def queue_example_primary_def initial_origin_world_def initial_outcome_world_def
      terminal_example_world_def initial_call_machine_def call_example_ready_shape call_example_seed_fields
      call_example_terminal_def call_example_certificate_fields terminal_core_def terminal_effect_completed_def
      queue_example_decision_def queue_example_publication_def sample_credited_state record_credit_def empty_message_state_def Let_def)
  show ?thesis
    by (simp add: enqueue_secondary_def queue_example_world_def initial_settlement_world_def primary queue_example_job_def
      settlement_key_def queue_example_publication_def queue_example_decision_def Let_def)
qed

definition queue_example_in_flight where
  "queue_example_in_flight = dispatch_secondary ((0,17),0)
    (enqueue_secondary (0,17) (queue_example_world call_example_ready))"

lemma one_dispatch_uses_the_recorded_key_and_commitment:
  "settlement_jobs queue_example_in_flight ((0,17),0) = Some
     (queue_example_job\<lparr>secondary_attempts := 1, secondary_state := Secondary_In_Flight\<rparr>)"
  by (simp add: queue_example_in_flight_def dispatch_secondary_def update_secondary_job_def
      checked_primary_commitment_opens_one_secondary_job queue_example_job_def)

definition queue_example_ack where
  "queue_example_ack = \<lparr>ack_settlement_key = ((0,17),0), ack_publication = queue_example_publication, ack_target = 99\<rparr>"

definition queue_example_wrong_ack where
  "queue_example_wrong_ack = queue_example_ack\<lparr>ack_publication := queue_example_publication\<lparr>
    publication_decision := queue_example_decision\<lparr>origin_commit_position := 1\<rparr>\<rparr>\<rparr>"

lemma wrong_commitment_with_the_right_key_is_rejected:
  "acknowledge_secondary (\<lambda>_. True) queue_example_wrong_ack queue_example_in_flight = queue_example_in_flight"
  by (simp add: acknowledge_secondary_def exact_secondary_ack_def queue_example_wrong_ack_def queue_example_ack_def
      queue_example_publication_def queue_example_decision_def one_dispatch_uses_the_recorded_key_and_commitment
      queue_example_job_def Let_def)

lemma matching_ack_after_a_retry_completes_without_changing_primary:
  "let retry = dispatch_secondary ((0,17),0) (fail_secondary ((0,17),0) queue_example_in_flight);
       final = acknowledge_secondary (\<lambda>_. True) queue_example_ack retry
   in settlement_jobs final ((0,17),0) = Some
     (queue_example_job\<lparr>secondary_attempts := 2, secondary_state := Secondary_Completed\<rparr>) \<and>
     settlement_primary final = settlement_primary queue_example_in_flight"
  by (simp add: Let_def acknowledge_secondary_def exact_secondary_ack_def queue_example_ack_def
      settlement_key_def queue_example_job_def queue_example_publication_def queue_example_decision_def
      dispatch_secondary_def fail_secondary_def update_secondary_job_def one_dispatch_uses_the_recorded_key_and_commitment)

definition acknowledge_without_publication_check where
  "acknowledge_without_publication_check verified ack s =
    (let key = ack_settlement_key ack in case settlement_jobs s key of None \<Rightarrow> s
     | Some job \<Rightarrow> if verified ack \<and> ack_settlement_key ack = settlement_key (secondary_publication job)
        \<and> ack_target ack = secondary_target job \<and> secondary_attempts job > 0
        then update_secondary_job key (job\<lparr>secondary_state := Secondary_Completed\<rparr>) s else s)"

lemma removing_publication_equality_accepts_the_wrong_commitment:
  "settlement_jobs (acknowledge_without_publication_check (\<lambda>_. True) queue_example_wrong_ack queue_example_in_flight)
    ((0,17),0) = Some (queue_example_job\<lparr>secondary_attempts := 1, secondary_state := Secondary_Completed\<rparr>)"
  by (simp add: acknowledge_without_publication_check_def queue_example_wrong_ack_def queue_example_ack_def
      settlement_key_def queue_example_job_def queue_example_publication_def queue_example_decision_def
      one_dispatch_uses_the_recorded_key_and_commitment update_secondary_job_def Let_def)

end
