theory Parallel_Exchange
  imports Parallel_Step_Frame
begin

definition service_ordered_pair where
  "service_ordered_pair execute first second s =
    (let one = execute first s; two = execute second (fst one)
     in (fst two, snd one, snd two))"

definition service_exchanged_pair where
  "service_exchanged_pair execute first second s =
    (let two = execute second s; one = execute first (fst two)
     in (fst one, snd one, snd two))"

context source_attestation
begin

theorem compatible_actual_product_actions_exchange:
  assumes independent: "compatible_service_actions first second
    (service_settlement (reopen_retained_product connection retained))"
  shows "service_ordered_pair
     (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack connection)
      first second retained =
    service_exchanged_pair
     (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack connection)
      first second retained"
proof -
  let ?s = "reopen_retained_product connection retained"
  let ?class = "\<lambda>action. classify_service_action action (service_settlement ?s)"
  let ?step = "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack connection"
  let ?local = "step_settlement_slot verified_ack"
  let ?update = "\<lambda>jobs. retained\<lparr>retained_secondary := jobs\<rparr>"
  have supported: "?class first \<noteq> Service_Serial" "?class second \<noteq> Service_Serial"
    using compatible_actions_have_no_shared_writer[OF independent] .
  have scope: "classify_service_action action (service_settlement (reopen_retained_product connection (?update jobs))) =
      ?class action" for action jobs
    by (simp add: reopening_after_a_queue_write_keeps_the_exact_primary_view queue_replacement_does_not_change_service_class)
  have observe: "fst (?step action retained) = retained" if "?class action = Service_Observation" for action
    unfolding schedule_at_retained_state_def Let_def
    by (simp add: scheduled_observations_read_but_do_not_write[OF that] product_round_trip_preserves_the_durable_projection)
  have observe_after: "?step action (?update jobs) = (?update jobs, snd (?step action retained))"
    if "?class action = Service_Observation" for action jobs
  proof -
    have exact: "classify_service_action action (service_settlement (reopen_retained_product connection (?update jobs))) = Service_Observation"
      using that by (simp add: scope)
    have state: "fst (?step action (?update jobs)) = ?update jobs"
      unfolding schedule_at_retained_state_def Let_def
      by (simp add: scheduled_observations_read_but_do_not_write[OF exact] product_round_trip_preserves_the_durable_projection)
    have reply: "snd (?step action (?update jobs)) = snd (?step action retained)"
      unfolding schedule_at_retained_state_def Let_def
      by (simp add: reopening_after_a_queue_write_keeps_the_exact_primary_view
          scheduled_observation_reply_is_independent_of_all_queue_writes[OF that])
    show ?thesis using state reply by (cases "?step action (?update jobs)") simp
  qed
  have slot: "?step action retained =
      (?update (fst (?local resolved (retained_secondary retained))), Scheduled_Settlement (snd (?local resolved (retained_secondary retained))))"
    if "?class action = Service_Slot resolved" for action resolved
    using classified_settlement_action_updates_only_its_real_slot[OF that]
    by (simp only: Let_def)
  have slot_after: "?step action (?update jobs) =
      (?update (fst (?local resolved jobs)), Scheduled_Settlement (snd (?local resolved jobs)))"
    if "?class action = Service_Slot resolved" for action resolved jobs
  proof -
    have exact: "classify_service_action action (service_settlement (reopen_retained_product connection (?update jobs))) = Service_Slot resolved"
      using that by (simp add: scope)
    show ?thesis using classified_settlement_action_updates_only_its_real_slot[OF exact] by (simp add: Let_def)
  qed
  have local_exchange: "?class first = Service_Slot x \<Longrightarrow> ?class second = Service_Slot y \<Longrightarrow>
      service_ordered_pair ?step first second retained = service_exchanged_pair ?step first second retained" for x y
  proof -
    assume x: "?class first = Service_Slot x" and y: "?class second = Service_Slot y"
    have distinct: "resolved_slot x \<noteq> resolved_slot y"
      by (rule compatible_settlement_writes_use_distinct_exact_slots[OF independent x y])
    show ?thesis using different_actual_settlement_slots_exchange[OF distinct, of verified_ack "retained_secondary retained"]
      by (simp add: service_ordered_pair_def service_exchanged_pair_def Let_def slot[OF x] slot[OF y]
          slot_after[OF x] slot_after[OF y])
  qed
  show ?thesis
  proof (cases "?class first")
    case Service_Observation
    note a = this
    show ?thesis using a supported(2)
      by (cases "?class second"; simp add: service_ordered_pair_def service_exchanged_pair_def Let_def observe observe_after slot)
  next
    case (Service_Slot x)
    note a = this
    show ?thesis
    proof (cases "?class second")
      case Service_Observation
      then show ?thesis using a
        by (simp add: service_ordered_pair_def service_exchanged_pair_def Let_def observe observe_after slot)
    next
      case (Service_Slot y)
      show ?thesis by (rule local_exchange[OF a Service_Slot])
    next
      case Service_Serial
      then show ?thesis using supported(2) by simp
    qed
  next
    case Service_Serial
    then show ?thesis using supported(1) by simp
  qed
qed

end

end
