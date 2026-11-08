theory Reference_Parallel_Consumption
  imports Reference_Authority_Trace "OIP_Product.Parallel_Exchange"
begin

context source_attestation
begin

lemma a_nonserial_product_step_changes_only_the_queue_projection:
  assumes nonserial: "classify_service_action action (service_settlement (reopen_retained_product connection retained)) \<noteq> Service_Serial"
  shows "\<exists>jobs. fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection action retained) = retained\<lparr>retained_secondary := jobs\<rparr>"
proof -
  let ?live = "reopen_retained_product connection retained"
  let ?run = "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack connection"
  show ?thesis
  proof (cases "classify_service_action action (service_settlement ?live)")
    case Service_Observation
    have read_only: "fst (schedule_service_step directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action ?live) = ?live"
      by (rule scheduled_observations_read_but_do_not_write[OF Service_Observation])
    have "fst (?run action retained) = retained"
      by (simp add: schedule_at_retained_state_def Let_def read_only product_round_trip_preserves_the_durable_projection)
    then show ?thesis by (intro exI[of _ "retained_secondary retained"]) simp
  next
    case (Service_Slot resolved)
    let ?result = "step_settlement_slot verified_ack resolved (retained_secondary retained)"
    have "?run action retained =
        (retained\<lparr>retained_secondary := fst ?result\<rparr>, Scheduled_Settlement (snd ?result))"
      by (rule classified_settlement_action_updates_only_its_real_slot[OF Service_Slot, unfolded Let_def])
    then show ?thesis by (intro exI[of _ "fst ?result"]) simp
  next
    case Service_Serial
    then show ?thesis using nonserial by simp
  qed
qed

lemma a_nonserial_reference_step_keeps_the_live_grants:
  assumes coherent: "reference_grants_fit registered (reference_product before) (reference_inputs before)"
    and nonserial: "classify_service_action action
      (service_settlement (reopen_retained_product connection (reference_product before))) \<noteq> Service_Serial"
  shows "let selected = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
          legal_grant order_verified spend_grant spend_verified read_permitted
          (reference_permitted_at (reference_inputs before)) verified maintainers registered verified_ack
          connection action (reference_product before)
    in service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
       legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
       authenticated connection action supplied before =
         (before\<lparr>reference_product := fst selected\<rparr>, Some (snd selected))"
proof -
  let ?selected = "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
          legal_grant order_verified spend_grant spend_verified read_permitted
          (reference_permitted_at (reference_inputs before)) verified maintainers registered verified_ack
          connection action (reference_product before)"
  obtain jobs where only_queue: "fst ?selected = (reference_product before)\<lparr>retained_secondary := jobs\<rparr>"
    using a_nonserial_product_step_changes_only_the_queue_projection[OF nonserial] by blast
  have same_epoch: "reference_records_epoch (fst ?selected) = reference_records_epoch (reference_product before)"
    by (simp add: only_queue reference_records_epoch_def)
  show ?thesis using coherent same_epoch
    by (cases before) (simp add: service_at_reference_snapshot_def select_reference_grants_def Let_def)
qed

theorem compatible_actions_exchange_in_the_actual_reference_service:
  assumes coherent: "reference_grants_fit registered (reference_product before) (reference_inputs before)"
    and compatible: "compatible_service_actions first second
        (service_settlement (reopen_retained_product connection (reference_product before)))"
  shows "let step = (\<lambda>action current.
          service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
            legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
            authenticated connection action None current)
    in service_ordered_pair step first second before = service_exchanged_pair step first second before"
proof -
  let ?retained = "reference_product before"
  let ?initial = "service_settlement (reopen_retained_product connection ?retained)"
  let ?class = "\<lambda>action. classify_service_action action ?initial"
  let ?actual = "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted
      (reference_permitted_at (reference_inputs before)) verified maintainers registered verified_ack connection"
  let ?ref = "\<lambda>action current. service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
      authenticated connection action None current"
  have supported: "?class first \<noteq> Service_Serial" "?class second \<noteq> Service_Serial"
    using compatible_actions_have_no_shared_writer[OF compatible] .
  have first_step: "?ref action before =
      (before\<lparr>reference_product := fst (?actual action ?retained)\<rparr>, Some (snd (?actual action ?retained)))"
    if "?class action \<noteq> Service_Serial" for action
    using a_nonserial_reference_step_keeps_the_live_grants[OF coherent that]
    by (simp add: Let_def)
  have next_step: "?ref b (before\<lparr>reference_product := fst (?actual a ?retained)\<rparr>) =
      (before\<lparr>reference_product := fst (?actual b (fst (?actual a ?retained)))\<rparr>,
        Some (snd (?actual b (fst (?actual a ?retained)))))"
    if a: "?class a \<noteq> Service_Serial" and b: "?class b \<noteq> Service_Serial" for a b
  proof -
    let ?after = "before\<lparr>reference_product := fst (?actual a ?retained)\<rparr>"
    obtain jobs where queue: "fst (?actual a ?retained) = ?retained\<lparr>retained_secondary := jobs\<rparr>"
      using a_nonserial_product_step_changes_only_the_queue_projection[OF a] by blast
    have live: "reference_grants_fit registered (reference_product ?after) (reference_inputs ?after)"
      using coherent by (simp add: queue reference_grants_fit_def reference_records_epoch_def)
    have safe: "classify_service_action b
        (service_settlement (reopen_retained_product connection (reference_product ?after))) \<noteq> Service_Serial"
      using b by (simp add: queue reopening_after_a_queue_write_keeps_the_exact_primary_view
          queue_replacement_does_not_change_service_class)
    show ?thesis using a_nonserial_reference_step_keeps_the_live_grants[OF live safe]
      by (simp add: Let_def)
  qed
  let ?lift = "\<lambda>(result, left, right).
    (before\<lparr>reference_product := result\<rparr>, Some left, Some right)"
  have in_order: "service_ordered_pair ?ref first second before =
      ?lift (service_ordered_pair ?actual first second ?retained)"
    by (simp add: service_ordered_pair_def first_step[OF supported(1)] next_step[OF supported(1,2)] Let_def)
  have exchanged: "service_exchanged_pair ?ref first second before =
      ?lift (service_exchanged_pair ?actual first second ?retained)"
    by (simp add: service_exchanged_pair_def first_step[OF supported(2)] next_step[OF supported(2,1)] Let_def)
  have underlying: "service_ordered_pair ?actual first second ?retained =
      service_exchanged_pair ?actual first second ?retained"
    by (rule compatible_actual_product_actions_exchange[OF compatible])
  show ?thesis by (simp add: in_order exchanged underlying Let_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.a_nonserial_product_step_changes_only_the_queue_projection
      source_attestation.a_nonserial_reference_step_keeps_the_live_grants
      source_attestation.compatible_actions_exchange_in_the_actual_reference_service})
  then () else error "Unexpected oracle in reference service scheduling"
\<close>

end
